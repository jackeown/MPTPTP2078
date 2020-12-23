%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 144 expanded)
%              Number of leaves         :   26 (  60 expanded)
%              Depth                    :    6
%              Number of atoms          :  267 ( 445 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f238,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f47,f51,f59,f63,f67,f71,f83,f95,f100,f106,f110,f114,f121,f153,f162,f188,f224,f237])).

fof(f237,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_36 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f232,f46])).

fof(f46,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl5_2
  <=> r1_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f232,plain,
    ( ~ r1_xboole_0(sK3,sK2)
    | ~ spl5_1
    | ~ spl5_36 ),
    inference(resolution,[],[f223,f42])).

fof(f42,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl5_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f223,plain,
    ( ! [X2] :
        ( ~ r1_tarski(sK1,X2)
        | ~ r1_xboole_0(sK3,X2) )
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl5_36
  <=> ! [X2] :
        ( ~ r1_tarski(sK1,X2)
        | ~ r1_xboole_0(sK3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f224,plain,
    ( spl5_36
    | ~ spl5_8
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f191,f186,f69,f222])).

fof(f69,plain,
    ( spl5_8
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f186,plain,
    ( spl5_30
  <=> ! [X0] :
        ( ~ r1_xboole_0(X0,sK3)
        | ~ r1_tarski(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f191,plain,
    ( ! [X2] :
        ( ~ r1_tarski(sK1,X2)
        | ~ r1_xboole_0(sK3,X2) )
    | ~ spl5_8
    | ~ spl5_30 ),
    inference(resolution,[],[f187,f70])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f187,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK3)
        | ~ r1_tarski(sK1,X0) )
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f186])).

fof(f188,plain,
    ( spl5_30
    | ~ spl5_15
    | spl5_25 ),
    inference(avatar_split_clause,[],[f167,f151,f98,f186])).

fof(f98,plain,
    ( spl5_15
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f151,plain,
    ( spl5_25
  <=> r1_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f167,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK3)
        | ~ r1_tarski(sK1,X0) )
    | ~ spl5_15
    | spl5_25 ),
    inference(resolution,[],[f152,f99])).

fof(f99,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f98])).

fof(f152,plain,
    ( ~ r1_xboole_0(sK1,sK3)
    | spl5_25 ),
    inference(avatar_component_clause,[],[f151])).

fof(f162,plain,
    ( ~ spl5_5
    | ~ spl5_17
    | spl5_24 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_17
    | spl5_24 ),
    inference(subsumption_resolution,[],[f159,f58])).

fof(f58,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl5_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f159,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_17
    | spl5_24 ),
    inference(resolution,[],[f149,f109])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl5_17
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f149,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl5_24 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl5_24
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f153,plain,
    ( ~ spl5_24
    | ~ spl5_25
    | ~ spl5_18
    | spl5_19 ),
    inference(avatar_split_clause,[],[f126,f119,f112,f151,f148])).

fof(f112,plain,
    ( spl5_18
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_xboole_0(X0,X2)
        | r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f119,plain,
    ( spl5_19
  <=> r1_tarski(sK1,k4_xboole_0(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f126,plain,
    ( ~ r1_xboole_0(sK1,sK3)
    | ~ r1_tarski(sK1,sK0)
    | ~ spl5_18
    | spl5_19 ),
    inference(resolution,[],[f120,f113])).

fof(f113,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f112])).

fof(f120,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK0,sK3))
    | spl5_19 ),
    inference(avatar_component_clause,[],[f119])).

fof(f121,plain,
    ( ~ spl5_19
    | ~ spl5_3
    | spl5_6
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f117,f104,f61,f49,f119])).

fof(f49,plain,
    ( spl5_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f61,plain,
    ( spl5_6
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f104,plain,
    ( spl5_16
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f117,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK0,sK3))
    | ~ spl5_3
    | spl5_6
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f116,f50])).

fof(f50,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f116,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | spl5_6
    | ~ spl5_16 ),
    inference(superposition,[],[f62,f105])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f104])).

fof(f62,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK3))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f114,plain,(
    spl5_18 ),
    inference(avatar_split_clause,[],[f37,f112])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f110,plain,
    ( spl5_17
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f102,f93,f81,f65,f108])).

fof(f65,plain,
    ( spl5_7
  <=> ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f81,plain,
    ( spl5_11
  <=> ! [X0,X2] :
        ( r1_tarski(X2,X0)
        | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f93,plain,
    ( spl5_14
  <=> ! [X1,X0] :
        ( v1_xboole_0(X0)
        | r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | r1_tarski(X1,X0) )
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f101,f66])).

fof(f66,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f65])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | r1_tarski(X1,X0) )
    | ~ spl5_11
    | ~ spl5_14 ),
    inference(resolution,[],[f94,f82])).

fof(f82,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
        | r1_tarski(X2,X0) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f81])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X1,X0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f93])).

fof(f106,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f31,f104])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f100,plain,(
    spl5_15 ),
    inference(avatar_split_clause,[],[f36,f98])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f95,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f29,f93])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f83,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f38,f81])).

fof(f38,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f71,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f30,f69])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f67,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f25,f65])).

fof(f25,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f63,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f22,f61])).

fof(f22,plain,(
    ~ r1_tarski(sK1,k3_subset_1(sK0,sK3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( ( r1_xboole_0(X3,X2)
                    & r1_tarski(X1,X2) )
                 => r1_tarski(X1,k3_subset_1(X0,X3)) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X0))
             => ( ( r1_xboole_0(X3,X2)
                  & r1_tarski(X1,X2) )
               => r1_tarski(X1,k3_subset_1(X0,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_subset_1)).

fof(f59,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f24,f57])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f51,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f19,f49])).

fof(f19,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f47,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f21,f45])).

fof(f21,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f20,f41])).

fof(f20,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:15:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (29982)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (29974)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (29990)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (29982)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (29981)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f238,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f43,f47,f51,f59,f63,f67,f71,f83,f95,f100,f106,f110,f114,f121,f153,f162,f188,f224,f237])).
% 0.21/0.49  fof(f237,plain,(
% 0.21/0.49    ~spl5_1 | ~spl5_2 | ~spl5_36),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f236])).
% 0.21/0.49  fof(f236,plain,(
% 0.21/0.49    $false | (~spl5_1 | ~spl5_2 | ~spl5_36)),
% 0.21/0.49    inference(subsumption_resolution,[],[f232,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    r1_xboole_0(sK3,sK2) | ~spl5_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    spl5_2 <=> r1_xboole_0(sK3,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    ~r1_xboole_0(sK3,sK2) | (~spl5_1 | ~spl5_36)),
% 0.21/0.49    inference(resolution,[],[f223,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    r1_tarski(sK1,sK2) | ~spl5_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    spl5_1 <=> r1_tarski(sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    ( ! [X2] : (~r1_tarski(sK1,X2) | ~r1_xboole_0(sK3,X2)) ) | ~spl5_36),
% 0.21/0.49    inference(avatar_component_clause,[],[f222])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    spl5_36 <=> ! [X2] : (~r1_tarski(sK1,X2) | ~r1_xboole_0(sK3,X2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    spl5_36 | ~spl5_8 | ~spl5_30),
% 0.21/0.49    inference(avatar_split_clause,[],[f191,f186,f69,f222])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    spl5_8 <=> ! [X1,X0] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.49  fof(f186,plain,(
% 0.21/0.49    spl5_30 <=> ! [X0] : (~r1_xboole_0(X0,sK3) | ~r1_tarski(sK1,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    ( ! [X2] : (~r1_tarski(sK1,X2) | ~r1_xboole_0(sK3,X2)) ) | (~spl5_8 | ~spl5_30)),
% 0.21/0.49    inference(resolution,[],[f187,f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) ) | ~spl5_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f69])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_xboole_0(X0,sK3) | ~r1_tarski(sK1,X0)) ) | ~spl5_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f186])).
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    spl5_30 | ~spl5_15 | spl5_25),
% 0.21/0.49    inference(avatar_split_clause,[],[f167,f151,f98,f186])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    spl5_15 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    spl5_25 <=> r1_xboole_0(sK1,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_xboole_0(X0,sK3) | ~r1_tarski(sK1,X0)) ) | (~spl5_15 | spl5_25)),
% 0.21/0.49    inference(resolution,[],[f152,f99])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) ) | ~spl5_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f98])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    ~r1_xboole_0(sK1,sK3) | spl5_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f151])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    ~spl5_5 | ~spl5_17 | spl5_24),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f161])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    $false | (~spl5_5 | ~spl5_17 | spl5_24)),
% 0.21/0.49    inference(subsumption_resolution,[],[f159,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl5_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    spl5_5 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (~spl5_17 | spl5_24)),
% 0.21/0.49    inference(resolution,[],[f149,f109])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl5_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f108])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    spl5_17 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    ~r1_tarski(sK1,sK0) | spl5_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f148])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    spl5_24 <=> r1_tarski(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    ~spl5_24 | ~spl5_25 | ~spl5_18 | spl5_19),
% 0.21/0.49    inference(avatar_split_clause,[],[f126,f119,f112,f151,f148])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    spl5_18 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    spl5_19 <=> r1_tarski(sK1,k4_xboole_0(sK0,sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    ~r1_xboole_0(sK1,sK3) | ~r1_tarski(sK1,sK0) | (~spl5_18 | spl5_19)),
% 0.21/0.49    inference(resolution,[],[f120,f113])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl5_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f112])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    ~r1_tarski(sK1,k4_xboole_0(sK0,sK3)) | spl5_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f119])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    ~spl5_19 | ~spl5_3 | spl5_6 | ~spl5_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f117,f104,f61,f49,f119])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    spl5_3 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    spl5_6 <=> r1_tarski(sK1,k3_subset_1(sK0,sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    spl5_16 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    ~r1_tarski(sK1,k4_xboole_0(sK0,sK3)) | (~spl5_3 | spl5_6 | ~spl5_16)),
% 0.21/0.49    inference(subsumption_resolution,[],[f116,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl5_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f49])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    ~r1_tarski(sK1,k4_xboole_0(sK0,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | (spl5_6 | ~spl5_16)),
% 0.21/0.49    inference(superposition,[],[f62,f105])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl5_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f104])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ~r1_tarski(sK1,k3_subset_1(sK0,sK3)) | spl5_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f61])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    spl5_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f37,f112])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    spl5_17 | ~spl5_7 | ~spl5_11 | ~spl5_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f102,f93,f81,f65,f108])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    spl5_7 <=> ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    spl5_11 <=> ! [X0,X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    spl5_14 <=> ! [X1,X0] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0)) ) | (~spl5_7 | ~spl5_11 | ~spl5_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f101,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) ) | ~spl5_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f65])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_xboole_0(k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X0)) ) | (~spl5_11 | ~spl5_14)),
% 0.21/0.49    inference(resolution,[],[f94,f82])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) ) | ~spl5_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f81])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,X0)) ) | ~spl5_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f93])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    spl5_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f31,f104])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    spl5_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f36,f98])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    spl5_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f29,f93])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    spl5_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f38,f81])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl5_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f30,f69])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl5_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f25,f65])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ~spl5_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f22,f61])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ~r1_tarski(sK1,k3_subset_1(sK0,sK3))),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(X1,k3_subset_1(X0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(X1,k3_subset_1(X0,X3)) & (r1_xboole_0(X3,X2) & r1_tarski(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ((r1_xboole_0(X3,X2) & r1_tarski(X1,X2)) => r1_tarski(X1,k3_subset_1(X0,X3))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f8])).
% 0.21/0.49  fof(f8,conjecture,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ((r1_xboole_0(X3,X2) & r1_tarski(X1,X2)) => r1_tarski(X1,k3_subset_1(X0,X3))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_subset_1)).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl5_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f24,f57])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    spl5_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f19,f49])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f21,f45])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    r1_xboole_0(sK3,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    spl5_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f20,f41])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    r1_tarski(sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (29982)------------------------------
% 0.21/0.49  % (29982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (29982)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (29982)Memory used [KB]: 10746
% 0.21/0.49  % (29982)Time elapsed: 0.066 s
% 0.21/0.49  % (29982)------------------------------
% 0.21/0.49  % (29982)------------------------------
% 0.21/0.49  % (29972)Success in time 0.129 s
%------------------------------------------------------------------------------
