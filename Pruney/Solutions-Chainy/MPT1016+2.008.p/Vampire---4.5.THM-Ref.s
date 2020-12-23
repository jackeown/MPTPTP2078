%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 297 expanded)
%              Number of leaves         :   29 (  96 expanded)
%              Depth                    :   13
%              Number of atoms          :  372 (1217 expanded)
%              Number of equality atoms :   57 ( 245 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f912,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f108,f118,f132,f148,f160,f167,f186,f425,f456,f564,f567,f577,f587,f627,f632,f656,f785,f911])).

fof(f911,plain,
    ( spl7_15
    | spl7_7
    | ~ spl7_2
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f906,f453,f66,f157,f418])).

fof(f418,plain,
    ( spl7_15
  <=> sP6(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f157,plain,
    ( spl7_7
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f66,plain,
    ( spl7_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f453,plain,
    ( spl7_18
  <=> sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f906,plain,
    ( sK2 = sK3
    | sP6(sK1,sK0)
    | ~ spl7_2
    | ~ spl7_18 ),
    inference(superposition,[],[f126,f455])).

fof(f455,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f453])).

fof(f126,plain,
    ( ! [X2] :
        ( sK2 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,sK2))
        | sP6(X2,sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f68,f51])).

fof(f51,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X0)
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | sP6(X3,X0) ) ),
    inference(cnf_transformation,[],[f51_D])).

fof(f51_D,plain,(
    ! [X0,X3] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X0)
          | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 )
    <=> ~ sP6(X3,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f68,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f785,plain,
    ( ~ spl7_2
    | ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f781])).

fof(f781,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_16 ),
    inference(resolution,[],[f678,f34])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f678,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))
    | ~ spl7_2
    | ~ spl7_16 ),
    inference(backward_demodulation,[],[f127,f424])).

fof(f424,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f422])).

fof(f422,plain,
    ( spl7_16
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f127,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK2))
    | ~ spl7_2 ),
    inference(resolution,[],[f124,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f124,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ spl7_2 ),
    inference(resolution,[],[f68,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f656,plain,
    ( ~ spl7_5
    | spl7_15
    | ~ spl7_17 ),
    inference(avatar_contradiction_clause,[],[f654])).

fof(f654,plain,
    ( $false
    | ~ spl7_5
    | spl7_15
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f420,f653])).

fof(f653,plain,
    ( sP6(sK1,sK0)
    | ~ spl7_5
    | ~ spl7_17 ),
    inference(resolution,[],[f451,f131])).

fof(f131,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl7_5
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f451,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK3,X4)
        | sP6(sK1,X4) )
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f450])).

fof(f450,plain,
    ( spl7_17
  <=> ! [X4] :
        ( ~ r2_hidden(sK3,X4)
        | sP6(sK1,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f420,plain,
    ( ~ sP6(sK1,sK0)
    | spl7_15 ),
    inference(avatar_component_clause,[],[f418])).

fof(f632,plain,
    ( ~ spl7_3
    | spl7_25 ),
    inference(avatar_contradiction_clause,[],[f628])).

fof(f628,plain,
    ( $false
    | ~ spl7_3
    | spl7_25 ),
    inference(subsumption_resolution,[],[f203,f626])).

fof(f626,plain,
    ( ~ r2_hidden(sK4(sK1),sK0)
    | spl7_25 ),
    inference(avatar_component_clause,[],[f624])).

fof(f624,plain,
    ( spl7_25
  <=> r2_hidden(sK4(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f203,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | ~ spl7_3 ),
    inference(resolution,[],[f101,f107])).

fof(f107,plain,
    ( r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl7_3
  <=> r2_hidden(sK4(sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f101,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK1))
      | r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f94,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

% (9619)Refutation not found, incomplete strategy% (9619)------------------------------
% (9619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9619)Termination reason: Refutation not found, incomplete strategy

% (9619)Memory used [KB]: 10618
% (9619)Time elapsed: 0.072 s
% (9619)------------------------------
% (9619)------------------------------
fof(f94,plain,(
    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f92,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f92,plain,(
    r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(global_subsumption,[],[f76,f91])).

fof(f91,plain,
    ( ~ v1_relat_1(sK1)
    | r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(resolution,[],[f75,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f75,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(resolution,[],[f33,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

fof(f76,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f33,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f627,plain,
    ( spl7_9
    | ~ spl7_25
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f604,f562,f624,f183])).

fof(f183,plain,
    ( spl7_9
  <=> sK4(sK1) = sK5(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f562,plain,
    ( spl7_22
  <=> ! [X0] :
        ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
        | ~ r2_hidden(X0,sK0)
        | sK5(sK1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f604,plain,
    ( ~ r2_hidden(sK4(sK1),sK0)
    | sK4(sK1) = sK5(sK1)
    | ~ spl7_22 ),
    inference(equality_resolution,[],[f563])).

fof(f563,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
        | ~ r2_hidden(X0,sK0)
        | sK5(sK1) = X0 )
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f562])).

fof(f587,plain,
    ( ~ spl7_6
    | spl7_21 ),
    inference(avatar_contradiction_clause,[],[f584])).

fof(f584,plain,
    ( $false
    | ~ spl7_6
    | spl7_21 ),
    inference(subsumption_resolution,[],[f204,f560])).

fof(f560,plain,
    ( ~ r2_hidden(sK5(sK1),sK0)
    | spl7_21 ),
    inference(avatar_component_clause,[],[f558])).

fof(f558,plain,
    ( spl7_21
  <=> r2_hidden(sK5(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f204,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | ~ spl7_6 ),
    inference(resolution,[],[f101,f147])).

fof(f147,plain,
    ( r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl7_6
  <=> r2_hidden(sK5(sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f577,plain,(
    spl7_20 ),
    inference(avatar_split_clause,[],[f76,f554])).

fof(f554,plain,
    ( spl7_20
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f567,plain,(
    spl7_19 ),
    inference(avatar_split_clause,[],[f31,f550])).

fof(f550,plain,
    ( spl7_19
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f31,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f564,plain,
    ( spl7_1
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_21
    | spl7_22
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f199,f116,f562,f558,f554,f550,f62])).

fof(f62,plain,
    ( spl7_1
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f116,plain,
    ( spl7_4
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X2,sK0)
        | X2 = X3
        | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3)
        | ~ r2_hidden(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f199,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
        | sK5(sK1) = X0
        | ~ r2_hidden(sK5(sK1),sK0)
        | ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(sK1)
        | v2_funct_1(sK1) )
    | ~ spl7_4 ),
    inference(superposition,[],[f117,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f117,plain,
    ( ! [X2,X3] :
        ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3)
        | X2 = X3
        | ~ r2_hidden(X2,sK0)
        | ~ r2_hidden(X3,sK0) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f116])).

fof(f456,plain,
    ( spl7_17
    | spl7_18
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f416,f164,f453,f450])).

fof(f164,plain,
    ( spl7_8
  <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

% (9614)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f416,plain,
    ( ! [X4] :
        ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
        | ~ r2_hidden(sK3,X4)
        | sP6(sK1,X4) )
    | ~ spl7_8 ),
    inference(superposition,[],[f51,f166])).

fof(f166,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f164])).

% (9631)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
fof(f425,plain,
    ( ~ spl7_15
    | spl7_16
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f60,f62,f422,f418])).

fof(f60,plain,
    ( ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ sP6(sK1,sK0) ),
    inference(global_subsumption,[],[f33,f31,f59])).

fof(f59,plain,
    ( ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ sP6(sK1,sK0) ),
    inference(resolution,[],[f32,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ sP6(X3,X0) ) ),
    inference(general_splitting,[],[f50,f51_D])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

fof(f32,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f186,plain,
    ( ~ spl7_9
    | spl7_1 ),
    inference(avatar_split_clause,[],[f90,f62,f183])).

fof(f90,plain,
    ( v2_funct_1(sK1)
    | sK4(sK1) != sK5(sK1) ),
    inference(global_subsumption,[],[f57,f76])).

fof(f57,plain,
    ( ~ v1_relat_1(sK1)
    | sK4(sK1) != sK5(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f31,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sK4(X0) != sK5(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f167,plain,
    ( ~ spl7_1
    | spl7_8 ),
    inference(avatar_split_clause,[],[f28,f164,f62])).

fof(f28,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f160,plain,
    ( ~ spl7_1
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f29,f157,f62])).

fof(f29,plain,
    ( sK2 != sK3
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f148,plain,
    ( spl7_6
    | spl7_1 ),
    inference(avatar_split_clause,[],[f88,f62,f145])).

fof(f88,plain,
    ( v2_funct_1(sK1)
    | r2_hidden(sK5(sK1),k1_relat_1(sK1)) ),
    inference(global_subsumption,[],[f55,f76])).

fof(f55,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f31,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK5(X0),k1_relat_1(X0))
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f132,plain,
    ( ~ spl7_1
    | spl7_5 ),
    inference(avatar_split_clause,[],[f27,f129,f62])).

fof(f27,plain,
    ( r2_hidden(sK3,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f118,plain,
    ( spl7_1
    | spl7_4 ),
    inference(avatar_split_clause,[],[f30,f116,f62])).

fof(f30,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X3,sK0)
      | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3)
      | X2 = X3
      | v2_funct_1(sK1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f108,plain,
    ( spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f87,f105,f62])).

fof(f87,plain,
    ( r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1) ),
    inference(global_subsumption,[],[f54,f76])).

fof(f54,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f31,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(X0),k1_relat_1(X0))
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f69,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f26,f66,f62])).

fof(f26,plain,
    ( r2_hidden(sK2,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:14:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (9625)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.46  % (9633)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.49  % (9618)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (9635)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.49  % (9627)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (9613)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (9615)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (9619)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (9634)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (9617)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (9633)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f912,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f69,f108,f118,f132,f148,f160,f167,f186,f425,f456,f564,f567,f577,f587,f627,f632,f656,f785,f911])).
% 0.21/0.50  fof(f911,plain,(
% 0.21/0.50    spl7_15 | spl7_7 | ~spl7_2 | ~spl7_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f906,f453,f66,f157,f418])).
% 0.21/0.50  fof(f418,plain,(
% 0.21/0.50    spl7_15 <=> sP6(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    spl7_7 <=> sK2 = sK3),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl7_2 <=> r2_hidden(sK2,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.50  fof(f453,plain,(
% 0.21/0.50    spl7_18 <=> sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.50  fof(f906,plain,(
% 0.21/0.50    sK2 = sK3 | sP6(sK1,sK0) | (~spl7_2 | ~spl7_18)),
% 0.21/0.50    inference(superposition,[],[f126,f455])).
% 0.21/0.50  fof(f455,plain,(
% 0.21/0.50    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~spl7_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f453])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    ( ! [X2] : (sK2 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,sK2)) | sP6(X2,sK0)) ) | ~spl7_2),
% 0.21/0.50    inference(resolution,[],[f68,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X2,X0,X3] : (~r2_hidden(X2,X0) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | sP6(X3,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f51_D])).
% 0.21/0.50  fof(f51_D,plain,(
% 0.21/0.50    ( ! [X0,X3] : (( ! [X2] : (~r2_hidden(X2,X0) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2) ) <=> ~sP6(X3,X0)) )),
% 0.21/0.50    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    r2_hidden(sK2,sK0) | ~spl7_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f66])).
% 0.21/0.50  fof(f785,plain,(
% 0.21/0.50    ~spl7_2 | ~spl7_16),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f781])).
% 0.21/0.50  fof(f781,plain,(
% 0.21/0.50    $false | (~spl7_2 | ~spl7_16)),
% 0.21/0.50    inference(resolution,[],[f678,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.50  fof(f678,plain,(
% 0.21/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) | (~spl7_2 | ~spl7_16)),
% 0.21/0.50    inference(backward_demodulation,[],[f127,f424])).
% 0.21/0.50  fof(f424,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | ~spl7_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f422])).
% 0.21/0.50  fof(f422,plain,(
% 0.21/0.50    spl7_16 <=> k1_xboole_0 = sK0),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    ~m1_subset_1(sK0,k1_zfmisc_1(sK2)) | ~spl7_2),
% 0.21/0.50    inference(resolution,[],[f124,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    ~r1_tarski(sK0,sK2) | ~spl7_2),
% 0.21/0.50    inference(resolution,[],[f68,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.50  fof(f656,plain,(
% 0.21/0.50    ~spl7_5 | spl7_15 | ~spl7_17),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f654])).
% 0.21/0.50  fof(f654,plain,(
% 0.21/0.50    $false | (~spl7_5 | spl7_15 | ~spl7_17)),
% 0.21/0.50    inference(subsumption_resolution,[],[f420,f653])).
% 0.21/0.50  fof(f653,plain,(
% 0.21/0.50    sP6(sK1,sK0) | (~spl7_5 | ~spl7_17)),
% 0.21/0.50    inference(resolution,[],[f451,f131])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    r2_hidden(sK3,sK0) | ~spl7_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f129])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    spl7_5 <=> r2_hidden(sK3,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.50  fof(f451,plain,(
% 0.21/0.50    ( ! [X4] : (~r2_hidden(sK3,X4) | sP6(sK1,X4)) ) | ~spl7_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f450])).
% 0.21/0.50  fof(f450,plain,(
% 0.21/0.50    spl7_17 <=> ! [X4] : (~r2_hidden(sK3,X4) | sP6(sK1,X4))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.21/0.50  fof(f420,plain,(
% 0.21/0.50    ~sP6(sK1,sK0) | spl7_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f418])).
% 0.21/0.50  fof(f632,plain,(
% 0.21/0.50    ~spl7_3 | spl7_25),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f628])).
% 0.21/0.50  fof(f628,plain,(
% 0.21/0.50    $false | (~spl7_3 | spl7_25)),
% 0.21/0.50    inference(subsumption_resolution,[],[f203,f626])).
% 0.21/0.50  fof(f626,plain,(
% 0.21/0.50    ~r2_hidden(sK4(sK1),sK0) | spl7_25),
% 0.21/0.50    inference(avatar_component_clause,[],[f624])).
% 0.21/0.50  fof(f624,plain,(
% 0.21/0.50    spl7_25 <=> r2_hidden(sK4(sK1),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    r2_hidden(sK4(sK1),sK0) | ~spl7_3),
% 0.21/0.50    inference(resolution,[],[f101,f107])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    r2_hidden(sK4(sK1),k1_relat_1(sK1)) | ~spl7_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f105])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    spl7_3 <=> r2_hidden(sK4(sK1),k1_relat_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | r2_hidden(X1,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f94,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.50  % (9619)Refutation not found, incomplete strategy% (9619)------------------------------
% 0.21/0.50  % (9619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (9619)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (9619)Memory used [KB]: 10618
% 0.21/0.50  % (9619)Time elapsed: 0.072 s
% 0.21/0.50  % (9619)------------------------------
% 0.21/0.50  % (9619)------------------------------
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))),
% 0.21/0.50    inference(resolution,[],[f92,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    r1_tarski(k1_relat_1(sK1),sK0)),
% 0.21/0.50    inference(global_subsumption,[],[f76,f91])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ~v1_relat_1(sK1) | r1_tarski(k1_relat_1(sK1),sK0)),
% 0.21/0.50    inference(resolution,[],[f75,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    v4_relat_1(sK1,sK0)),
% 0.21/0.50    inference(resolution,[],[f33,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.50    inference(flattening,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.21/0.50    inference(negated_conjecture,[],[f11])).
% 0.21/0.50  fof(f11,conjecture,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    v1_relat_1(sK1)),
% 0.21/0.50    inference(resolution,[],[f33,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f627,plain,(
% 0.21/0.50    spl7_9 | ~spl7_25 | ~spl7_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f604,f562,f624,f183])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    spl7_9 <=> sK4(sK1) = sK5(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.50  fof(f562,plain,(
% 0.21/0.50    spl7_22 <=> ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | ~r2_hidden(X0,sK0) | sK5(sK1) = X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.21/0.50  fof(f604,plain,(
% 0.21/0.50    ~r2_hidden(sK4(sK1),sK0) | sK4(sK1) = sK5(sK1) | ~spl7_22),
% 0.21/0.50    inference(equality_resolution,[],[f563])).
% 0.21/0.50  fof(f563,plain,(
% 0.21/0.50    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | ~r2_hidden(X0,sK0) | sK5(sK1) = X0) ) | ~spl7_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f562])).
% 0.21/0.50  fof(f587,plain,(
% 0.21/0.50    ~spl7_6 | spl7_21),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f584])).
% 0.21/0.50  fof(f584,plain,(
% 0.21/0.50    $false | (~spl7_6 | spl7_21)),
% 0.21/0.50    inference(subsumption_resolution,[],[f204,f560])).
% 0.21/0.50  fof(f560,plain,(
% 0.21/0.50    ~r2_hidden(sK5(sK1),sK0) | spl7_21),
% 0.21/0.50    inference(avatar_component_clause,[],[f558])).
% 0.21/0.50  fof(f558,plain,(
% 0.21/0.50    spl7_21 <=> r2_hidden(sK5(sK1),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.50  fof(f204,plain,(
% 0.21/0.50    r2_hidden(sK5(sK1),sK0) | ~spl7_6),
% 0.21/0.50    inference(resolution,[],[f101,f147])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    r2_hidden(sK5(sK1),k1_relat_1(sK1)) | ~spl7_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f145])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    spl7_6 <=> r2_hidden(sK5(sK1),k1_relat_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.50  fof(f577,plain,(
% 0.21/0.50    spl7_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f76,f554])).
% 0.21/0.50  fof(f554,plain,(
% 0.21/0.50    spl7_20 <=> v1_relat_1(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.21/0.50  fof(f567,plain,(
% 0.21/0.50    spl7_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f31,f550])).
% 0.21/0.50  fof(f550,plain,(
% 0.21/0.50    spl7_19 <=> v1_funct_1(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    v1_funct_1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f564,plain,(
% 0.21/0.50    spl7_1 | ~spl7_19 | ~spl7_20 | ~spl7_21 | spl7_22 | ~spl7_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f199,f116,f562,f558,f554,f550,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    spl7_1 <=> v2_funct_1(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    spl7_4 <=> ! [X3,X2] : (~r2_hidden(X2,sK0) | X2 = X3 | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | sK5(sK1) = X0 | ~r2_hidden(sK5(sK1),sK0) | ~r2_hidden(X0,sK0) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | v2_funct_1(sK1)) ) | ~spl7_4),
% 0.21/0.50    inference(superposition,[],[f117,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) | v2_funct_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    ( ! [X2,X3] : (k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3) | X2 = X3 | ~r2_hidden(X2,sK0) | ~r2_hidden(X3,sK0)) ) | ~spl7_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f116])).
% 0.21/0.50  fof(f456,plain,(
% 0.21/0.50    spl7_17 | spl7_18 | ~spl7_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f416,f164,f453,f450])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    spl7_8 <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.50  % (9614)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  fof(f416,plain,(
% 0.21/0.50    ( ! [X4] : (sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~r2_hidden(sK3,X4) | sP6(sK1,X4)) ) | ~spl7_8),
% 0.21/0.50    inference(superposition,[],[f51,f166])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~spl7_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f164])).
% 0.21/0.51  % (9631)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  fof(f425,plain,(
% 0.21/0.51    ~spl7_15 | spl7_16 | ~spl7_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f60,f62,f422,f418])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | ~sP6(sK1,sK0)),
% 0.21/0.51    inference(global_subsumption,[],[f33,f31,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | ~sP6(sK1,sK0)),
% 0.21/0.51    inference(resolution,[],[f32,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X3) | k1_xboole_0 = X1 | ~sP6(X3,X0)) )),
% 0.21/0.51    inference(general_splitting,[],[f50,f51_D])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f186,plain,(
% 0.21/0.51    ~spl7_9 | spl7_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f90,f62,f183])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    v2_funct_1(sK1) | sK4(sK1) != sK5(sK1)),
% 0.21/0.51    inference(global_subsumption,[],[f57,f76])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ~v1_relat_1(sK1) | sK4(sK1) != sK5(sK1) | v2_funct_1(sK1)),
% 0.21/0.51    inference(resolution,[],[f31,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sK4(X0) != sK5(X0) | v2_funct_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    ~spl7_1 | spl7_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f28,f164,f62])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~v2_funct_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    ~spl7_1 | ~spl7_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f29,f157,f62])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    sK2 != sK3 | ~v2_funct_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    spl7_6 | spl7_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f88,f62,f145])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    v2_funct_1(sK1) | r2_hidden(sK5(sK1),k1_relat_1(sK1))),
% 0.21/0.51    inference(global_subsumption,[],[f55,f76])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ~v1_relat_1(sK1) | r2_hidden(sK5(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1)),
% 0.21/0.51    inference(resolution,[],[f31,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK5(X0),k1_relat_1(X0)) | v2_funct_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    ~spl7_1 | spl7_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f27,f129,f62])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    r2_hidden(sK3,sK0) | ~v2_funct_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    spl7_1 | spl7_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f30,f116,f62])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~r2_hidden(X2,sK0) | ~r2_hidden(X3,sK0) | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3) | X2 = X3 | v2_funct_1(sK1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    spl7_1 | spl7_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f87,f105,f62])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    r2_hidden(sK4(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1)),
% 0.21/0.51    inference(global_subsumption,[],[f54,f76])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ~v1_relat_1(sK1) | r2_hidden(sK4(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1)),
% 0.21/0.51    inference(resolution,[],[f31,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK4(X0),k1_relat_1(X0)) | v2_funct_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ~spl7_1 | spl7_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f26,f66,f62])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    r2_hidden(sK2,sK0) | ~v2_funct_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (9633)------------------------------
% 0.21/0.51  % (9633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9633)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (9633)Memory used [KB]: 11001
% 0.21/0.51  % (9633)Time elapsed: 0.092 s
% 0.21/0.51  % (9633)------------------------------
% 0.21/0.51  % (9633)------------------------------
% 0.21/0.51  % (9621)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (9612)Success in time 0.156 s
%------------------------------------------------------------------------------
