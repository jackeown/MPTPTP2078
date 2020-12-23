%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t62_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:48 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   62 (  94 expanded)
%              Number of leaves         :   13 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  188 ( 300 expanded)
%              Number of equality atoms :   65 ( 101 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f226,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f88,f92,f96,f112,f116,f124,f225])).

fof(f225,plain,
    ( ~ spl4_0
    | spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f223,f123])).

fof(f123,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl4_13
  <=> k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f223,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | ~ spl4_0
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,
    ( ! [X0] :
        ( k1_tarski(sK0) != k1_tarski(X0)
        | k1_tarski(k1_funct_1(sK2,X0)) = k2_relat_1(sK2) )
    | ~ spl4_0
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f119,f107])).

fof(f107,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK2)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f101,f106])).

fof(f106,plain,
    ( k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f105,f91])).

fof(f91,plain,
    ( v1_funct_2(sK2,k1_tarski(sK0),sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl4_4
  <=> v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f105,plain,
    ( k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2)
    | ~ v1_funct_2(sK2,k1_tarski(sK0),sK1)
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f100,f87])).

fof(f87,plain,
    ( k1_xboole_0 != sK1
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_3
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f100,plain,
    ( k1_xboole_0 = sK1
    | k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2)
    | ~ v1_funct_2(sK2,k1_tarski(sK0),sK1)
    | ~ spl4_6 ),
    inference(resolution,[],[f95,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t62_funct_2.p',d1_funct_2)).

fof(f95,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f101,plain,
    ( k1_relset_1(k1_tarski(sK0),sK1,sK2) = k1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f95,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t62_funct_2.p',redefinition_k1_relset_1)).

fof(f119,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k1_relat_1(sK2)
        | k1_tarski(k1_funct_1(sK2,X0)) = k2_relat_1(sK2) )
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f118,f83])).

fof(f83,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl4_0
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | k1_tarski(X0) != k1_relat_1(sK2)
        | k1_tarski(k1_funct_1(sK2,X0)) = k2_relat_1(sK2) )
    | ~ spl4_8 ),
    inference(resolution,[],[f111,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t62_funct_2.p',t14_funct_1)).

fof(f111,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl4_8
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f124,plain,
    ( ~ spl4_13
    | ~ spl4_6
    | spl4_11 ),
    inference(avatar_split_clause,[],[f117,f114,f94,f122])).

fof(f114,plain,
    ( spl4_11
  <=> k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f117,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f115,f98])).

fof(f98,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) = k2_relat_1(sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f95,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t62_funct_2.p',redefinition_k2_relset_1)).

fof(f115,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f116,plain,(
    ~ spl4_11 ),
    inference(avatar_split_clause,[],[f54,f114])).

fof(f54,plain,(
    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t62_funct_2.p',t62_funct_2)).

fof(f112,plain,
    ( spl4_8
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f102,f94,f110])).

fof(f102,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f95,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t62_funct_2.p',cc1_relset_1)).

fof(f96,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f52,f94])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f92,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f51,f90])).

fof(f51,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f88,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f53,f86])).

fof(f53,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f84,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f50,f82])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
