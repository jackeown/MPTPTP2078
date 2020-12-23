%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t61_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:48 EDT 2019

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 120 expanded)
%              Number of leaves         :   18 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  220 ( 350 expanded)
%              Number of equality atoms :   57 (  76 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f385,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f93,f97,f101,f105,f123,f134,f140,f332,f384])).

fof(f384,plain,
    ( spl4_7
    | ~ spl4_16
    | ~ spl4_74 ),
    inference(avatar_contradiction_clause,[],[f383])).

fof(f383,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_16
    | ~ spl4_74 ),
    inference(subsumption_resolution,[],[f382,f100])).

fof(f100,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_7
  <=> ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f382,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ spl4_16
    | ~ spl4_74 ),
    inference(resolution,[],[f336,f139])).

fof(f139,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl4_16
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f336,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK2),X0)
        | r2_hidden(k1_funct_1(sK2,sK0),X0) )
    | ~ spl4_74 ),
    inference(superposition,[],[f73,f331])).

fof(f331,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | ~ spl4_74 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl4_74
  <=> k1_tarski(k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t61_funct_2.p',t37_zfmisc_1)).

fof(f332,plain,
    ( spl4_74
    | ~ spl4_0
    | spl4_3
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f318,f121,f103,f95,f91,f87,f330])).

fof(f87,plain,
    ( spl4_0
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f91,plain,
    ( spl4_3
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f95,plain,
    ( spl4_4
  <=> v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f103,plain,
    ( spl4_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f121,plain,
    ( spl4_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f318,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | ~ spl4_0
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(equality_resolution,[],[f126])).

fof(f126,plain,
    ( ! [X0] :
        ( k1_tarski(sK0) != k1_tarski(X0)
        | k1_tarski(k1_funct_1(sK2,X0)) = k2_relat_1(sK2) )
    | ~ spl4_0
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f125,f117])).

fof(f117,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK2)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f109,f116])).

fof(f116,plain,
    ( k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f115,f96])).

fof(f96,plain,
    ( v1_funct_2(sK2,k1_tarski(sK0),sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f115,plain,
    ( k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2)
    | ~ v1_funct_2(sK2,k1_tarski(sK0),sK1)
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f107,f92])).

fof(f92,plain,
    ( k1_xboole_0 != sK1
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f107,plain,
    ( k1_xboole_0 = sK1
    | k1_tarski(sK0) = k1_relset_1(k1_tarski(sK0),sK1,sK2)
    | ~ v1_funct_2(sK2,k1_tarski(sK0),sK1)
    | ~ spl4_8 ),
    inference(resolution,[],[f104,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t61_funct_2.p',d1_funct_2)).

fof(f104,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f109,plain,
    ( k1_relset_1(k1_tarski(sK0),sK1,sK2) = k1_relat_1(sK2)
    | ~ spl4_8 ),
    inference(resolution,[],[f104,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t61_funct_2.p',redefinition_k1_relset_1)).

fof(f125,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != k1_relat_1(sK2)
        | k1_tarski(k1_funct_1(sK2,X0)) = k2_relat_1(sK2) )
    | ~ spl4_0
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f124,f88])).

fof(f88,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f87])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | k1_tarski(X0) != k1_relat_1(sK2)
        | k1_tarski(k1_funct_1(sK2,X0)) = k2_relat_1(sK2) )
    | ~ spl4_10 ),
    inference(resolution,[],[f122,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t61_funct_2.p',t14_funct_1)).

fof(f122,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f140,plain,
    ( spl4_16
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f135,f132,f138])).

fof(f132,plain,
    ( spl4_14
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f135,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl4_14 ),
    inference(resolution,[],[f133,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t61_funct_2.p',t3_subset)).

fof(f133,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f132])).

fof(f134,plain,
    ( spl4_14
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f119,f103,f132])).

fof(f119,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f112,f108])).

fof(f108,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) = k2_relat_1(sK2)
    | ~ spl4_8 ),
    inference(resolution,[],[f104,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t61_funct_2.p',redefinition_k2_relset_1)).

fof(f112,plain,
    ( m1_subset_1(k2_relset_1(k1_tarski(sK0),sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl4_8 ),
    inference(resolution,[],[f104,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t61_funct_2.p',dt_k2_relset_1)).

fof(f123,plain,
    ( spl4_10
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f110,f103,f121])).

fof(f110,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_8 ),
    inference(resolution,[],[f104,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t61_funct_2.p',cc1_relset_1)).

fof(f105,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f53,f103])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
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
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t61_funct_2.p',t61_funct_2)).

fof(f101,plain,(
    ~ spl4_7 ),
    inference(avatar_split_clause,[],[f55,f99])).

fof(f55,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f97,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f52,f95])).

fof(f52,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f93,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f54,f91])).

fof(f54,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f89,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f51,f87])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
