%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t41_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:45 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 138 expanded)
%              Number of leaves         :   20 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :  248 ( 480 expanded)
%              Number of equality atoms :   59 ( 112 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f268,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f102,f106,f119,f127,f146,f163,f167,f176,f185,f247,f248,f264])).

fof(f264,plain,
    ( ~ spl6_0
    | ~ spl6_20
    | spl6_25
    | ~ spl6_40 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f262,f175])).

fof(f175,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k8_relat_1(sK3,sK4),sK2)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl6_25
  <=> k1_funct_1(sK4,sK2) != k1_funct_1(k8_relat_1(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f262,plain,
    ( k1_funct_1(sK4,sK2) = k1_funct_1(k8_relat_1(sK3,sK4),sK2)
    | ~ spl6_0
    | ~ spl6_20
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f261,f162])).

fof(f162,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl6_20
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f261,plain,
    ( ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK2) = k1_funct_1(k8_relat_1(sK3,sK4),sK2)
    | ~ spl6_0
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f253,f97])).

fof(f97,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl6_0
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f253,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,sK2) = k1_funct_1(k8_relat_1(sK3,sK4),sK2)
    | ~ spl6_40 ),
    inference(resolution,[],[f243,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
       => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t41_funct_2.p',t87_funct_1)).

fof(f243,plain,
    ( r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4)))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl6_40
  <=> r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f248,plain,
    ( k1_relat_1(sK4) != sK0
    | r2_hidden(sK2,k1_relat_1(sK4))
    | ~ r2_hidden(sK2,sK0) ),
    introduced(theory_axiom,[])).

fof(f247,plain,
    ( spl6_40
    | ~ spl6_43
    | ~ spl6_0
    | ~ spl6_12
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f157,f144,f125,f96,f245,f242])).

fof(f245,plain,
    ( spl6_43
  <=> ~ r2_hidden(sK2,k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f125,plain,
    ( spl6_12
  <=> r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f144,plain,
    ( spl6_18
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f157,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK4))
    | r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4)))
    | ~ spl6_0
    | ~ spl6_12
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f138,f151])).

fof(f151,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_18 ),
    inference(resolution,[],[f145,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t41_funct_2.p',cc1_relset_1)).

fof(f145,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f144])).

fof(f138,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4)))
    | ~ spl6_0
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f132,f97])).

fof(f132,plain,
    ( ~ v1_funct_1(sK4)
    | ~ r2_hidden(sK2,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4)))
    | ~ spl6_12 ),
    inference(resolution,[],[f126,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t41_funct_2.p',t86_funct_1)).

fof(f126,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2),sK3)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f125])).

fof(f185,plain,
    ( spl6_28
    | spl6_5
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f159,f144,f117,f104,f183])).

fof(f183,plain,
    ( spl6_28
  <=> k1_relat_1(sK4) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f104,plain,
    ( spl6_5
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f117,plain,
    ( spl6_8
  <=> v1_funct_2(sK4,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f159,plain,
    ( k1_relat_1(sK4) = sK0
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f153,f156])).

fof(f156,plain,
    ( k1_relset_1(sK0,sK1,sK4) = sK0
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f155,f118])).

fof(f118,plain,
    ( v1_funct_2(sK4,sK0,sK1)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f117])).

fof(f155,plain,
    ( k1_relset_1(sK0,sK1,sK4) = sK0
    | ~ v1_funct_2(sK4,sK0,sK1)
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f150,f105])).

fof(f105,plain,
    ( k1_xboole_0 != sK1
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f104])).

fof(f150,plain,
    ( k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK4) = sK0
    | ~ v1_funct_2(sK4,sK0,sK1)
    | ~ spl6_18 ),
    inference(resolution,[],[f145,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t41_funct_2.p',d1_funct_2)).

fof(f153,plain,
    ( k1_relset_1(sK0,sK1,sK4) = k1_relat_1(sK4)
    | ~ spl6_18 ),
    inference(resolution,[],[f145,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t41_funct_2.p',redefinition_k1_relset_1)).

fof(f176,plain,
    ( ~ spl6_25
    | ~ spl6_18
    | spl6_23 ),
    inference(avatar_split_clause,[],[f168,f165,f144,f174])).

fof(f165,plain,
    ( spl6_23
  <=> k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f168,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k8_relat_1(sK3,sK4),sK2)
    | ~ spl6_18
    | ~ spl6_23 ),
    inference(forward_demodulation,[],[f166,f148])).

fof(f148,plain,
    ( ! [X1] : k6_relset_1(sK0,sK1,X1,sK4) = k8_relat_1(X1,sK4)
    | ~ spl6_18 ),
    inference(resolution,[],[f145,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t41_funct_2.p',redefinition_k6_relset_1)).

fof(f166,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f165])).

fof(f167,plain,(
    ~ spl6_23 ),
    inference(avatar_split_clause,[],[f62,f165])).

fof(f62,plain,(
    k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
      & k1_xboole_0 != X1
      & r2_hidden(k1_funct_1(X4,X2),X3)
      & r2_hidden(X2,X0)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X4,X0,X1)
      & v1_funct_1(X4) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
      & k1_xboole_0 != X1
      & r2_hidden(k1_funct_1(X4,X2),X3)
      & r2_hidden(X2,X0)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X4,X0,X1)
      & v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X4,X0,X1)
          & v1_funct_1(X4) )
       => ( ( r2_hidden(k1_funct_1(X4,X2),X3)
            & r2_hidden(X2,X0) )
         => ( k1_funct_1(X4,X2) = k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4) )
     => ( ( r2_hidden(k1_funct_1(X4,X2),X3)
          & r2_hidden(X2,X0) )
       => ( k1_funct_1(X4,X2) = k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t41_funct_2.p',t41_funct_2)).

fof(f163,plain,
    ( spl6_20
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f151,f144,f161])).

fof(f146,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f58,f144])).

fof(f58,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f127,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f60,f125])).

fof(f60,plain,(
    r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f119,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f57,f117])).

fof(f57,plain,(
    v1_funct_2(sK4,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f106,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f61,f104])).

fof(f61,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f102,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f59,f100])).

fof(f100,plain,
    ( spl6_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f59,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f98,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f56,f96])).

fof(f56,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
