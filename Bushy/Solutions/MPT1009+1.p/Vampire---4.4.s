%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t64_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:48 EDT 2019

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 123 expanded)
%              Number of leaves         :   21 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :  199 ( 335 expanded)
%              Number of equality atoms :   34 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f196,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f83,f90,f97,f104,f111,f121,f138,f164,f174,f192,f195])).

fof(f195,plain,
    ( ~ spl5_14
    | spl5_23 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | ~ spl5_14
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f193,f137])).

fof(f137,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl5_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f193,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl5_23 ),
    inference(resolution,[],[f191,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t64_funct_2.p',t144_relat_1)).

fof(f191,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl5_23
  <=> ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f192,plain,
    ( ~ spl5_23
    | ~ spl5_0
    | spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | spl5_17 ),
    inference(avatar_split_clause,[],[f184,f162,f95,f88,f81,f74,f190])).

fof(f74,plain,
    ( spl5_0
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f81,plain,
    ( spl5_3
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f88,plain,
    ( spl5_4
  <=> v1_funct_2(sK3,k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f95,plain,
    ( spl5_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f162,plain,
    ( spl5_17
  <=> ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f184,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_17 ),
    inference(backward_demodulation,[],[f183,f163])).

fof(f163,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f162])).

fof(f183,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f182,f139])).

fof(f139,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK3) = k2_relat_1(sK3)
    | ~ spl5_6 ),
    inference(resolution,[],[f59,f96])).

fof(f96,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t64_funct_2.p',redefinition_k2_relset_1)).

fof(f182,plain,
    ( k1_tarski(k1_funct_1(sK3,sK0)) = k2_relset_1(k1_tarski(sK0),sK1,sK3)
    | ~ spl5_0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f181,f82])).

fof(f82,plain,
    ( k1_xboole_0 != sK1
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f181,plain,
    ( k1_xboole_0 = sK1
    | k1_tarski(k1_funct_1(sK3,sK0)) = k2_relset_1(k1_tarski(sK0),sK1,sK3)
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f180,f75])).

fof(f75,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f74])).

fof(f180,plain,
    ( ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK1
    | k1_tarski(k1_funct_1(sK3,sK0)) = k2_relset_1(k1_tarski(sK0),sK1,sK3)
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f178,f89])).

fof(f89,plain,
    ( v1_funct_2(sK3,k1_tarski(sK0),sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f178,plain,
    ( ~ v1_funct_2(sK3,k1_tarski(sK0),sK1)
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK1
    | k1_tarski(k1_funct_1(sK3,sK0)) = k2_relset_1(k1_tarski(sK0),sK1,sK3)
    | ~ spl5_6 ),
    inference(resolution,[],[f56,f96])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      | ~ v1_funct_2(X2,k1_tarski(X0),X1)
      | ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      | ~ v1_funct_2(X2,k1_tarski(X0),X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      | ~ v1_funct_2(X2,k1_tarski(X0),X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t64_funct_2.p',t62_funct_2)).

fof(f174,plain,
    ( ~ spl5_19
    | spl5_20
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f126,f95,f172,f169])).

fof(f169,plain,
    ( spl5_19
  <=> ~ v1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f172,plain,
    ( spl5_20
  <=> ! [X0] : ~ r2_hidden(X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | ~ v1_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK1)) )
    | ~ spl5_6 ),
    inference(resolution,[],[f63,f96])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t64_funct_2.p',t5_subset)).

fof(f164,plain,
    ( ~ spl5_17
    | ~ spl5_6
    | spl5_9 ),
    inference(avatar_split_clause,[],[f157,f102,f95,f162])).

fof(f102,plain,
    ( spl5_9
  <=> ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f157,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(backward_demodulation,[],[f155,f103])).

fof(f103,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f102])).

fof(f155,plain,
    ( ! [X15] : k7_relset_1(k1_tarski(sK0),sK1,sK3,X15) = k9_relat_1(sK3,X15)
    | ~ spl5_6 ),
    inference(resolution,[],[f57,f96])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t64_funct_2.p',redefinition_k7_relset_1)).

fof(f138,plain,
    ( spl5_14
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f123,f95,f136])).

fof(f123,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_6 ),
    inference(resolution,[],[f69,f96])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t64_funct_2.p',cc1_relset_1)).

fof(f121,plain,
    ( spl5_12
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f112,f95,f119])).

fof(f119,plain,
    ( spl5_12
  <=> r1_tarski(sK3,k2_zfmisc_1(k1_tarski(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f112,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_tarski(sK0),sK1))
    | ~ spl5_6 ),
    inference(resolution,[],[f54,f96])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t64_funct_2.p',t3_subset)).

fof(f111,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f62,f109])).

fof(f109,plain,
    ( spl5_10
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f62,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t64_funct_2.p',d2_xboole_0)).

fof(f104,plain,(
    ~ spl5_9 ),
    inference(avatar_split_clause,[],[f52,f102])).

fof(f52,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t64_funct_2.p',t64_funct_2)).

fof(f97,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f50,f95])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f90,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f49,f88])).

fof(f49,plain,(
    v1_funct_2(sK3,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f83,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f51,f81])).

fof(f51,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f48,f74])).

fof(f48,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
