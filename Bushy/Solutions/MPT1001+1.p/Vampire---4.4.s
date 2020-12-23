%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t49_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:46 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 290 expanded)
%              Number of leaves         :   18 (  74 expanded)
%              Depth                    :   19
%              Number of atoms          :  255 (1304 expanded)
%              Number of equality atoms :   86 ( 589 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f394,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f334,f360,f367,f393])).

fof(f393,plain,
    ( ~ spl6_0
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f392])).

fof(f392,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f391,f98])).

fof(f98,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl6_0
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f391,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f390,f356])).

fof(f356,plain,
    ( k2_relat_1(sK2) = sK1
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f355])).

fof(f355,plain,
    ( spl6_6
  <=> k2_relat_1(sK2) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f390,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f386,f112])).

fof(f112,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f64,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t49_funct_2.p',cc1_relset_1)).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,
    ( ( k2_relset_1(sK0,sK1,sK2) != sK1
      | ( k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3)) = k1_xboole_0
        & r2_hidden(sK3,sK1) ) )
    & ( k2_relset_1(sK0,sK1,sK2) = sK1
      | ! [X4] :
          ( k8_relset_1(sK0,sK1,sK2,k1_tarski(X4)) != k1_xboole_0
          | ~ r2_hidden(X4,sK1) ) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f52,f54,f53])).

fof(f53,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relset_1(X0,X1,X2) != X1
          | ? [X3] :
              ( k8_relset_1(X0,X1,X2,k1_tarski(X3)) = k1_xboole_0
              & r2_hidden(X3,X1) ) )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ! [X4] :
              ( k8_relset_1(X0,X1,X2,k1_tarski(X4)) != k1_xboole_0
              | ~ r2_hidden(X4,X1) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k2_relset_1(sK0,sK1,sK2) != sK1
        | ? [X3] :
            ( k8_relset_1(sK0,sK1,sK2,k1_tarski(X3)) = k1_xboole_0
            & r2_hidden(X3,sK1) ) )
      & ( k2_relset_1(sK0,sK1,sK2) = sK1
        | ! [X4] :
            ( k8_relset_1(sK0,sK1,sK2,k1_tarski(X4)) != k1_xboole_0
            | ~ r2_hidden(X4,sK1) ) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k8_relset_1(X0,X1,X2,k1_tarski(X3)) = k1_xboole_0
          & r2_hidden(X3,X1) )
     => ( k8_relset_1(X0,X1,X2,k1_tarski(sK3)) = k1_xboole_0
        & r2_hidden(sK3,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( k8_relset_1(X0,X1,X2,k1_tarski(X3)) = k1_xboole_0
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X4] :
            ( k8_relset_1(X0,X1,X2,k1_tarski(X4)) != k1_xboole_0
            | ~ r2_hidden(X4,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( k8_relset_1(X0,X1,X2,k1_tarski(X3)) = k1_xboole_0
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X3] :
            ( k8_relset_1(X0,X1,X2,k1_tarski(X3)) != k1_xboole_0
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( k8_relset_1(X0,X1,X2,k1_tarski(X3)) = k1_xboole_0
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X3] :
            ( k8_relset_1(X0,X1,X2,k1_tarski(X3)) != k1_xboole_0
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( k8_relset_1(X0,X1,X2,k1_tarski(X3)) != k1_xboole_0
            | ~ r2_hidden(X3,X1) )
      <~> k2_relset_1(X0,X1,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( ! [X3] :
              ~ ( k8_relset_1(X0,X1,X2,k1_tarski(X3)) = k1_xboole_0
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(pure_predicate_removal,[],[f29])).

fof(f29,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( k8_relset_1(X0,X1,X2,k1_tarski(X3)) = k1_xboole_0
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( k8_relset_1(X0,X1,X2,k1_tarski(X3)) = k1_xboole_0
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( k8_relset_1(X0,X1,X2,k1_tarski(X3)) = k1_xboole_0
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t49_funct_2.p',t49_funct_2)).

fof(f386,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_4 ),
    inference(trivial_inequality_removal,[],[f383])).

fof(f383,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_4 ),
    inference(superposition,[],[f73,f370])).

fof(f370,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK3))
    | ~ spl6_4 ),
    inference(superposition,[],[f353,f132])).

fof(f132,plain,(
    ! [X0] : k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(unit_resulting_resolution,[],[f64,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t49_funct_2.p',redefinition_k8_relset_1)).

fof(f353,plain,
    ( k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3)) = k1_xboole_0
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl6_4
  <=> k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k2_relat_1(X1))
          | k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t49_funct_2.p',t142_funct_1)).

fof(f367,plain,
    ( ~ spl6_2
    | spl6_7 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f346,f359])).

fof(f359,plain,
    ( k2_relat_1(sK2) != sK1
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f358])).

fof(f358,plain,
    ( spl6_7
  <=> k2_relat_1(sK2) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f346,plain,
    ( k2_relat_1(sK2) = sK1
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f101,f120])).

fof(f120,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f64,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t49_funct_2.p',redefinition_k2_relset_1)).

fof(f101,plain,
    ( k2_relset_1(sK0,sK1,sK2) = sK1
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl6_2
  <=> k2_relset_1(sK0,sK1,sK2) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f360,plain,
    ( spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f338,f358,f352])).

fof(f338,plain,
    ( k2_relat_1(sK2) != sK1
    | k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3)) = k1_xboole_0 ),
    inference(forward_demodulation,[],[f67,f120])).

fof(f67,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

fof(f334,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f329,f146])).

fof(f146,plain,
    ( r2_hidden(sK4(sK1,sK2),sK1)
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f112,f134,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(sK4(X0,X1)))
        & r2_hidden(sK4(X0,X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
          & r2_hidden(X2,X0) )
     => ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(sK4(X0,X1)))
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ? [X2] :
          ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_relat_1(X1))
      | ? [X2] :
          ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ~ ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X2))
              & r2_hidden(X2,X0) )
       => r1_tarski(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t49_funct_2.p',t143_funct_1)).

fof(f134,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f120,f127])).

fof(f127,plain,
    ( ~ r1_tarski(sK1,k2_relset_1(sK0,sK1,sK2))
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f104,f123,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t49_funct_2.p',d10_xboole_0)).

fof(f123,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f117,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t49_funct_2.p',t3_subset)).

fof(f117,plain,(
    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f64,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t49_funct_2.p',dt_k2_relset_1)).

fof(f104,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl6_3
  <=> k2_relset_1(sK0,sK1,sK2) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f329,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK1)
    | ~ spl6_3 ),
    inference(trivial_inequality_removal,[],[f324])).

fof(f324,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK4(sK1,sK2),sK1)
    | ~ spl6_3 ),
    inference(superposition,[],[f148,f145])).

fof(f145,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK4(sK1,sK2)))
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f112,f134,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = k10_relat_1(X1,k1_tarski(sK4(X0,X1)))
      | r1_tarski(X0,k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f148,plain,
    ( ! [X4] :
        ( k1_xboole_0 != k10_relat_1(sK2,k1_tarski(X4))
        | ~ r2_hidden(X4,sK1) )
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f132,f106])).

fof(f106,plain,
    ( ! [X4] :
        ( k8_relset_1(sK0,sK1,sK2,k1_tarski(X4)) != k1_xboole_0
        | ~ r2_hidden(X4,sK1) )
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f65,f104])).

fof(f65,plain,(
    ! [X4] :
      ( k2_relset_1(sK0,sK1,sK2) = sK1
      | k8_relset_1(sK0,sK1,sK2,k1_tarski(X4)) != k1_xboole_0
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f105,plain,
    ( spl6_0
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f66,f103,f97])).

fof(f66,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f55])).
%------------------------------------------------------------------------------
