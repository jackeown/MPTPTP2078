%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 749 expanded)
%              Number of leaves         :   26 ( 201 expanded)
%              Depth                    :   16
%              Number of atoms          :  551 (4223 expanded)
%              Number of equality atoms :  123 (1028 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f594,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f102,f119,f149,f206,f212,f242,f248,f283,f327,f344,f384,f388,f499,f559,f562,f564,f593])).

fof(f593,plain,(
    ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f589])).

fof(f589,plain,
    ( $false
    | ~ spl4_10 ),
    inference(resolution,[],[f201,f136])).

fof(f136,plain,(
    ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f133,f134])).

fof(f134,plain,(
    ! [X2] : k7_relat_1(sK3,X2) = k2_partfun1(sK0,sK1,sK3,X2) ),
    inference(subsumption_resolution,[],[f125,f43])).

fof(f43,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

fof(f125,plain,(
    ! [X2] :
      ( k7_relat_1(sK3,X2) = k2_partfun1(sK0,sK1,sK3,X2)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f45,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f133,plain,(
    ! [X1] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f124,f43])).

fof(f124,plain,(
    ! [X1] :
      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f45,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f201,plain,
    ( ! [X0] : ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl4_10
  <=> ! [X0] : ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f564,plain,
    ( ~ spl4_8
    | ~ spl4_9
    | spl4_2
    | spl4_4 ),
    inference(avatar_split_clause,[],[f563,f95,f86,f161,f157])).

fof(f157,plain,
    ( spl4_8
  <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f161,plain,
    ( spl4_9
  <=> sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f86,plain,
    ( spl4_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f95,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f563,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f538,f97])).

fof(f97,plain,
    ( k1_xboole_0 != sK1
    | spl4_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f538,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_2 ),
    inference(resolution,[],[f150,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f150,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(forward_demodulation,[],[f88,f134])).

fof(f88,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f562,plain,
    ( spl4_3
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f561])).

fof(f561,plain,
    ( $false
    | spl4_3
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f560,f158])).

fof(f158,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f157])).

fof(f560,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(forward_demodulation,[],[f92,f134])).

fof(f92,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f559,plain,
    ( ~ spl4_3
    | spl4_9
    | ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f558])).

fof(f558,plain,
    ( $false
    | ~ spl4_3
    | spl4_9
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f557,f163])).

fof(f163,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f161])).

fof(f557,plain,
    ( sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f549,f240])).

fof(f240,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl4_13
  <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f549,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_3 ),
    inference(resolution,[],[f502,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f502,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f91,f134])).

fof(f91,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f499,plain,
    ( spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f498])).

fof(f498,plain,
    ( $false
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f492,f410])).

fof(f410,plain,
    ( ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f395,f73])).

fof(f73,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f395,plain,
    ( ! [X1] : m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f136,f390])).

fof(f390,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f117,f303])).

fof(f303,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f117,f101])).

fof(f101,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f117,plain,
    ( sK0 = sK2
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl4_7
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f492,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f491,f72])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f491,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f482,f424])).

fof(f424,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0))
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f407,f96])).

fof(f96,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f407,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,k1_xboole_0))
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f364,f390])).

fof(f364,plain,
    ( sK0 = k1_relset_1(sK0,sK1,k7_relat_1(sK3,sK0))
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f351,f362])).

fof(f362,plain,
    ( sK0 = k1_relat_1(k7_relat_1(sK3,sK0))
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f240,f117])).

fof(f351,plain,
    ( k1_relset_1(sK0,sK1,k7_relat_1(sK3,sK0)) = k1_relat_1(k7_relat_1(sK3,sK0))
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f219,f117])).

fof(f219,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_8 ),
    inference(resolution,[],[f158,f67])).

fof(f482,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0))
    | ~ m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(resolution,[],[f435,f79])).

fof(f79,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f435,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f289,f303])).

fof(f289,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0)
    | spl4_2
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f150,f96])).

fof(f388,plain,
    ( ~ spl4_7
    | spl4_8 ),
    inference(avatar_contradiction_clause,[],[f387])).

fof(f387,plain,
    ( $false
    | ~ spl4_7
    | spl4_8 ),
    inference(subsumption_resolution,[],[f386,f136])).

fof(f386,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_7
    | spl4_8 ),
    inference(forward_demodulation,[],[f159,f117])).

fof(f159,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f157])).

fof(f384,plain,
    ( spl4_3
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f383])).

fof(f383,plain,
    ( $false
    | spl4_3
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f378,f136])).

fof(f378,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_3
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f377,f134])).

fof(f377,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_3
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f92,f117])).

fof(f344,plain,
    ( ~ spl4_5
    | ~ spl4_7
    | spl4_11 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_7
    | spl4_11 ),
    inference(subsumption_resolution,[],[f342,f55])).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f342,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | ~ spl4_5
    | ~ spl4_7
    | spl4_11 ),
    inference(forward_demodulation,[],[f209,f303])).

fof(f209,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | spl4_11 ),
    inference(subsumption_resolution,[],[f208,f140])).

fof(f140,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f131,f68])).

fof(f68,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f131,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f45,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f208,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_11 ),
    inference(subsumption_resolution,[],[f207,f75])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f207,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_11 ),
    inference(superposition,[],[f205,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f205,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl4_11
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f327,plain,
    ( ~ spl4_5
    | ~ spl4_7
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f326])).

fof(f326,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_7
    | spl4_12 ),
    inference(subsumption_resolution,[],[f309,f55])).

fof(f309,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | ~ spl4_5
    | ~ spl4_7
    | spl4_12 ),
    inference(backward_demodulation,[],[f245,f303])).

fof(f245,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | spl4_12 ),
    inference(subsumption_resolution,[],[f244,f140])).

fof(f244,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_12 ),
    inference(subsumption_resolution,[],[f243,f75])).

fof(f243,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_12 ),
    inference(superposition,[],[f236,f71])).

fof(f236,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(k7_relat_1(sK3,sK2)))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl4_12
  <=> r1_tarski(sK2,k1_relat_1(k7_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f283,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | ~ spl4_5
    | spl4_6 ),
    inference(subsumption_resolution,[],[f272,f55])).

fof(f272,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_5
    | spl4_6 ),
    inference(backward_demodulation,[],[f113,f101])).

fof(f113,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl4_6
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f248,plain,
    ( spl4_4
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | spl4_4
    | spl4_12 ),
    inference(subsumption_resolution,[],[f246,f46])).

fof(f46,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f246,plain,
    ( ~ r1_tarski(sK2,sK0)
    | spl4_4
    | spl4_12 ),
    inference(forward_demodulation,[],[f245,f138])).

fof(f138,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl4_4 ),
    inference(forward_demodulation,[],[f129,f122])).

fof(f122,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f121,f45])).

fof(f121,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_4 ),
    inference(subsumption_resolution,[],[f120,f97])).

fof(f120,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f44,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f44,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f129,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f45,f67])).

fof(f242,plain,
    ( ~ spl4_12
    | spl4_13
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f230,f203,f238,f234])).

fof(f230,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ r1_tarski(sK2,k1_relat_1(k7_relat_1(sK3,sK2)))
    | ~ spl4_11 ),
    inference(resolution,[],[f204,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f204,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f203])).

fof(f212,plain,
    ( spl4_4
    | spl4_11 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | spl4_4
    | spl4_11 ),
    inference(subsumption_resolution,[],[f210,f46])).

fof(f210,plain,
    ( ~ r1_tarski(sK2,sK0)
    | spl4_4
    | spl4_11 ),
    inference(forward_demodulation,[],[f209,f138])).

fof(f206,plain,
    ( spl4_10
    | ~ spl4_11
    | spl4_8 ),
    inference(avatar_split_clause,[],[f197,f157,f203,f200])).

fof(f197,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
        | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) )
    | spl4_8 ),
    inference(resolution,[],[f159,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f149,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl4_1 ),
    inference(resolution,[],[f137,f135])).

fof(f135,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | spl4_1 ),
    inference(backward_demodulation,[],[f84,f134])).

fof(f84,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl4_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f137,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK3,X0)) ),
    inference(backward_demodulation,[],[f132,f134])).

fof(f132,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) ),
    inference(subsumption_resolution,[],[f123,f43])).

fof(f123,plain,(
    ! [X0] :
      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f45,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f119,plain,
    ( ~ spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f108,f115,f111])).

fof(f108,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f46,f59])).

fof(f102,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f47,f99,f95])).

fof(f47,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f37])).

fof(f93,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f48,f90,f86,f82])).

fof(f48,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:30:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (31164)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (31183)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.50  % (31175)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (31161)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (31163)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (31167)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.51  % (31180)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (31168)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (31160)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (31165)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (31178)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (31176)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.52  % (31177)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.52  % (31169)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.52  % (31171)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  % (31170)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.53  % (31185)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.53  % (31162)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.53  % (31172)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.53  % (31166)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.53  % (31179)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.54  % (31173)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (31181)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.55  % (31174)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.55  % (31184)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.55  % (31171)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f594,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f93,f102,f119,f149,f206,f212,f242,f248,f283,f327,f344,f384,f388,f499,f559,f562,f564,f593])).
% 0.20/0.55  fof(f593,plain,(
% 0.20/0.55    ~spl4_10),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f589])).
% 0.20/0.55  fof(f589,plain,(
% 0.20/0.55    $false | ~spl4_10),
% 0.20/0.55    inference(resolution,[],[f201,f136])).
% 0.20/0.55  fof(f136,plain,(
% 0.20/0.55    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 0.20/0.55    inference(backward_demodulation,[],[f133,f134])).
% 0.20/0.55  fof(f134,plain,(
% 0.20/0.55    ( ! [X2] : (k7_relat_1(sK3,X2) = k2_partfun1(sK0,sK1,sK3,X2)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f125,f43])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    v1_funct_1(sK3)),
% 0.20/0.55    inference(cnf_transformation,[],[f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.55    inference(flattening,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.55    inference(ennf_transformation,[],[f17])).
% 0.20/0.55  fof(f17,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.55    inference(negated_conjecture,[],[f16])).
% 0.20/0.55  fof(f16,conjecture,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 0.20/0.55  fof(f125,plain,(
% 0.20/0.55    ( ! [X2] : (k7_relat_1(sK3,X2) = k2_partfun1(sK0,sK1,sK3,X2) | ~v1_funct_1(sK3)) )),
% 0.20/0.55    inference(resolution,[],[f45,f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.55    inference(flattening,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.55    inference(cnf_transformation,[],[f37])).
% 0.20/0.55  fof(f133,plain,(
% 0.20/0.55    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f124,f43])).
% 0.20/0.55  fof(f124,plain,(
% 0.20/0.55    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) )),
% 0.20/0.55    inference(resolution,[],[f45,f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.55    inference(flattening,[],[f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.20/0.55  fof(f201,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | ~spl4_10),
% 0.20/0.55    inference(avatar_component_clause,[],[f200])).
% 0.20/0.55  fof(f200,plain,(
% 0.20/0.55    spl4_10 <=> ! [X0] : ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.55  fof(f564,plain,(
% 0.20/0.55    ~spl4_8 | ~spl4_9 | spl4_2 | spl4_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f563,f95,f86,f161,f157])).
% 0.20/0.55  fof(f157,plain,(
% 0.20/0.55    spl4_8 <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.55  fof(f161,plain,(
% 0.20/0.55    spl4_9 <=> sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.55  fof(f86,plain,(
% 0.20/0.55    spl4_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.55  fof(f95,plain,(
% 0.20/0.55    spl4_4 <=> k1_xboole_0 = sK1),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.55  fof(f563,plain,(
% 0.20/0.55    sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_2 | spl4_4)),
% 0.20/0.55    inference(subsumption_resolution,[],[f538,f97])).
% 0.20/0.55  fof(f97,plain,(
% 0.20/0.55    k1_xboole_0 != sK1 | spl4_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f95])).
% 0.20/0.55  fof(f538,plain,(
% 0.20/0.55    sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | k1_xboole_0 = sK1 | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_2),
% 0.20/0.55    inference(resolution,[],[f150,f62])).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(nnf_transformation,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(flattening,[],[f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.55  fof(f150,plain,(
% 0.20/0.55    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_2),
% 0.20/0.55    inference(forward_demodulation,[],[f88,f134])).
% 0.20/0.55  fof(f88,plain,(
% 0.20/0.55    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f86])).
% 0.20/0.55  fof(f562,plain,(
% 0.20/0.55    spl4_3 | ~spl4_8),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f561])).
% 0.20/0.55  fof(f561,plain,(
% 0.20/0.55    $false | (spl4_3 | ~spl4_8)),
% 0.20/0.55    inference(subsumption_resolution,[],[f560,f158])).
% 0.20/0.55  fof(f158,plain,(
% 0.20/0.55    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_8),
% 0.20/0.55    inference(avatar_component_clause,[],[f157])).
% 0.20/0.55  fof(f560,plain,(
% 0.20/0.55    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 0.20/0.55    inference(forward_demodulation,[],[f92,f134])).
% 0.20/0.55  fof(f92,plain,(
% 0.20/0.55    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f90])).
% 0.20/0.55  fof(f90,plain,(
% 0.20/0.55    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.55  fof(f559,plain,(
% 0.20/0.55    ~spl4_3 | spl4_9 | ~spl4_13),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f558])).
% 0.20/0.55  fof(f558,plain,(
% 0.20/0.55    $false | (~spl4_3 | spl4_9 | ~spl4_13)),
% 0.20/0.55    inference(subsumption_resolution,[],[f557,f163])).
% 0.20/0.55  fof(f163,plain,(
% 0.20/0.55    sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | spl4_9),
% 0.20/0.55    inference(avatar_component_clause,[],[f161])).
% 0.20/0.55  fof(f557,plain,(
% 0.20/0.55    sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | (~spl4_3 | ~spl4_13)),
% 0.20/0.55    inference(forward_demodulation,[],[f549,f240])).
% 0.20/0.55  fof(f240,plain,(
% 0.20/0.55    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_13),
% 0.20/0.55    inference(avatar_component_clause,[],[f238])).
% 0.20/0.55  fof(f238,plain,(
% 0.20/0.55    spl4_13 <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.55  fof(f549,plain,(
% 0.20/0.55    k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_3),
% 0.20/0.55    inference(resolution,[],[f502,f67])).
% 0.20/0.55  fof(f67,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.55  fof(f502,plain,(
% 0.20/0.55    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_3),
% 0.20/0.55    inference(backward_demodulation,[],[f91,f134])).
% 0.20/0.55  fof(f91,plain,(
% 0.20/0.55    m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f90])).
% 0.20/0.55  fof(f499,plain,(
% 0.20/0.55    spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_13),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f498])).
% 0.20/0.55  fof(f498,plain,(
% 0.20/0.55    $false | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_13)),
% 0.20/0.55    inference(subsumption_resolution,[],[f492,f410])).
% 0.20/0.55  fof(f410,plain,(
% 0.20/0.55    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k1_xboole_0))) ) | (~spl4_5 | ~spl4_7)),
% 0.20/0.55    inference(forward_demodulation,[],[f395,f73])).
% 0.20/0.55  fof(f73,plain,(
% 0.20/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.55    inference(equality_resolution,[],[f53])).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f39])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.55    inference(flattening,[],[f38])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.55    inference(nnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.55  fof(f395,plain,(
% 0.20/0.55    ( ! [X1] : (m1_subset_1(k7_relat_1(sK3,X1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))) ) | (~spl4_5 | ~spl4_7)),
% 0.20/0.55    inference(backward_demodulation,[],[f136,f390])).
% 0.20/0.55  fof(f390,plain,(
% 0.20/0.55    k1_xboole_0 = sK0 | (~spl4_5 | ~spl4_7)),
% 0.20/0.55    inference(backward_demodulation,[],[f117,f303])).
% 0.20/0.55  fof(f303,plain,(
% 0.20/0.55    k1_xboole_0 = sK2 | (~spl4_5 | ~spl4_7)),
% 0.20/0.55    inference(forward_demodulation,[],[f117,f101])).
% 0.20/0.55  fof(f101,plain,(
% 0.20/0.55    k1_xboole_0 = sK0 | ~spl4_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f99])).
% 0.20/0.55  fof(f99,plain,(
% 0.20/0.55    spl4_5 <=> k1_xboole_0 = sK0),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.55  fof(f117,plain,(
% 0.20/0.55    sK0 = sK2 | ~spl4_7),
% 0.20/0.55    inference(avatar_component_clause,[],[f115])).
% 0.20/0.55  fof(f115,plain,(
% 0.20/0.55    spl4_7 <=> sK0 = sK2),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.55  fof(f492,plain,(
% 0.20/0.55    ~m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_13)),
% 0.20/0.55    inference(forward_demodulation,[],[f491,f72])).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f54])).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f39])).
% 0.20/0.55  fof(f491,plain,(
% 0.20/0.55    ~m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_13)),
% 0.20/0.55    inference(subsumption_resolution,[],[f482,f424])).
% 0.20/0.55  fof(f424,plain,(
% 0.20/0.55    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) | (~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_13)),
% 0.20/0.55    inference(backward_demodulation,[],[f407,f96])).
% 0.20/0.55  fof(f96,plain,(
% 0.20/0.55    k1_xboole_0 = sK1 | ~spl4_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f95])).
% 0.20/0.55  fof(f407,plain,(
% 0.20/0.55    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,k1_xboole_0)) | (~spl4_5 | ~spl4_7 | ~spl4_8 | ~spl4_13)),
% 0.20/0.55    inference(backward_demodulation,[],[f364,f390])).
% 0.20/0.55  fof(f364,plain,(
% 0.20/0.55    sK0 = k1_relset_1(sK0,sK1,k7_relat_1(sK3,sK0)) | (~spl4_7 | ~spl4_8 | ~spl4_13)),
% 0.20/0.55    inference(backward_demodulation,[],[f351,f362])).
% 0.20/0.55  fof(f362,plain,(
% 0.20/0.55    sK0 = k1_relat_1(k7_relat_1(sK3,sK0)) | (~spl4_7 | ~spl4_13)),
% 0.20/0.55    inference(forward_demodulation,[],[f240,f117])).
% 0.20/0.55  fof(f351,plain,(
% 0.20/0.55    k1_relset_1(sK0,sK1,k7_relat_1(sK3,sK0)) = k1_relat_1(k7_relat_1(sK3,sK0)) | (~spl4_7 | ~spl4_8)),
% 0.20/0.55    inference(backward_demodulation,[],[f219,f117])).
% 0.20/0.55  fof(f219,plain,(
% 0.20/0.55    k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_8),
% 0.20/0.55    inference(resolution,[],[f158,f67])).
% 0.20/0.55  fof(f482,plain,(
% 0.20/0.55    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) | ~m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7)),
% 0.20/0.55    inference(resolution,[],[f435,f79])).
% 0.20/0.55  fof(f79,plain,(
% 0.20/0.55    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.55    inference(equality_resolution,[],[f63])).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f42])).
% 0.20/0.55  fof(f435,plain,(
% 0.20/0.55    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_7)),
% 0.20/0.55    inference(forward_demodulation,[],[f289,f303])).
% 0.20/0.55  fof(f289,plain,(
% 0.20/0.55    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) | (spl4_2 | ~spl4_4)),
% 0.20/0.55    inference(backward_demodulation,[],[f150,f96])).
% 0.20/0.55  fof(f388,plain,(
% 0.20/0.55    ~spl4_7 | spl4_8),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f387])).
% 0.20/0.55  fof(f387,plain,(
% 0.20/0.55    $false | (~spl4_7 | spl4_8)),
% 0.20/0.55    inference(subsumption_resolution,[],[f386,f136])).
% 0.20/0.55  fof(f386,plain,(
% 0.20/0.55    ~m1_subset_1(k7_relat_1(sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl4_7 | spl4_8)),
% 0.20/0.55    inference(forward_demodulation,[],[f159,f117])).
% 0.20/0.55  fof(f159,plain,(
% 0.20/0.55    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_8),
% 0.20/0.55    inference(avatar_component_clause,[],[f157])).
% 0.20/0.55  fof(f384,plain,(
% 0.20/0.55    spl4_3 | ~spl4_7),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f383])).
% 0.20/0.55  fof(f383,plain,(
% 0.20/0.55    $false | (spl4_3 | ~spl4_7)),
% 0.20/0.55    inference(subsumption_resolution,[],[f378,f136])).
% 0.20/0.55  fof(f378,plain,(
% 0.20/0.55    ~m1_subset_1(k7_relat_1(sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl4_3 | ~spl4_7)),
% 0.20/0.55    inference(forward_demodulation,[],[f377,f134])).
% 0.20/0.55  fof(f377,plain,(
% 0.20/0.55    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl4_3 | ~spl4_7)),
% 0.20/0.55    inference(forward_demodulation,[],[f92,f117])).
% 0.20/0.55  fof(f344,plain,(
% 0.20/0.55    ~spl4_5 | ~spl4_7 | spl4_11),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f343])).
% 0.20/0.55  fof(f343,plain,(
% 0.20/0.55    $false | (~spl4_5 | ~spl4_7 | spl4_11)),
% 0.20/0.55    inference(subsumption_resolution,[],[f342,f55])).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.55  fof(f342,plain,(
% 0.20/0.55    ~r1_tarski(k1_xboole_0,k1_relat_1(sK3)) | (~spl4_5 | ~spl4_7 | spl4_11)),
% 0.20/0.55    inference(forward_demodulation,[],[f209,f303])).
% 0.20/0.55  fof(f209,plain,(
% 0.20/0.55    ~r1_tarski(sK2,k1_relat_1(sK3)) | spl4_11),
% 0.20/0.55    inference(subsumption_resolution,[],[f208,f140])).
% 0.20/0.55  fof(f140,plain,(
% 0.20/0.55    v1_relat_1(sK3)),
% 0.20/0.55    inference(subsumption_resolution,[],[f131,f68])).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.55  fof(f131,plain,(
% 0.20/0.55    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.55    inference(resolution,[],[f45,f69])).
% 0.20/0.55  fof(f69,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.55  fof(f208,plain,(
% 0.20/0.55    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl4_11),
% 0.20/0.55    inference(subsumption_resolution,[],[f207,f75])).
% 0.20/0.55  fof(f75,plain,(
% 0.20/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.55    inference(equality_resolution,[],[f57])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.55    inference(flattening,[],[f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.55    inference(nnf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.55  fof(f207,plain,(
% 0.20/0.55    ~r1_tarski(sK2,sK2) | ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl4_11),
% 0.20/0.55    inference(superposition,[],[f205,f71])).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(flattening,[],[f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.20/0.55  fof(f205,plain,(
% 0.20/0.55    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | spl4_11),
% 0.20/0.55    inference(avatar_component_clause,[],[f203])).
% 0.20/0.55  fof(f203,plain,(
% 0.20/0.55    spl4_11 <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.55  fof(f327,plain,(
% 0.20/0.55    ~spl4_5 | ~spl4_7 | spl4_12),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f326])).
% 0.20/0.55  fof(f326,plain,(
% 0.20/0.55    $false | (~spl4_5 | ~spl4_7 | spl4_12)),
% 0.20/0.55    inference(subsumption_resolution,[],[f309,f55])).
% 0.20/0.55  fof(f309,plain,(
% 0.20/0.55    ~r1_tarski(k1_xboole_0,k1_relat_1(sK3)) | (~spl4_5 | ~spl4_7 | spl4_12)),
% 0.20/0.55    inference(backward_demodulation,[],[f245,f303])).
% 0.20/0.55  fof(f245,plain,(
% 0.20/0.55    ~r1_tarski(sK2,k1_relat_1(sK3)) | spl4_12),
% 0.20/0.55    inference(subsumption_resolution,[],[f244,f140])).
% 0.20/0.55  fof(f244,plain,(
% 0.20/0.55    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl4_12),
% 0.20/0.55    inference(subsumption_resolution,[],[f243,f75])).
% 0.20/0.55  fof(f243,plain,(
% 0.20/0.55    ~r1_tarski(sK2,sK2) | ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl4_12),
% 0.20/0.55    inference(superposition,[],[f236,f71])).
% 0.20/0.55  fof(f236,plain,(
% 0.20/0.55    ~r1_tarski(sK2,k1_relat_1(k7_relat_1(sK3,sK2))) | spl4_12),
% 0.20/0.55    inference(avatar_component_clause,[],[f234])).
% 0.20/0.55  fof(f234,plain,(
% 0.20/0.55    spl4_12 <=> r1_tarski(sK2,k1_relat_1(k7_relat_1(sK3,sK2)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.55  fof(f283,plain,(
% 0.20/0.55    ~spl4_5 | spl4_6),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f282])).
% 0.20/0.55  fof(f282,plain,(
% 0.20/0.55    $false | (~spl4_5 | spl4_6)),
% 0.20/0.55    inference(subsumption_resolution,[],[f272,f55])).
% 0.20/0.55  fof(f272,plain,(
% 0.20/0.55    ~r1_tarski(k1_xboole_0,sK2) | (~spl4_5 | spl4_6)),
% 0.20/0.55    inference(backward_demodulation,[],[f113,f101])).
% 0.20/0.55  fof(f113,plain,(
% 0.20/0.55    ~r1_tarski(sK0,sK2) | spl4_6),
% 0.20/0.55    inference(avatar_component_clause,[],[f111])).
% 0.20/0.55  fof(f111,plain,(
% 0.20/0.55    spl4_6 <=> r1_tarski(sK0,sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.55  fof(f248,plain,(
% 0.20/0.55    spl4_4 | spl4_12),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f247])).
% 0.20/0.55  fof(f247,plain,(
% 0.20/0.55    $false | (spl4_4 | spl4_12)),
% 0.20/0.55    inference(subsumption_resolution,[],[f246,f46])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    r1_tarski(sK2,sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f37])).
% 0.20/0.55  fof(f246,plain,(
% 0.20/0.55    ~r1_tarski(sK2,sK0) | (spl4_4 | spl4_12)),
% 0.20/0.55    inference(forward_demodulation,[],[f245,f138])).
% 0.20/0.55  fof(f138,plain,(
% 0.20/0.55    sK0 = k1_relat_1(sK3) | spl4_4),
% 0.20/0.55    inference(forward_demodulation,[],[f129,f122])).
% 0.20/0.55  fof(f122,plain,(
% 0.20/0.55    sK0 = k1_relset_1(sK0,sK1,sK3) | spl4_4),
% 0.20/0.55    inference(subsumption_resolution,[],[f121,f45])).
% 0.20/0.55  fof(f121,plain,(
% 0.20/0.55    sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_4),
% 0.20/0.55    inference(subsumption_resolution,[],[f120,f97])).
% 0.20/0.55  fof(f120,plain,(
% 0.20/0.55    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.55    inference(resolution,[],[f44,f60])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f42])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f37])).
% 0.20/0.55  fof(f129,plain,(
% 0.20/0.55    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.20/0.55    inference(resolution,[],[f45,f67])).
% 0.20/0.55  fof(f242,plain,(
% 0.20/0.55    ~spl4_12 | spl4_13 | ~spl4_11),
% 0.20/0.55    inference(avatar_split_clause,[],[f230,f203,f238,f234])).
% 0.20/0.55  fof(f230,plain,(
% 0.20/0.55    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~r1_tarski(sK2,k1_relat_1(k7_relat_1(sK3,sK2))) | ~spl4_11),
% 0.20/0.55    inference(resolution,[],[f204,f59])).
% 0.20/0.55  fof(f59,plain,(
% 0.20/0.55    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f41])).
% 0.20/0.55  fof(f204,plain,(
% 0.20/0.55    r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | ~spl4_11),
% 0.20/0.55    inference(avatar_component_clause,[],[f203])).
% 0.20/0.55  fof(f212,plain,(
% 0.20/0.55    spl4_4 | spl4_11),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f211])).
% 0.20/0.55  fof(f211,plain,(
% 0.20/0.55    $false | (spl4_4 | spl4_11)),
% 0.20/0.55    inference(subsumption_resolution,[],[f210,f46])).
% 0.20/0.55  fof(f210,plain,(
% 0.20/0.55    ~r1_tarski(sK2,sK0) | (spl4_4 | spl4_11)),
% 0.20/0.55    inference(forward_demodulation,[],[f209,f138])).
% 0.20/0.55  fof(f206,plain,(
% 0.20/0.55    spl4_10 | ~spl4_11 | spl4_8),
% 0.20/0.55    inference(avatar_split_clause,[],[f197,f157,f203,f200])).
% 0.20/0.55  fof(f197,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | spl4_8),
% 0.20/0.55    inference(resolution,[],[f159,f70])).
% 0.20/0.55  fof(f70,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.20/0.55    inference(flattening,[],[f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.20/0.55    inference(ennf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 0.20/0.55  fof(f149,plain,(
% 0.20/0.55    spl4_1),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f145])).
% 0.20/0.55  fof(f145,plain,(
% 0.20/0.55    $false | spl4_1),
% 0.20/0.55    inference(resolution,[],[f137,f135])).
% 0.20/0.55  fof(f135,plain,(
% 0.20/0.55    ~v1_funct_1(k7_relat_1(sK3,sK2)) | spl4_1),
% 0.20/0.55    inference(backward_demodulation,[],[f84,f134])).
% 0.20/0.55  fof(f84,plain,(
% 0.20/0.55    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f82])).
% 0.20/0.55  fof(f82,plain,(
% 0.20/0.55    spl4_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.55  fof(f137,plain,(
% 0.20/0.55    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0))) )),
% 0.20/0.55    inference(backward_demodulation,[],[f132,f134])).
% 0.20/0.55  fof(f132,plain,(
% 0.20/0.55    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f123,f43])).
% 0.20/0.55  fof(f123,plain,(
% 0.20/0.55    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) | ~v1_funct_1(sK3)) )),
% 0.20/0.55    inference(resolution,[],[f45,f49])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f119,plain,(
% 0.20/0.55    ~spl4_6 | spl4_7),
% 0.20/0.55    inference(avatar_split_clause,[],[f108,f115,f111])).
% 0.20/0.55  fof(f108,plain,(
% 0.20/0.55    sK0 = sK2 | ~r1_tarski(sK0,sK2)),
% 0.20/0.55    inference(resolution,[],[f46,f59])).
% 0.20/0.55  fof(f102,plain,(
% 0.20/0.55    ~spl4_4 | spl4_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f47,f99,f95])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.20/0.55    inference(cnf_transformation,[],[f37])).
% 0.20/0.55  fof(f93,plain,(
% 0.20/0.55    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f48,f90,f86,f82])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.20/0.55    inference(cnf_transformation,[],[f37])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (31171)------------------------------
% 0.20/0.55  % (31171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (31171)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (31171)Memory used [KB]: 10874
% 0.20/0.55  % (31171)Time elapsed: 0.129 s
% 0.20/0.55  % (31171)------------------------------
% 0.20/0.55  % (31171)------------------------------
% 0.20/0.55  % (31182)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.56  % (31159)Success in time 0.192 s
%------------------------------------------------------------------------------
