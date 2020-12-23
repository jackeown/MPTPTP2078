%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 477 expanded)
%              Number of leaves         :   18 ( 128 expanded)
%              Depth                    :   19
%              Number of atoms          :  377 (2044 expanded)
%              Number of equality atoms :   85 ( 579 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f275,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f113,f137,f163,f173,f183,f184,f237,f248,f272])).

fof(f272,plain,
    ( spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f270,f238])).

fof(f238,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f220,f50])).

fof(f50,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f220,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(backward_demodulation,[],[f188,f216])).

fof(f216,plain,
    ( k1_xboole_0 = sK1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f209,f46])).

fof(f46,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
      | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
      | ~ v1_funct_1(sK1) )
    & r1_tarski(k2_relat_1(sK1),sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
        | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
        | ~ v1_funct_1(sK1) )
      & r1_tarski(k2_relat_1(sK1),sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f209,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_relat_1(sK1)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(trivial_inequality_removal,[],[f208])).

fof(f208,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | ~ v1_relat_1(sK1)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(superposition,[],[f54,f199])).

fof(f199,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f128,f186])).

fof(f186,plain,
    ( k1_xboole_0 = sK0
    | spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f185,f106])).

fof(f106,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl7_2
  <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f185,plain,
    ( k1_xboole_0 = sK0
    | v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f178,f179])).

fof(f179,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | ~ spl7_3 ),
    inference(resolution,[],[f109,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f109,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl7_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f178,plain,
    ( k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | k1_xboole_0 = sK0
    | v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ spl7_3 ),
    inference(resolution,[],[f109,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f128,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl7_5
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f188,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)
    | spl7_2
    | ~ spl7_3 ),
    inference(backward_demodulation,[],[f106,f186])).

fof(f270,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f269,f216])).

fof(f269,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f156,f186])).

fof(f156,plain,
    ( v1_funct_2(sK1,k1_xboole_0,sK0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl7_10
  <=> v1_funct_2(sK1,k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f248,plain,
    ( spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | spl7_9 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | spl7_9 ),
    inference(subsumption_resolution,[],[f224,f246])).

fof(f246,plain,
    ( ! [X2] : k1_xboole_0 = k1_relset_1(X2,k1_xboole_0,k1_xboole_0)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f245,f50])).

fof(f245,plain,
    ( ! [X2] : k1_relat_1(k1_xboole_0) = k1_relset_1(X2,k1_xboole_0,k1_xboole_0)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f244,f216])).

fof(f244,plain,
    ( ! [X2] : k1_relat_1(sK1) = k1_relset_1(X2,k1_xboole_0,sK1)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f243,f52])).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f243,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_xboole_0,X2)
        | k1_relat_1(sK1) = k1_relset_1(X2,k1_xboole_0,sK1) )
    | spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f223,f50])).

fof(f223,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_relat_1(k1_xboole_0),X2)
        | k1_relat_1(sK1) = k1_relset_1(X2,k1_xboole_0,sK1) )
    | spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(backward_demodulation,[],[f191,f216])).

fof(f191,plain,
    ( ! [X2] :
        ( k1_relat_1(sK1) = k1_relset_1(X2,k1_xboole_0,sK1)
        | ~ r1_tarski(k1_relat_1(sK1),X2) )
    | spl7_2
    | ~ spl7_3 ),
    inference(backward_demodulation,[],[f133,f186])).

fof(f133,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_relat_1(sK1),X2)
      | k1_relat_1(sK1) = k1_relset_1(X2,sK0,sK1) ) ),
    inference(resolution,[],[f120,f77])).

fof(f120,plain,(
    ! [X0] :
      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | ~ r1_tarski(k1_relat_1(sK1),X0) ) ),
    inference(subsumption_resolution,[],[f118,f46])).

fof(f118,plain,(
    ! [X0] :
      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
      | ~ r1_tarski(k1_relat_1(sK1),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f48,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f48,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f224,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | spl7_9 ),
    inference(backward_demodulation,[],[f194,f216])).

fof(f194,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | spl7_2
    | ~ spl7_3
    | spl7_9 ),
    inference(backward_demodulation,[],[f152,f186])).

fof(f152,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,sK1)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl7_9
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f237,plain,
    ( spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | spl7_11 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | spl7_11 ),
    inference(subsumption_resolution,[],[f235,f52])).

fof(f235,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | spl7_11 ),
    inference(forward_demodulation,[],[f219,f50])).

fof(f219,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | spl7_11 ),
    inference(backward_demodulation,[],[f161,f216])).

fof(f161,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_xboole_0)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl7_11
  <=> r1_tarski(k1_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f184,plain,
    ( ~ spl7_4
    | spl7_5 ),
    inference(avatar_split_clause,[],[f176,f126,f122])).

fof(f122,plain,
    ( spl7_4
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f176,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(resolution,[],[f48,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f183,plain,
    ( spl7_2
    | ~ spl7_3
    | spl7_6 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | spl7_2
    | ~ spl7_3
    | spl7_6 ),
    inference(subsumption_resolution,[],[f179,f181])).

fof(f181,plain,
    ( k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | spl7_2
    | ~ spl7_3
    | spl7_6 ),
    inference(subsumption_resolution,[],[f180,f106])).

fof(f180,plain,
    ( k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ spl7_3
    | spl7_6 ),
    inference(subsumption_resolution,[],[f178,f140])).

fof(f140,plain,
    ( k1_xboole_0 != sK0
    | spl7_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl7_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f173,plain,
    ( spl7_4
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f167,f52])).

fof(f167,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK1))
    | spl7_4
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f124,f141])).

fof(f141,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f124,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK1))
    | spl7_4 ),
    inference(avatar_component_clause,[],[f122])).

fof(f163,plain,
    ( spl7_10
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f135,f159,f151,f155])).

fof(f135,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_xboole_0)
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,sK1)
    | v1_funct_2(sK1,k1_xboole_0,sK0) ),
    inference(resolution,[],[f120,f97])).

fof(f97,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f137,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | spl7_3 ),
    inference(subsumption_resolution,[],[f130,f89])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f130,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | spl7_3 ),
    inference(resolution,[],[f120,f110])).

fof(f110,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f113,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl7_1 ),
    inference(subsumption_resolution,[],[f102,f47])).

fof(f47,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f102,plain,
    ( ~ v1_funct_1(sK1)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl7_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f111,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f49,f108,f104,f100])).

fof(f49,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:41:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.46  % (27057)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.46  % (27049)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.49  % (27048)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (27042)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (27035)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (27040)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (27042)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (27038)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (27058)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (27036)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f275,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f111,f113,f137,f163,f173,f183,f184,f237,f248,f272])).
% 0.21/0.52  fof(f272,plain,(
% 0.21/0.52    spl7_2 | ~spl7_3 | ~spl7_5 | ~spl7_10),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f271])).
% 0.21/0.52  fof(f271,plain,(
% 0.21/0.52    $false | (spl7_2 | ~spl7_3 | ~spl7_5 | ~spl7_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f270,f238])).
% 0.21/0.52  fof(f238,plain,(
% 0.21/0.52    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl7_2 | ~spl7_3 | ~spl7_5)),
% 0.21/0.52    inference(forward_demodulation,[],[f220,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.52  fof(f220,plain,(
% 0.21/0.52    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (spl7_2 | ~spl7_3 | ~spl7_5)),
% 0.21/0.52    inference(backward_demodulation,[],[f188,f216])).
% 0.21/0.52  fof(f216,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | (spl7_2 | ~spl7_3 | ~spl7_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f209,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    v1_relat_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.52    inference(negated_conjecture,[],[f12])).
% 0.21/0.52  fof(f12,conjecture,(
% 0.21/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~v1_relat_1(sK1) | (spl7_2 | ~spl7_3 | ~spl7_5)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f208])).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | ~v1_relat_1(sK1) | (spl7_2 | ~spl7_3 | ~spl7_5)),
% 0.21/0.52    inference(superposition,[],[f54,f199])).
% 0.21/0.52  fof(f199,plain,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(sK1) | (spl7_2 | ~spl7_3 | ~spl7_5)),
% 0.21/0.52    inference(forward_demodulation,[],[f128,f186])).
% 0.21/0.52  fof(f186,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | (spl7_2 | ~spl7_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f185,f106])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | spl7_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f104])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    spl7_2 <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~spl7_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f178,f179])).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) | ~spl7_3),
% 0.21/0.52    inference(resolution,[],[f109,f77])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~spl7_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f108])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    spl7_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1) | k1_xboole_0 = sK0 | v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~spl7_3),
% 0.21/0.52    inference(resolution,[],[f109,f80])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    sK0 = k2_relat_1(sK1) | ~spl7_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f126])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    spl7_5 <=> sK0 = k2_relat_1(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.52  fof(f188,plain,(
% 0.21/0.52    ~v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) | (spl7_2 | ~spl7_3)),
% 0.21/0.52    inference(backward_demodulation,[],[f106,f186])).
% 0.21/0.52  fof(f270,plain,(
% 0.21/0.52    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl7_2 | ~spl7_3 | ~spl7_5 | ~spl7_10)),
% 0.21/0.52    inference(forward_demodulation,[],[f269,f216])).
% 0.21/0.52  fof(f269,plain,(
% 0.21/0.52    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (spl7_2 | ~spl7_3 | ~spl7_10)),
% 0.21/0.52    inference(forward_demodulation,[],[f156,f186])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    v1_funct_2(sK1,k1_xboole_0,sK0) | ~spl7_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f155])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    spl7_10 <=> v1_funct_2(sK1,k1_xboole_0,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.52  fof(f248,plain,(
% 0.21/0.52    spl7_2 | ~spl7_3 | ~spl7_5 | spl7_9),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f247])).
% 0.21/0.52  fof(f247,plain,(
% 0.21/0.52    $false | (spl7_2 | ~spl7_3 | ~spl7_5 | spl7_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f224,f246])).
% 0.21/0.52  fof(f246,plain,(
% 0.21/0.52    ( ! [X2] : (k1_xboole_0 = k1_relset_1(X2,k1_xboole_0,k1_xboole_0)) ) | (spl7_2 | ~spl7_3 | ~spl7_5)),
% 0.21/0.52    inference(forward_demodulation,[],[f245,f50])).
% 0.21/0.52  fof(f245,plain,(
% 0.21/0.52    ( ! [X2] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X2,k1_xboole_0,k1_xboole_0)) ) | (spl7_2 | ~spl7_3 | ~spl7_5)),
% 0.21/0.52    inference(forward_demodulation,[],[f244,f216])).
% 0.21/0.52  fof(f244,plain,(
% 0.21/0.52    ( ! [X2] : (k1_relat_1(sK1) = k1_relset_1(X2,k1_xboole_0,sK1)) ) | (spl7_2 | ~spl7_3 | ~spl7_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f243,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.52  fof(f243,plain,(
% 0.21/0.52    ( ! [X2] : (~r1_tarski(k1_xboole_0,X2) | k1_relat_1(sK1) = k1_relset_1(X2,k1_xboole_0,sK1)) ) | (spl7_2 | ~spl7_3 | ~spl7_5)),
% 0.21/0.52    inference(forward_demodulation,[],[f223,f50])).
% 0.21/0.52  fof(f223,plain,(
% 0.21/0.52    ( ! [X2] : (~r1_tarski(k1_relat_1(k1_xboole_0),X2) | k1_relat_1(sK1) = k1_relset_1(X2,k1_xboole_0,sK1)) ) | (spl7_2 | ~spl7_3 | ~spl7_5)),
% 0.21/0.52    inference(backward_demodulation,[],[f191,f216])).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    ( ! [X2] : (k1_relat_1(sK1) = k1_relset_1(X2,k1_xboole_0,sK1) | ~r1_tarski(k1_relat_1(sK1),X2)) ) | (spl7_2 | ~spl7_3)),
% 0.21/0.52    inference(backward_demodulation,[],[f133,f186])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    ( ! [X2] : (~r1_tarski(k1_relat_1(sK1),X2) | k1_relat_1(sK1) = k1_relset_1(X2,sK0,sK1)) )),
% 0.21/0.52    inference(resolution,[],[f120,f77])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~r1_tarski(k1_relat_1(sK1),X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f118,f46])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~r1_tarski(k1_relat_1(sK1),X0) | ~v1_relat_1(sK1)) )),
% 0.21/0.52    inference(resolution,[],[f48,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    r1_tarski(k2_relat_1(sK1),sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f224,plain,(
% 0.21/0.52    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl7_2 | ~spl7_3 | ~spl7_5 | spl7_9)),
% 0.21/0.52    inference(backward_demodulation,[],[f194,f216])).
% 0.21/0.52  fof(f194,plain,(
% 0.21/0.52    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | (spl7_2 | ~spl7_3 | spl7_9)),
% 0.21/0.52    inference(backward_demodulation,[],[f152,f186])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,sK1) | spl7_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f151])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    spl7_9 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.52  fof(f237,plain,(
% 0.21/0.52    spl7_2 | ~spl7_3 | ~spl7_5 | spl7_11),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f236])).
% 0.21/0.52  fof(f236,plain,(
% 0.21/0.52    $false | (spl7_2 | ~spl7_3 | ~spl7_5 | spl7_11)),
% 0.21/0.52    inference(subsumption_resolution,[],[f235,f52])).
% 0.21/0.52  fof(f235,plain,(
% 0.21/0.52    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (spl7_2 | ~spl7_3 | ~spl7_5 | spl7_11)),
% 0.21/0.52    inference(forward_demodulation,[],[f219,f50])).
% 0.21/0.52  fof(f219,plain,(
% 0.21/0.52    ~r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) | (spl7_2 | ~spl7_3 | ~spl7_5 | spl7_11)),
% 0.21/0.52    inference(backward_demodulation,[],[f161,f216])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    ~r1_tarski(k1_relat_1(sK1),k1_xboole_0) | spl7_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f159])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    spl7_11 <=> r1_tarski(k1_relat_1(sK1),k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.52  fof(f184,plain,(
% 0.21/0.52    ~spl7_4 | spl7_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f176,f126,f122])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    spl7_4 <=> r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    sK0 = k2_relat_1(sK1) | ~r1_tarski(sK0,k2_relat_1(sK1))),
% 0.21/0.52    inference(resolution,[],[f48,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    spl7_2 | ~spl7_3 | spl7_6),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f182])).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    $false | (spl7_2 | ~spl7_3 | spl7_6)),
% 0.21/0.52    inference(subsumption_resolution,[],[f179,f181])).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1) | (spl7_2 | ~spl7_3 | spl7_6)),
% 0.21/0.52    inference(subsumption_resolution,[],[f180,f106])).
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1) | v1_funct_2(sK1,k1_relat_1(sK1),sK0) | (~spl7_3 | spl7_6)),
% 0.21/0.52    inference(subsumption_resolution,[],[f178,f140])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    k1_xboole_0 != sK0 | spl7_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f139])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    spl7_6 <=> k1_xboole_0 = sK0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    spl7_4 | ~spl7_6),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f172])).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    $false | (spl7_4 | ~spl7_6)),
% 0.21/0.52    inference(subsumption_resolution,[],[f167,f52])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    ~r1_tarski(k1_xboole_0,k2_relat_1(sK1)) | (spl7_4 | ~spl7_6)),
% 0.21/0.52    inference(backward_demodulation,[],[f124,f141])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | ~spl7_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f139])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    ~r1_tarski(sK0,k2_relat_1(sK1)) | spl7_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f122])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    spl7_10 | ~spl7_9 | ~spl7_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f135,f159,f151,f155])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    ~r1_tarski(k1_relat_1(sK1),k1_xboole_0) | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,sK1) | v1_funct_2(sK1,k1_xboole_0,sK0)),
% 0.21/0.52    inference(resolution,[],[f120,f97])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f45])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    spl7_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f136])).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    $false | spl7_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f130,f89])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f38])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | spl7_3),
% 0.21/0.52    inference(resolution,[],[f120,f110])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | spl7_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f108])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    spl7_1),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f112])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    $false | spl7_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f102,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    v1_funct_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    ~v1_funct_1(sK1) | spl7_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f100])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    spl7_1 <=> v1_funct_1(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    ~spl7_1 | ~spl7_2 | ~spl7_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f49,f108,f104,f100])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (27042)------------------------------
% 0.21/0.52  % (27042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (27042)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (27042)Memory used [KB]: 10746
% 0.21/0.52  % (27042)Time elapsed: 0.089 s
% 0.21/0.52  % (27042)------------------------------
% 0.21/0.52  % (27042)------------------------------
% 0.21/0.52  % (27047)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (27050)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (27033)Success in time 0.162 s
%------------------------------------------------------------------------------
