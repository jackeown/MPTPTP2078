%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:56 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 829 expanded)
%              Number of leaves         :   32 ( 261 expanded)
%              Depth                    :   22
%              Number of atoms          :  584 (5582 expanded)
%              Number of equality atoms :   79 ( 185 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f773,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f516,f529,f542,f624,f647,f653,f699,f772])).

fof(f772,plain,
    ( spl4_1
    | ~ spl4_12
    | ~ spl4_17 ),
    inference(avatar_contradiction_clause,[],[f771])).

fof(f771,plain,
    ( $false
    | spl4_1
    | ~ spl4_12
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f753,f117])).

fof(f117,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f96,f95])).

fof(f95,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f64,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f63,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f96,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f66,f64])).

fof(f66,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f753,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | spl4_1
    | ~ spl4_12
    | ~ spl4_17 ),
    inference(backward_demodulation,[],[f109,f743])).

fof(f743,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_12
    | ~ spl4_17 ),
    inference(resolution,[],[f737,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f737,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_12
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f736,f136])).

fof(f136,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f134,f76])).

fof(f76,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f134,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f74,f56])).

% (29092)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% (29094)Refutation not found, incomplete strategy% (29094)------------------------------
% (29094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29094)Termination reason: Refutation not found, incomplete strategy

% (29094)Memory used [KB]: 10874
% (29094)Time elapsed: 0.179 s
% (29094)------------------------------
% (29094)------------------------------
fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f46,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X3] :
        ( ( ~ v2_funct_2(X3,sK0)
          | ~ v2_funct_1(sK2) )
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ( ~ v2_funct_2(sK3,sK0)
        | ~ v2_funct_1(sK2) )
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f736,plain,
    ( ~ v1_relat_1(sK2)
    | v1_xboole_0(sK2)
    | ~ spl4_12
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f728,f62])).

fof(f62,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f728,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK2)
    | v1_xboole_0(sK2)
    | ~ spl4_12
    | ~ spl4_17 ),
    inference(superposition,[],[f75,f700])).

fof(f700,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_12
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f541,f497])).

fof(f497,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f495])).

fof(f495,plain,
    ( spl4_12
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f541,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f539])).

fof(f539,plain,
    ( spl4_17
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f109,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f699,plain,
    ( ~ spl4_12
    | spl4_16 ),
    inference(avatar_contradiction_clause,[],[f698])).

fof(f698,plain,
    ( $false
    | ~ spl4_12
    | spl4_16 ),
    inference(subsumption_resolution,[],[f697,f136])).

fof(f697,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl4_12
    | spl4_16 ),
    inference(subsumption_resolution,[],[f696,f560])).

fof(f560,plain,
    ( v4_relat_1(sK2,k1_xboole_0)
    | ~ spl4_12 ),
    inference(backward_demodulation,[],[f194,f497])).

fof(f194,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f86,f56])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f696,plain,
    ( ~ v4_relat_1(sK2,k1_xboole_0)
    | ~ v1_relat_1(sK2)
    | ~ spl4_12
    | spl4_16 ),
    inference(resolution,[],[f683,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f683,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_xboole_0)
    | ~ spl4_12
    | spl4_16 ),
    inference(forward_demodulation,[],[f537,f497])).

fof(f537,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f535])).

fof(f535,plain,
    ( spl4_16
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f653,plain,
    ( spl4_12
    | ~ spl4_13
    | spl4_1 ),
    inference(avatar_split_clause,[],[f493,f107,f499,f495])).

fof(f499,plain,
    ( spl4_13
  <=> v2_funct_1(k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f493,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | spl4_1 ),
    inference(subsumption_resolution,[],[f492,f54])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f492,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f491,f55])).

fof(f55,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f491,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f490,f56])).

fof(f490,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f489,f57])).

fof(f57,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f489,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f488,f58])).

fof(f58,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f488,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f487,f59])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f487,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f478,f109])).

fof(f478,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f88,f395])).

fof(f395,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f391,f54])).

fof(f391,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f291,f56])).

fof(f291,plain,(
    ! [X12,X10,X11] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | k1_partfun1(X10,X11,sK1,sK0,X12,sK3) = k5_relat_1(X12,sK3)
      | ~ v1_funct_1(X12) ) ),
    inference(subsumption_resolution,[],[f281,f57])).

fof(f281,plain,(
    ! [X12,X10,X11] :
      ( k1_partfun1(X10,X11,sK1,sK0,X12,sK3) = k5_relat_1(X12,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ v1_funct_1(X12) ) ),
    inference(resolution,[],[f92,f59])).

fof(f92,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

fof(f647,plain,
    ( spl4_2
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f646])).

fof(f646,plain,
    ( $false
    | spl4_2
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f645,f137])).

fof(f137,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f135,f76])).

fof(f135,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f74,f59])).

fof(f645,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_2
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f638,f113])).

fof(f113,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl4_2
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f638,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_15 ),
    inference(superposition,[],[f214,f528])).

fof(f528,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f526])).

fof(f526,plain,
    ( spl4_15
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f214,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f100,f172])).

fof(f172,plain,(
    ! [X2] :
      ( v5_relat_1(X2,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f80,f101])).

fof(f101,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f100,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f624,plain,(
    spl4_14 ),
    inference(avatar_contradiction_clause,[],[f623])).

fof(f623,plain,
    ( $false
    | spl4_14 ),
    inference(subsumption_resolution,[],[f622,f137])).

fof(f622,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_14 ),
    inference(subsumption_resolution,[],[f621,f201])).

fof(f201,plain,(
    v5_relat_1(sK3,sK0) ),
    inference(resolution,[],[f87,f59])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f621,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | spl4_14 ),
    inference(resolution,[],[f524,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f524,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f522])).

fof(f522,plain,
    ( spl4_14
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f542,plain,
    ( ~ spl4_16
    | spl4_17 ),
    inference(avatar_split_clause,[],[f533,f539,f535])).

fof(f533,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(forward_demodulation,[],[f532,f99])).

fof(f99,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f69,f64])).

fof(f69,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f532,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f531,f99])).

fof(f531,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0)))
    | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f530,f137])).

fof(f530,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0)))
    | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f510,f136])).

fof(f510,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0)))
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f227,f504])).

fof(f504,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f482,f503])).

fof(f503,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f475,f258])).

fof(f258,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X1,X1,X2,k6_partfun1(X1))
      | k6_partfun1(X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    inference(resolution,[],[f90,f68])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f475,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f60,f395])).

fof(f60,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f482,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f481,f54])).

fof(f481,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f480,f56])).

fof(f480,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f479,f57])).

fof(f479,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f476,f59])).

fof(f476,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f94,f395])).

fof(f94,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f227,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_relat_1(X3),k1_relat_1(k5_relat_1(X3,X2)))
      | ~ v1_relat_1(X3)
      | k1_relat_1(X3) = k1_relat_1(k5_relat_1(X3,X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f72,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f529,plain,
    ( ~ spl4_14
    | spl4_15 ),
    inference(avatar_split_clause,[],[f520,f526,f522])).

fof(f520,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),sK0) ),
    inference(forward_demodulation,[],[f519,f98])).

fof(f98,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f70,f64])).

fof(f70,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f519,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f518,f98])).

fof(f518,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0)))
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f517,f137])).

fof(f517,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0)))
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f509,f136])).

fof(f509,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f238,f504])).

fof(f238,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k2_relat_1(X2),k2_relat_1(k5_relat_1(X3,X2)))
      | ~ v1_relat_1(X3)
      | k2_relat_1(X2) = k2_relat_1(k5_relat_1(X3,X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f73,f85])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f516,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f515])).

fof(f515,plain,
    ( $false
    | spl4_13 ),
    inference(subsumption_resolution,[],[f505,f96])).

fof(f505,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_13 ),
    inference(backward_demodulation,[],[f501,f504])).

fof(f501,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f499])).

fof(f114,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f61,f111,f107])).

fof(f61,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:39:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.50  % (29066)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.50  % (29074)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (29089)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (29080)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (29067)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (29073)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (29070)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (29071)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (29072)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (29081)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (29095)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (29090)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (29068)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (29087)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (29069)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (29091)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (29076)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (29077)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (29086)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (29076)Refutation not found, incomplete strategy% (29076)------------------------------
% 0.21/0.54  % (29076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29076)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29076)Memory used [KB]: 10874
% 0.21/0.54  % (29076)Time elapsed: 0.135 s
% 0.21/0.54  % (29076)------------------------------
% 0.21/0.54  % (29076)------------------------------
% 0.21/0.54  % (29088)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (29082)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (29078)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (29094)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (29083)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (29093)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (29075)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (29085)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (29084)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (29079)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (29082)Refutation not found, incomplete strategy% (29082)------------------------------
% 0.21/0.56  % (29082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (29082)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (29082)Memory used [KB]: 10746
% 0.21/0.56  % (29082)Time elapsed: 0.158 s
% 0.21/0.56  % (29082)------------------------------
% 0.21/0.56  % (29082)------------------------------
% 1.56/0.57  % (29072)Refutation found. Thanks to Tanya!
% 1.56/0.57  % SZS status Theorem for theBenchmark
% 1.56/0.57  % SZS output start Proof for theBenchmark
% 1.56/0.57  fof(f773,plain,(
% 1.56/0.57    $false),
% 1.56/0.57    inference(avatar_sat_refutation,[],[f114,f516,f529,f542,f624,f647,f653,f699,f772])).
% 1.56/0.57  fof(f772,plain,(
% 1.56/0.57    spl4_1 | ~spl4_12 | ~spl4_17),
% 1.56/0.57    inference(avatar_contradiction_clause,[],[f771])).
% 1.56/0.57  fof(f771,plain,(
% 1.56/0.57    $false | (spl4_1 | ~spl4_12 | ~spl4_17)),
% 1.56/0.57    inference(subsumption_resolution,[],[f753,f117])).
% 1.56/0.57  fof(f117,plain,(
% 1.56/0.57    v2_funct_1(k1_xboole_0)),
% 1.56/0.57    inference(superposition,[],[f96,f95])).
% 1.56/0.57  fof(f95,plain,(
% 1.56/0.57    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.56/0.57    inference(definition_unfolding,[],[f63,f64])).
% 1.56/0.57  fof(f64,plain,(
% 1.56/0.57    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f20])).
% 1.56/0.57  fof(f20,axiom,(
% 1.56/0.57    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.56/0.57  fof(f63,plain,(
% 1.56/0.57    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.56/0.57    inference(cnf_transformation,[],[f12])).
% 1.56/0.57  fof(f12,axiom,(
% 1.56/0.57    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 1.56/0.57  fof(f96,plain,(
% 1.56/0.57    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.56/0.57    inference(definition_unfolding,[],[f66,f64])).
% 1.56/0.57  fof(f66,plain,(
% 1.56/0.57    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.56/0.57    inference(cnf_transformation,[],[f13])).
% 1.56/0.57  fof(f13,axiom,(
% 1.56/0.57    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.56/0.57  fof(f753,plain,(
% 1.56/0.57    ~v2_funct_1(k1_xboole_0) | (spl4_1 | ~spl4_12 | ~spl4_17)),
% 1.56/0.57    inference(backward_demodulation,[],[f109,f743])).
% 1.56/0.57  fof(f743,plain,(
% 1.56/0.57    k1_xboole_0 = sK2 | (~spl4_12 | ~spl4_17)),
% 1.56/0.57    inference(resolution,[],[f737,f71])).
% 1.56/0.57  fof(f71,plain,(
% 1.56/0.57    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.56/0.57    inference(cnf_transformation,[],[f26])).
% 1.56/0.57  fof(f26,plain,(
% 1.56/0.57    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.56/0.57    inference(ennf_transformation,[],[f2])).
% 1.56/0.57  fof(f2,axiom,(
% 1.56/0.57    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.56/0.57  fof(f737,plain,(
% 1.56/0.57    v1_xboole_0(sK2) | (~spl4_12 | ~spl4_17)),
% 1.56/0.57    inference(subsumption_resolution,[],[f736,f136])).
% 1.56/0.57  fof(f136,plain,(
% 1.56/0.57    v1_relat_1(sK2)),
% 1.56/0.57    inference(subsumption_resolution,[],[f134,f76])).
% 1.56/0.57  fof(f76,plain,(
% 1.56/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.56/0.57    inference(cnf_transformation,[],[f7])).
% 1.56/0.57  fof(f7,axiom,(
% 1.56/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.56/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.56/0.57  fof(f134,plain,(
% 1.56/0.57    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.56/0.57    inference(resolution,[],[f74,f56])).
% 1.56/0.58  % (29092)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.56/0.58  % (29094)Refutation not found, incomplete strategy% (29094)------------------------------
% 1.56/0.58  % (29094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % (29094)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.58  
% 1.56/0.58  % (29094)Memory used [KB]: 10874
% 1.56/0.58  % (29094)Time elapsed: 0.179 s
% 1.56/0.58  % (29094)------------------------------
% 1.56/0.58  % (29094)------------------------------
% 1.56/0.58  fof(f56,plain,(
% 1.56/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.56/0.58    inference(cnf_transformation,[],[f47])).
% 1.56/0.58  fof(f47,plain,(
% 1.56/0.58    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.56/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f46,f45])).
% 1.56/0.58  fof(f45,plain,(
% 1.56/0.58    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.56/0.58    introduced(choice_axiom,[])).
% 1.56/0.58  fof(f46,plain,(
% 1.56/0.58    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.56/0.58    introduced(choice_axiom,[])).
% 1.56/0.58  fof(f25,plain,(
% 1.56/0.58    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.56/0.58    inference(flattening,[],[f24])).
% 1.56/0.58  fof(f24,plain,(
% 1.56/0.58    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.56/0.58    inference(ennf_transformation,[],[f23])).
% 1.56/0.58  fof(f23,negated_conjecture,(
% 1.56/0.58    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.56/0.58    inference(negated_conjecture,[],[f22])).
% 1.56/0.58  fof(f22,conjecture,(
% 1.56/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.56/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 1.56/0.58  fof(f74,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f29])).
% 1.56/0.58  fof(f29,plain,(
% 1.56/0.58    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.56/0.58    inference(ennf_transformation,[],[f4])).
% 1.56/0.58  fof(f4,axiom,(
% 1.56/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.56/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.56/0.58  fof(f736,plain,(
% 1.56/0.58    ~v1_relat_1(sK2) | v1_xboole_0(sK2) | (~spl4_12 | ~spl4_17)),
% 1.56/0.58    inference(subsumption_resolution,[],[f728,f62])).
% 1.56/0.58  fof(f62,plain,(
% 1.56/0.58    v1_xboole_0(k1_xboole_0)),
% 1.56/0.58    inference(cnf_transformation,[],[f1])).
% 1.56/0.58  fof(f1,axiom,(
% 1.56/0.58    v1_xboole_0(k1_xboole_0)),
% 1.56/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.56/0.58  fof(f728,plain,(
% 1.56/0.58    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(sK2) | v1_xboole_0(sK2) | (~spl4_12 | ~spl4_17)),
% 1.56/0.58    inference(superposition,[],[f75,f700])).
% 1.56/0.58  fof(f700,plain,(
% 1.56/0.58    k1_xboole_0 = k1_relat_1(sK2) | (~spl4_12 | ~spl4_17)),
% 1.56/0.58    inference(forward_demodulation,[],[f541,f497])).
% 1.56/0.58  fof(f497,plain,(
% 1.56/0.58    k1_xboole_0 = sK0 | ~spl4_12),
% 1.56/0.58    inference(avatar_component_clause,[],[f495])).
% 1.56/0.58  fof(f495,plain,(
% 1.56/0.58    spl4_12 <=> k1_xboole_0 = sK0),
% 1.56/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.56/0.58  fof(f541,plain,(
% 1.56/0.58    sK0 = k1_relat_1(sK2) | ~spl4_17),
% 1.56/0.58    inference(avatar_component_clause,[],[f539])).
% 1.56/0.58  fof(f539,plain,(
% 1.56/0.58    spl4_17 <=> sK0 = k1_relat_1(sK2)),
% 1.56/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.56/0.58  fof(f75,plain,(
% 1.56/0.58    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f31])).
% 1.56/0.58  fof(f31,plain,(
% 1.56/0.58    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 1.56/0.58    inference(flattening,[],[f30])).
% 1.56/0.58  fof(f30,plain,(
% 1.56/0.58    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 1.56/0.58    inference(ennf_transformation,[],[f8])).
% 1.56/0.58  fof(f8,axiom,(
% 1.56/0.58    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 1.56/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).
% 1.56/0.58  fof(f109,plain,(
% 1.56/0.58    ~v2_funct_1(sK2) | spl4_1),
% 1.56/0.58    inference(avatar_component_clause,[],[f107])).
% 1.56/0.58  fof(f107,plain,(
% 1.56/0.58    spl4_1 <=> v2_funct_1(sK2)),
% 1.56/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.56/0.58  fof(f699,plain,(
% 1.56/0.58    ~spl4_12 | spl4_16),
% 1.56/0.58    inference(avatar_contradiction_clause,[],[f698])).
% 1.56/0.58  fof(f698,plain,(
% 1.56/0.58    $false | (~spl4_12 | spl4_16)),
% 1.56/0.58    inference(subsumption_resolution,[],[f697,f136])).
% 1.56/0.58  fof(f697,plain,(
% 1.56/0.58    ~v1_relat_1(sK2) | (~spl4_12 | spl4_16)),
% 1.56/0.58    inference(subsumption_resolution,[],[f696,f560])).
% 1.56/0.58  fof(f560,plain,(
% 1.56/0.58    v4_relat_1(sK2,k1_xboole_0) | ~spl4_12),
% 1.56/0.58    inference(backward_demodulation,[],[f194,f497])).
% 1.56/0.58  fof(f194,plain,(
% 1.56/0.58    v4_relat_1(sK2,sK0)),
% 1.56/0.58    inference(resolution,[],[f86,f56])).
% 1.56/0.58  fof(f86,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f36])).
% 1.56/0.58  fof(f36,plain,(
% 1.56/0.58    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/0.58    inference(ennf_transformation,[],[f14])).
% 1.56/0.58  fof(f14,axiom,(
% 1.56/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.56/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.56/0.58  fof(f696,plain,(
% 1.56/0.58    ~v4_relat_1(sK2,k1_xboole_0) | ~v1_relat_1(sK2) | (~spl4_12 | spl4_16)),
% 1.56/0.58    inference(resolution,[],[f683,f77])).
% 1.56/0.58  fof(f77,plain,(
% 1.56/0.58    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f48])).
% 1.56/0.58  fof(f48,plain,(
% 1.56/0.58    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.56/0.58    inference(nnf_transformation,[],[f32])).
% 1.56/0.58  fof(f32,plain,(
% 1.56/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.56/0.58    inference(ennf_transformation,[],[f5])).
% 1.56/0.58  fof(f5,axiom,(
% 1.56/0.58    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.56/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.56/0.58  fof(f683,plain,(
% 1.56/0.58    ~r1_tarski(k1_relat_1(sK2),k1_xboole_0) | (~spl4_12 | spl4_16)),
% 1.56/0.58    inference(forward_demodulation,[],[f537,f497])).
% 1.56/0.58  fof(f537,plain,(
% 1.56/0.58    ~r1_tarski(k1_relat_1(sK2),sK0) | spl4_16),
% 1.56/0.58    inference(avatar_component_clause,[],[f535])).
% 1.56/0.58  fof(f535,plain,(
% 1.56/0.58    spl4_16 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 1.56/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.56/0.58  fof(f653,plain,(
% 1.56/0.58    spl4_12 | ~spl4_13 | spl4_1),
% 1.56/0.58    inference(avatar_split_clause,[],[f493,f107,f499,f495])).
% 1.56/0.58  fof(f499,plain,(
% 1.56/0.58    spl4_13 <=> v2_funct_1(k5_relat_1(sK2,sK3))),
% 1.56/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.56/0.58  fof(f493,plain,(
% 1.56/0.58    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | spl4_1),
% 1.56/0.58    inference(subsumption_resolution,[],[f492,f54])).
% 1.56/0.58  fof(f54,plain,(
% 1.56/0.58    v1_funct_1(sK2)),
% 1.56/0.58    inference(cnf_transformation,[],[f47])).
% 1.56/0.58  fof(f492,plain,(
% 1.56/0.58    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_1(sK2) | spl4_1),
% 1.56/0.58    inference(subsumption_resolution,[],[f491,f55])).
% 1.56/0.58  fof(f55,plain,(
% 1.56/0.58    v1_funct_2(sK2,sK0,sK1)),
% 1.56/0.58    inference(cnf_transformation,[],[f47])).
% 1.56/0.58  fof(f491,plain,(
% 1.56/0.58    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 1.56/0.58    inference(subsumption_resolution,[],[f490,f56])).
% 1.56/0.58  fof(f490,plain,(
% 1.56/0.58    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 1.56/0.58    inference(subsumption_resolution,[],[f489,f57])).
% 1.56/0.58  fof(f57,plain,(
% 1.56/0.58    v1_funct_1(sK3)),
% 1.56/0.58    inference(cnf_transformation,[],[f47])).
% 1.56/0.58  fof(f489,plain,(
% 1.56/0.58    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 1.56/0.58    inference(subsumption_resolution,[],[f488,f58])).
% 1.56/0.58  fof(f58,plain,(
% 1.56/0.58    v1_funct_2(sK3,sK1,sK0)),
% 1.56/0.58    inference(cnf_transformation,[],[f47])).
% 1.56/0.58  fof(f488,plain,(
% 1.56/0.58    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 1.56/0.58    inference(subsumption_resolution,[],[f487,f59])).
% 1.56/0.58  fof(f59,plain,(
% 1.56/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.56/0.58    inference(cnf_transformation,[],[f47])).
% 1.56/0.58  fof(f487,plain,(
% 1.56/0.58    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 1.56/0.58    inference(subsumption_resolution,[],[f478,f109])).
% 1.56/0.58  fof(f478,plain,(
% 1.56/0.58    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.56/0.58    inference(superposition,[],[f88,f395])).
% 1.56/0.58  fof(f395,plain,(
% 1.56/0.58    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.56/0.58    inference(subsumption_resolution,[],[f391,f54])).
% 1.56/0.58  fof(f391,plain,(
% 1.56/0.58    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2)),
% 1.56/0.58    inference(resolution,[],[f291,f56])).
% 1.56/0.58  fof(f291,plain,(
% 1.56/0.58    ( ! [X12,X10,X11] : (~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | k1_partfun1(X10,X11,sK1,sK0,X12,sK3) = k5_relat_1(X12,sK3) | ~v1_funct_1(X12)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f281,f57])).
% 1.56/0.58  fof(f281,plain,(
% 1.56/0.58    ( ! [X12,X10,X11] : (k1_partfun1(X10,X11,sK1,sK0,X12,sK3) = k5_relat_1(X12,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | ~v1_funct_1(X12)) )),
% 1.56/0.58    inference(resolution,[],[f92,f59])).
% 1.56/0.58  fof(f92,plain,(
% 1.56/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f42])).
% 1.56/0.58  fof(f42,plain,(
% 1.56/0.58    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.56/0.58    inference(flattening,[],[f41])).
% 1.56/0.58  fof(f41,plain,(
% 1.56/0.58    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.56/0.58    inference(ennf_transformation,[],[f19])).
% 1.56/0.58  fof(f19,axiom,(
% 1.56/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.56/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.56/0.58  fof(f88,plain,(
% 1.56/0.58    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f38])).
% 1.56/0.58  fof(f38,plain,(
% 1.56/0.58    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.56/0.58    inference(flattening,[],[f37])).
% 1.56/0.58  fof(f37,plain,(
% 1.56/0.58    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.56/0.58    inference(ennf_transformation,[],[f21])).
% 1.56/0.58  fof(f21,axiom,(
% 1.56/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.56/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).
% 1.56/0.58  fof(f647,plain,(
% 1.56/0.58    spl4_2 | ~spl4_15),
% 1.56/0.58    inference(avatar_contradiction_clause,[],[f646])).
% 1.56/0.58  fof(f646,plain,(
% 1.56/0.58    $false | (spl4_2 | ~spl4_15)),
% 1.56/0.58    inference(subsumption_resolution,[],[f645,f137])).
% 1.56/0.58  fof(f137,plain,(
% 1.56/0.58    v1_relat_1(sK3)),
% 1.56/0.58    inference(subsumption_resolution,[],[f135,f76])).
% 1.56/0.58  fof(f135,plain,(
% 1.56/0.58    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 1.56/0.58    inference(resolution,[],[f74,f59])).
% 1.56/0.58  fof(f645,plain,(
% 1.56/0.58    ~v1_relat_1(sK3) | (spl4_2 | ~spl4_15)),
% 1.56/0.58    inference(subsumption_resolution,[],[f638,f113])).
% 1.56/0.58  fof(f113,plain,(
% 1.56/0.58    ~v2_funct_2(sK3,sK0) | spl4_2),
% 1.56/0.58    inference(avatar_component_clause,[],[f111])).
% 1.56/0.58  fof(f111,plain,(
% 1.56/0.58    spl4_2 <=> v2_funct_2(sK3,sK0)),
% 1.56/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.56/0.58  fof(f638,plain,(
% 1.56/0.58    v2_funct_2(sK3,sK0) | ~v1_relat_1(sK3) | ~spl4_15),
% 1.56/0.58    inference(superposition,[],[f214,f528])).
% 1.56/0.58  fof(f528,plain,(
% 1.56/0.58    sK0 = k2_relat_1(sK3) | ~spl4_15),
% 1.56/0.58    inference(avatar_component_clause,[],[f526])).
% 1.56/0.58  fof(f526,plain,(
% 1.56/0.58    spl4_15 <=> sK0 = k2_relat_1(sK3)),
% 1.56/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.56/0.58  fof(f214,plain,(
% 1.56/0.58    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f100,f172])).
% 1.56/0.58  fof(f172,plain,(
% 1.56/0.58    ( ! [X2] : (v5_relat_1(X2,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.56/0.58    inference(resolution,[],[f80,f101])).
% 1.56/0.58  fof(f101,plain,(
% 1.56/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.56/0.58    inference(equality_resolution,[],[f84])).
% 1.56/0.58  fof(f84,plain,(
% 1.56/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.56/0.58    inference(cnf_transformation,[],[f52])).
% 1.56/0.58  fof(f52,plain,(
% 1.56/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.58    inference(flattening,[],[f51])).
% 1.56/0.58  fof(f51,plain,(
% 1.56/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.58    inference(nnf_transformation,[],[f3])).
% 1.56/0.58  fof(f3,axiom,(
% 1.56/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.56/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.56/0.58  fof(f80,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f49])).
% 1.56/0.58  fof(f49,plain,(
% 1.56/0.58    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.56/0.58    inference(nnf_transformation,[],[f33])).
% 1.56/0.58  fof(f33,plain,(
% 1.56/0.58    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.56/0.58    inference(ennf_transformation,[],[f6])).
% 1.56/0.58  fof(f6,axiom,(
% 1.56/0.58    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.56/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.56/0.58  fof(f100,plain,(
% 1.56/0.58    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.56/0.58    inference(equality_resolution,[],[f82])).
% 1.56/0.58  fof(f82,plain,(
% 1.56/0.58    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f50])).
% 1.56/0.58  fof(f50,plain,(
% 1.56/0.58    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.56/0.58    inference(nnf_transformation,[],[f35])).
% 1.56/0.58  fof(f35,plain,(
% 1.56/0.58    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.56/0.58    inference(flattening,[],[f34])).
% 1.56/0.58  fof(f34,plain,(
% 1.56/0.58    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.56/0.58    inference(ennf_transformation,[],[f16])).
% 1.56/0.58  fof(f16,axiom,(
% 1.56/0.58    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.56/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.56/0.58  fof(f624,plain,(
% 1.56/0.58    spl4_14),
% 1.56/0.58    inference(avatar_contradiction_clause,[],[f623])).
% 1.56/0.58  fof(f623,plain,(
% 1.56/0.58    $false | spl4_14),
% 1.56/0.58    inference(subsumption_resolution,[],[f622,f137])).
% 1.56/0.58  fof(f622,plain,(
% 1.56/0.58    ~v1_relat_1(sK3) | spl4_14),
% 1.56/0.58    inference(subsumption_resolution,[],[f621,f201])).
% 1.56/0.58  fof(f201,plain,(
% 1.56/0.58    v5_relat_1(sK3,sK0)),
% 1.56/0.58    inference(resolution,[],[f87,f59])).
% 1.56/0.58  fof(f87,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f36])).
% 1.56/0.58  fof(f621,plain,(
% 1.56/0.58    ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | spl4_14),
% 1.56/0.58    inference(resolution,[],[f524,f79])).
% 1.56/0.58  fof(f79,plain,(
% 1.56/0.58    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f49])).
% 1.56/0.58  fof(f524,plain,(
% 1.56/0.58    ~r1_tarski(k2_relat_1(sK3),sK0) | spl4_14),
% 1.56/0.58    inference(avatar_component_clause,[],[f522])).
% 1.56/0.58  fof(f522,plain,(
% 1.56/0.58    spl4_14 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 1.56/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.56/0.58  fof(f542,plain,(
% 1.56/0.58    ~spl4_16 | spl4_17),
% 1.56/0.58    inference(avatar_split_clause,[],[f533,f539,f535])).
% 1.56/0.58  fof(f533,plain,(
% 1.56/0.58    sK0 = k1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),sK0)),
% 1.56/0.58    inference(forward_demodulation,[],[f532,f99])).
% 1.56/0.58  fof(f99,plain,(
% 1.56/0.58    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.56/0.58    inference(definition_unfolding,[],[f69,f64])).
% 1.56/0.58  fof(f69,plain,(
% 1.56/0.58    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.56/0.58    inference(cnf_transformation,[],[f11])).
% 1.56/0.58  fof(f11,axiom,(
% 1.56/0.58    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.56/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.56/0.58  fof(f532,plain,(
% 1.56/0.58    ~r1_tarski(k1_relat_1(sK2),sK0) | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))),
% 1.56/0.58    inference(forward_demodulation,[],[f531,f99])).
% 1.56/0.58  fof(f531,plain,(
% 1.56/0.58    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0))) | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))),
% 1.56/0.58    inference(subsumption_resolution,[],[f530,f137])).
% 1.56/0.58  fof(f530,plain,(
% 1.56/0.58    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0))) | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(sK3)),
% 1.56/0.58    inference(subsumption_resolution,[],[f510,f136])).
% 1.56/0.58  fof(f510,plain,(
% 1.56/0.58    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0))) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(sK3)),
% 1.56/0.58    inference(superposition,[],[f227,f504])).
% 1.56/0.58  fof(f504,plain,(
% 1.56/0.58    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.56/0.58    inference(global_subsumption,[],[f482,f503])).
% 1.56/0.58  fof(f503,plain,(
% 1.56/0.58    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.56/0.58    inference(resolution,[],[f475,f258])).
% 1.56/0.58  fof(f258,plain,(
% 1.56/0.58    ( ! [X2,X1] : (~r2_relset_1(X1,X1,X2,k6_partfun1(X1)) | k6_partfun1(X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))) )),
% 1.56/0.58    inference(resolution,[],[f90,f68])).
% 1.56/0.58  fof(f68,plain,(
% 1.56/0.58    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.56/0.58    inference(cnf_transformation,[],[f18])).
% 1.56/0.58  fof(f18,axiom,(
% 1.56/0.58    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.56/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.56/0.58  fof(f90,plain,(
% 1.56/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.56/0.58    inference(cnf_transformation,[],[f53])).
% 1.56/0.58  fof(f53,plain,(
% 1.56/0.58    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/0.58    inference(nnf_transformation,[],[f40])).
% 1.56/0.58  fof(f40,plain,(
% 1.56/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/0.58    inference(flattening,[],[f39])).
% 1.56/0.58  fof(f39,plain,(
% 1.56/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.56/0.58    inference(ennf_transformation,[],[f15])).
% 1.56/0.58  fof(f15,axiom,(
% 1.56/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.56/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.56/0.58  fof(f475,plain,(
% 1.56/0.58    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 1.56/0.58    inference(backward_demodulation,[],[f60,f395])).
% 1.56/0.58  fof(f60,plain,(
% 1.56/0.58    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.56/0.58    inference(cnf_transformation,[],[f47])).
% 1.56/0.58  fof(f482,plain,(
% 1.56/0.58    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.56/0.58    inference(subsumption_resolution,[],[f481,f54])).
% 1.56/0.58  fof(f481,plain,(
% 1.56/0.58    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 1.56/0.58    inference(subsumption_resolution,[],[f480,f56])).
% 1.56/0.58  fof(f480,plain,(
% 1.56/0.58    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.56/0.58    inference(subsumption_resolution,[],[f479,f57])).
% 1.56/0.58  fof(f479,plain,(
% 1.56/0.58    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.56/0.58    inference(subsumption_resolution,[],[f476,f59])).
% 1.56/0.58  fof(f476,plain,(
% 1.56/0.58    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.56/0.58    inference(superposition,[],[f94,f395])).
% 1.56/0.58  fof(f94,plain,(
% 1.56/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f44])).
% 1.56/0.58  fof(f44,plain,(
% 1.56/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.56/0.58    inference(flattening,[],[f43])).
% 1.56/0.58  fof(f43,plain,(
% 1.56/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.56/0.58    inference(ennf_transformation,[],[f17])).
% 1.56/0.58  fof(f17,axiom,(
% 1.56/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.56/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.56/0.58  fof(f227,plain,(
% 1.56/0.58    ( ! [X2,X3] : (~r1_tarski(k1_relat_1(X3),k1_relat_1(k5_relat_1(X3,X2))) | ~v1_relat_1(X3) | k1_relat_1(X3) = k1_relat_1(k5_relat_1(X3,X2)) | ~v1_relat_1(X2)) )),
% 1.56/0.58    inference(resolution,[],[f72,f85])).
% 1.56/0.58  fof(f85,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f52])).
% 1.56/0.58  fof(f72,plain,(
% 1.56/0.58    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f27])).
% 1.56/0.58  fof(f27,plain,(
% 1.56/0.58    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.56/0.58    inference(ennf_transformation,[],[f9])).
% 1.56/0.58  fof(f9,axiom,(
% 1.56/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 1.56/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 1.56/0.58  fof(f529,plain,(
% 1.56/0.58    ~spl4_14 | spl4_15),
% 1.56/0.58    inference(avatar_split_clause,[],[f520,f526,f522])).
% 1.56/0.58  fof(f520,plain,(
% 1.56/0.58    sK0 = k2_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),sK0)),
% 1.56/0.58    inference(forward_demodulation,[],[f519,f98])).
% 1.56/0.58  fof(f98,plain,(
% 1.56/0.58    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.56/0.58    inference(definition_unfolding,[],[f70,f64])).
% 1.56/0.58  fof(f70,plain,(
% 1.56/0.58    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.56/0.58    inference(cnf_transformation,[],[f11])).
% 1.56/0.58  fof(f519,plain,(
% 1.56/0.58    ~r1_tarski(k2_relat_1(sK3),sK0) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))),
% 1.56/0.58    inference(forward_demodulation,[],[f518,f98])).
% 1.56/0.58  fof(f518,plain,(
% 1.56/0.58    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0))) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))),
% 1.56/0.58    inference(subsumption_resolution,[],[f517,f137])).
% 1.56/0.58  fof(f517,plain,(
% 1.56/0.58    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0))) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(sK3)),
% 1.56/0.58    inference(subsumption_resolution,[],[f509,f136])).
% 1.56/0.58  fof(f509,plain,(
% 1.56/0.58    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0))) | ~v1_relat_1(sK2) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(sK3)),
% 1.56/0.58    inference(superposition,[],[f238,f504])).
% 1.56/0.58  fof(f238,plain,(
% 1.56/0.58    ( ! [X2,X3] : (~r1_tarski(k2_relat_1(X2),k2_relat_1(k5_relat_1(X3,X2))) | ~v1_relat_1(X3) | k2_relat_1(X2) = k2_relat_1(k5_relat_1(X3,X2)) | ~v1_relat_1(X2)) )),
% 1.56/0.58    inference(resolution,[],[f73,f85])).
% 1.56/0.58  fof(f73,plain,(
% 1.56/0.58    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f28])).
% 1.56/0.58  fof(f28,plain,(
% 1.56/0.58    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.56/0.58    inference(ennf_transformation,[],[f10])).
% 1.56/0.58  fof(f10,axiom,(
% 1.56/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.56/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 1.56/0.58  fof(f516,plain,(
% 1.56/0.58    spl4_13),
% 1.56/0.58    inference(avatar_contradiction_clause,[],[f515])).
% 1.56/0.58  fof(f515,plain,(
% 1.56/0.58    $false | spl4_13),
% 1.56/0.58    inference(subsumption_resolution,[],[f505,f96])).
% 1.56/0.58  fof(f505,plain,(
% 1.56/0.58    ~v2_funct_1(k6_partfun1(sK0)) | spl4_13),
% 1.56/0.58    inference(backward_demodulation,[],[f501,f504])).
% 1.56/0.58  fof(f501,plain,(
% 1.56/0.58    ~v2_funct_1(k5_relat_1(sK2,sK3)) | spl4_13),
% 1.56/0.58    inference(avatar_component_clause,[],[f499])).
% 1.56/0.58  fof(f114,plain,(
% 1.56/0.58    ~spl4_1 | ~spl4_2),
% 1.56/0.58    inference(avatar_split_clause,[],[f61,f111,f107])).
% 1.56/0.58  fof(f61,plain,(
% 1.56/0.58    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 1.56/0.58    inference(cnf_transformation,[],[f47])).
% 1.56/0.58  % SZS output end Proof for theBenchmark
% 1.56/0.58  % (29072)------------------------------
% 1.56/0.58  % (29072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % (29072)Termination reason: Refutation
% 1.56/0.58  
% 1.56/0.58  % (29072)Memory used [KB]: 11257
% 1.56/0.58  % (29072)Time elapsed: 0.146 s
% 1.56/0.58  % (29072)------------------------------
% 1.56/0.58  % (29072)------------------------------
% 1.81/0.58  % (29065)Success in time 0.229 s
%------------------------------------------------------------------------------
