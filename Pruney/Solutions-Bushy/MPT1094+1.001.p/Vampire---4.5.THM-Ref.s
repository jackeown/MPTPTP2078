%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1094+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:15 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 135 expanded)
%              Number of leaves         :   13 (  34 expanded)
%              Depth                    :   16
%              Number of atoms          :  216 ( 515 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f55,f71,f83])).

fof(f83,plain,
    ( ~ spl1_1
    | spl1_2 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | ~ spl1_1
    | spl1_2 ),
    inference(subsumption_resolution,[],[f81,f30])).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ v1_finset_1(sK0)
      | ~ v1_finset_1(k1_relat_1(sK0)) )
    & ( v1_finset_1(sK0)
      | v1_finset_1(k1_relat_1(sK0)) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ( ~ v1_finset_1(X0)
          | ~ v1_finset_1(k1_relat_1(X0)) )
        & ( v1_finset_1(X0)
          | v1_finset_1(k1_relat_1(X0)) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ v1_finset_1(sK0)
        | ~ v1_finset_1(k1_relat_1(sK0)) )
      & ( v1_finset_1(sK0)
        | v1_finset_1(k1_relat_1(sK0)) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(X0)
        | ~ v1_finset_1(k1_relat_1(X0)) )
      & ( v1_finset_1(X0)
        | v1_finset_1(k1_relat_1(X0)) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(X0)
        | ~ v1_finset_1(k1_relat_1(X0)) )
      & ( v1_finset_1(X0)
        | v1_finset_1(k1_relat_1(X0)) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ( v1_finset_1(k1_relat_1(X0))
      <~> v1_finset_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( v1_finset_1(k1_relat_1(X0))
      <~> v1_finset_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v1_finset_1(k1_relat_1(X0))
        <=> v1_finset_1(X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_finset_1(k1_relat_1(X0))
      <=> v1_finset_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_finset_1)).

fof(f81,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl1_1
    | spl1_2 ),
    inference(subsumption_resolution,[],[f80,f49])).

% (16358)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
fof(f49,plain,
    ( v1_finset_1(k1_relat_1(sK0))
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl1_1
  <=> v1_finset_1(k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f80,plain,
    ( ~ v1_finset_1(k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_1
    | spl1_2 ),
    inference(subsumption_resolution,[],[f78,f52])).

fof(f52,plain,
    ( ~ v1_finset_1(sK0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl1_2
  <=> v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f78,plain,
    ( v1_finset_1(sK0)
    | ~ v1_finset_1(k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(resolution,[],[f77,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_finset_1(k2_relat_1(X0))
      | v1_finset_1(X0)
      | ~ v1_finset_1(k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f60,f34])).

fof(f34,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | ~ v1_finset_1(X1)
      | v1_finset_1(X2)
      | ~ v1_finset_1(X0) ) ),
    inference(resolution,[],[f58,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0)
      | v1_finset_1(X2) ) ),
    inference(resolution,[],[f42,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_finset_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_finset_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_finset_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_finset_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_finset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_finset_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_zfmisc_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_zfmisc_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_zfmisc_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_finset_1(X0) )
     => v1_finset_1(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_finset_1)).

fof(f77,plain,
    ( v1_finset_1(k2_relat_1(sK0))
    | ~ spl1_1 ),
    inference(subsumption_resolution,[],[f76,f30])).

fof(f76,plain,
    ( v1_finset_1(k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(subsumption_resolution,[],[f74,f31])).

fof(f31,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,
    ( v1_finset_1(k2_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(resolution,[],[f49,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_finset_1(k1_relat_1(X0))
      | v1_finset_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_finset_1(k2_relat_1(X0))
      | ~ v1_finset_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_finset_1(k2_relat_1(X0))
      | ~ v1_finset_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_finset_1(k1_relat_1(X0))
       => v1_finset_1(k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_finset_1)).

fof(f71,plain,
    ( spl1_1
    | ~ spl1_2 ),
    inference(avatar_contradiction_clause,[],[f70])).

fof(f70,plain,
    ( $false
    | spl1_1
    | ~ spl1_2 ),
    inference(subsumption_resolution,[],[f69,f45])).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k9_funct_3(X0,X1)) ),
    inference(definition_unfolding,[],[f39,f38])).

fof(f38,plain,(
    ! [X0,X1] : k7_funct_3(X0,X1) = k9_funct_3(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k7_funct_3(X0,X1) = k9_funct_3(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_funct_3)).

fof(f39,plain,(
    ! [X0,X1] : v1_relat_1(k7_funct_3(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_funct_1(k7_funct_3(X0,X1))
      & v1_relat_1(k7_funct_3(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_funct_3)).

fof(f69,plain,
    ( ~ v1_relat_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)))
    | spl1_1
    | ~ spl1_2 ),
    inference(subsumption_resolution,[],[f68,f44])).

fof(f44,plain,(
    ! [X0,X1] : v1_funct_1(k9_funct_3(X0,X1)) ),
    inference(definition_unfolding,[],[f40,f38])).

fof(f40,plain,(
    ! [X0,X1] : v1_funct_1(k7_funct_3(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f68,plain,
    ( ~ v1_funct_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ v1_relat_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)))
    | spl1_1
    | ~ spl1_2 ),
    inference(subsumption_resolution,[],[f67,f53])).

fof(f53,plain,
    ( v1_finset_1(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f67,plain,
    ( ~ v1_finset_1(sK0)
    | ~ v1_funct_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ v1_relat_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)))
    | spl1_1 ),
    inference(subsumption_resolution,[],[f66,f48])).

fof(f48,plain,
    ( ~ v1_finset_1(k1_relat_1(sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f66,plain,
    ( v1_finset_1(k1_relat_1(sK0))
    | ~ v1_finset_1(sK0)
    | ~ v1_funct_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ v1_relat_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(superposition,[],[f41,f64])).

fof(f64,plain,(
    k1_relat_1(sK0) = k9_relat_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f62,f30])).

fof(f62,plain,
    ( k1_relat_1(sK0) = k9_relat_1(k9_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)),sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f36,f31])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_funct_3)).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v1_finset_1(k9_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_finset_1)).

fof(f55,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f33,f51,f47])).

fof(f33,plain,
    ( ~ v1_finset_1(sK0)
    | ~ v1_finset_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,
    ( spl1_1
    | spl1_2 ),
    inference(avatar_split_clause,[],[f32,f51,f47])).

fof(f32,plain,
    ( v1_finset_1(sK0)
    | v1_finset_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

%------------------------------------------------------------------------------
