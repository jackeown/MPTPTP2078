%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 309 expanded)
%              Number of leaves         :   17 (  79 expanded)
%              Depth                    :   22
%              Number of atoms          :  278 (1359 expanded)
%              Number of equality atoms :   86 ( 600 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f171,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f73,f77,f131,f170])).

fof(f170,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f168,f72])).

fof(f72,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl5_3
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f168,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f167,f141])).

fof(f141,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f79,f66])).

fof(f66,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl5_2
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f79,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f35,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
      | ( k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3))
        & r2_hidden(sK3,sK1) ) )
    & ( sK1 = k2_relset_1(sK0,sK1,sK2)
      | ! [X4] :
          ( k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X4))
          | ~ r2_hidden(X4,sK1) ) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f25,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relset_1(X0,X1,X2) != X1
          | ? [X3] :
              ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
              & r2_hidden(X3,X1) ) )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ! [X4] :
              ( k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X4))
              | ~ r2_hidden(X4,X1) ) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( sK1 != k2_relset_1(sK0,sK1,sK2)
        | ? [X3] :
            ( k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(X3))
            & r2_hidden(X3,sK1) ) )
      & ( sK1 = k2_relset_1(sK0,sK1,sK2)
        | ! [X4] :
            ( k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X4))
            | ~ r2_hidden(X4,sK1) ) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(X3))
        & r2_hidden(X3,sK1) )
   => ( k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3))
      & r2_hidden(sK3,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X4] :
            ( k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X4))
            | ~ r2_hidden(X4,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X3] :
            ( k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3))
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) != X1
        | ? [X3] :
            ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
            & r2_hidden(X3,X1) ) )
      & ( k2_relset_1(X0,X1,X2) = X1
        | ! [X3] :
            ( k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3))
            | ~ r2_hidden(X3,X1) ) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3))
            | ~ r2_hidden(X3,X1) )
      <~> k2_relset_1(X0,X1,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( ! [X3] :
              ~ ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_2)).

fof(f167,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f163,f80])).

fof(f80,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f35,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f163,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl5_1 ),
    inference(trivial_inequality_removal,[],[f162])).

fof(f162,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl5_1 ),
    inference(superposition,[],[f57,f159])).

fof(f159,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k2_tarski(sK3,sK3))
    | ~ spl5_1 ),
    inference(superposition,[],[f63,f78])).

fof(f78,plain,(
    ! [X0] : k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(resolution,[],[f35,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f63,plain,
    ( k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k2_tarski(sK3,sK3))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl5_1
  <=> k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k2_tarski(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,k2_tarski(X0,X0))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f40,f39])).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k2_relat_1(X1))
          | k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0 )
        & ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
          | ~ r2_hidden(X0,k2_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(f131,plain,
    ( spl5_2
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f127,f99])).

fof(f99,plain,
    ( ~ r1_tarski(sK1,k2_relat_1(sK2))
    | spl5_2 ),
    inference(subsumption_resolution,[],[f98,f94])).

fof(f94,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl5_2 ),
    inference(superposition,[],[f67,f79])).

fof(f67,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f98,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(resolution,[],[f97,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f97,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f96,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f96,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f95,f35])).

fof(f95,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f52,f79])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f127,plain,
    ( r1_tarski(sK1,k2_relat_1(sK2))
    | spl5_2
    | ~ spl5_4 ),
    inference(resolution,[],[f125,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f125,plain,
    ( ~ r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1)
    | spl5_2
    | ~ spl5_4 ),
    inference(trivial_inequality_removal,[],[f122])).

fof(f122,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1)
    | spl5_2
    | ~ spl5_4 ),
    inference(superposition,[],[f82,f121])).

fof(f121,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k2_tarski(sK4(sK1,k2_relat_1(sK2)),sK4(sK1,k2_relat_1(sK2))))
    | spl5_2 ),
    inference(resolution,[],[f101,f99])).

fof(f101,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_relat_1(sK2))
      | k1_xboole_0 = k10_relat_1(sK2,k2_tarski(sK4(X0,k2_relat_1(sK2)),sK4(X0,k2_relat_1(sK2)))) ) ),
    inference(resolution,[],[f83,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f83,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_relat_1(sK2))
      | k1_xboole_0 = k10_relat_1(sK2,k2_tarski(X0,X0)) ) ),
    inference(resolution,[],[f80,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = k10_relat_1(X1,k2_tarski(X0,X0))
      | r2_hidden(X0,k2_relat_1(X1)) ) ),
    inference(definition_unfolding,[],[f41,f39])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_relat_1(X1))
      | k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f82,plain,
    ( ! [X4] :
        ( k1_xboole_0 != k10_relat_1(sK2,k2_tarski(X4,X4))
        | ~ r2_hidden(X4,sK1) )
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f76,f78])).

fof(f76,plain,
    ( ! [X4] :
        ( k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k2_tarski(X4,X4))
        | ~ r2_hidden(X4,sK1) )
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl5_4
  <=> ! [X4] :
        ( k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k2_tarski(X4,X4))
        | ~ r2_hidden(X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f77,plain,
    ( spl5_4
    | spl5_2 ),
    inference(avatar_split_clause,[],[f55,f65,f75])).

fof(f55,plain,(
    ! [X4] :
      ( sK1 = k2_relset_1(sK0,sK1,sK2)
      | k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k2_tarski(X4,X4))
      | ~ r2_hidden(X4,sK1) ) ),
    inference(definition_unfolding,[],[f36,f39])).

fof(f36,plain,(
    ! [X4] :
      ( sK1 = k2_relset_1(sK0,sK1,sK2)
      | k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X4))
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f73,plain,
    ( spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f37,f65,f70])).

fof(f37,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f68,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f54,f65,f61])).

fof(f54,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k2_tarski(sK3,sK3)) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f38,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:15:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (22440)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (22443)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.50  % (22448)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (22458)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (22438)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (22462)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (22435)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (22439)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (22442)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (22436)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (22436)Refutation not found, incomplete strategy% (22436)------------------------------
% 0.21/0.51  % (22436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22436)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22436)Memory used [KB]: 10746
% 0.21/0.51  % (22436)Time elapsed: 0.106 s
% 0.21/0.51  % (22436)------------------------------
% 0.21/0.51  % (22436)------------------------------
% 0.21/0.51  % (22442)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f68,f73,f77,f131,f170])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f169])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    $false | (~spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f168,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    r2_hidden(sK3,sK1) | ~spl5_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    spl5_3 <=> r2_hidden(sK3,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    ~r2_hidden(sK3,sK1) | (~spl5_1 | ~spl5_2)),
% 0.21/0.51    inference(forward_demodulation,[],[f167,f141])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    sK1 = k2_relat_1(sK2) | ~spl5_2),
% 0.21/0.51    inference(backward_demodulation,[],[f79,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl5_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    spl5_2 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.51    inference(resolution,[],[f35,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    (sK1 != k2_relset_1(sK0,sK1,sK2) | (k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3)) & r2_hidden(sK3,sK1))) & (sK1 = k2_relset_1(sK0,sK1,sK2) | ! [X4] : (k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X4)) | ~r2_hidden(X4,sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f25,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X4] : (k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X4)) | ~r2_hidden(X4,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((sK1 != k2_relset_1(sK0,sK1,sK2) | ? [X3] : (k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(X3)) & r2_hidden(X3,sK1))) & (sK1 = k2_relset_1(sK0,sK1,sK2) | ! [X4] : (k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X4)) | ~r2_hidden(X4,sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ? [X3] : (k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(X3)) & r2_hidden(X3,sK1)) => (k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3)) & r2_hidden(sK3,sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X4] : (k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X4)) | ~r2_hidden(X4,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(rectify,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X3] : (k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3)) | ~r2_hidden(X3,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) != X1 | ? [X3] : (k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1))) & (k2_relset_1(X0,X1,X2) = X1 | ! [X3] : (k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3)) | ~r2_hidden(X3,X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((! [X3] : (k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3)) | ~r2_hidden(X3,X1)) <~> k2_relset_1(X0,X1,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (! [X3] : ~(k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.51  fof(f11,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.51    inference(negated_conjecture,[],[f10])).
% 0.21/0.51  fof(f10,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_2)).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    ~r2_hidden(sK3,k2_relat_1(sK2)) | ~spl5_1),
% 0.21/0.51    inference(subsumption_resolution,[],[f163,f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    v1_relat_1(sK2)),
% 0.21/0.51    inference(resolution,[],[f35,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    ~r2_hidden(sK3,k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl5_1),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f162])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK3,k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl5_1),
% 0.21/0.51    inference(superposition,[],[f57,f159])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    k1_xboole_0 = k10_relat_1(sK2,k2_tarski(sK3,sK3)) | ~spl5_1),
% 0.21/0.51    inference(superposition,[],[f63,f78])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X0] : (k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0)) )),
% 0.21/0.51    inference(resolution,[],[f35,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k2_tarski(sK3,sK3)) | ~spl5_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    spl5_1 <=> k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k2_tarski(sK3,sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,k2_tarski(X0,X0)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f40,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : (((r2_hidden(X0,k2_relat_1(X1)) | k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0) & (k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 | ~r2_hidden(X0,k2_relat_1(X1)))) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    spl5_2 | ~spl5_4),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f130])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    $false | (spl5_2 | ~spl5_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f127,f99])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    ~r1_tarski(sK1,k2_relat_1(sK2)) | spl5_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f98,f94])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    sK1 != k2_relat_1(sK2) | spl5_2),
% 0.21/0.51    inference(superposition,[],[f67,f79])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    sK1 != k2_relset_1(sK0,sK1,sK2) | spl5_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f65])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    sK1 = k2_relat_1(sK2) | ~r1_tarski(sK1,k2_relat_1(sK2))),
% 0.21/0.51    inference(resolution,[],[f97,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(flattening,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.51    inference(resolution,[],[f96,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f95,f35])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(superposition,[],[f52,f79])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    r1_tarski(sK1,k2_relat_1(sK2)) | (spl5_2 | ~spl5_4)),
% 0.21/0.51    inference(resolution,[],[f125,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.51    inference(rectify,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    ~r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1) | (spl5_2 | ~spl5_4)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f122])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1) | (spl5_2 | ~spl5_4)),
% 0.21/0.51    inference(superposition,[],[f82,f121])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    k1_xboole_0 = k10_relat_1(sK2,k2_tarski(sK4(sK1,k2_relat_1(sK2)),sK4(sK1,k2_relat_1(sK2)))) | spl5_2),
% 0.21/0.51    inference(resolution,[],[f101,f99])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(X0,k2_relat_1(sK2)) | k1_xboole_0 = k10_relat_1(sK2,k2_tarski(sK4(X0,k2_relat_1(sK2)),sK4(X0,k2_relat_1(sK2))))) )),
% 0.21/0.51    inference(resolution,[],[f83,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK2)) | k1_xboole_0 = k10_relat_1(sK2,k2_tarski(X0,X0))) )),
% 0.21/0.51    inference(resolution,[],[f80,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 = k10_relat_1(X1,k2_tarski(X0,X0)) | r2_hidden(X0,k2_relat_1(X1))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f41,f39])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(X0,k2_relat_1(X1)) | k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0 | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ( ! [X4] : (k1_xboole_0 != k10_relat_1(sK2,k2_tarski(X4,X4)) | ~r2_hidden(X4,sK1)) ) | ~spl5_4),
% 0.21/0.51    inference(backward_demodulation,[],[f76,f78])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X4] : (k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k2_tarski(X4,X4)) | ~r2_hidden(X4,sK1)) ) | ~spl5_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    spl5_4 <=> ! [X4] : (k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k2_tarski(X4,X4)) | ~r2_hidden(X4,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    spl5_4 | spl5_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f55,f65,f75])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X4] : (sK1 = k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k2_tarski(X4,X4)) | ~r2_hidden(X4,sK1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f36,f39])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X4] : (sK1 = k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X4)) | ~r2_hidden(X4,sK1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    spl5_3 | ~spl5_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f37,f65,f70])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    sK1 != k2_relset_1(sK0,sK1,sK2) | r2_hidden(sK3,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    spl5_1 | ~spl5_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f54,f65,f61])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k2_tarski(sK3,sK3))),
% 0.21/0.51    inference(definition_unfolding,[],[f38,f39])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3))),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (22442)------------------------------
% 0.21/0.51  % (22442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22442)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (22442)Memory used [KB]: 10746
% 0.21/0.51  % (22442)Time elapsed: 0.107 s
% 0.21/0.51  % (22442)------------------------------
% 0.21/0.51  % (22442)------------------------------
% 0.21/0.52  % (22433)Success in time 0.161 s
%------------------------------------------------------------------------------
