%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:27 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 206 expanded)
%              Number of leaves         :   17 (  60 expanded)
%              Depth                    :   18
%              Number of atoms          :  289 ( 906 expanded)
%              Number of equality atoms :   49 ( 112 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f217,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f75,f146,f210,f214,f216])).

fof(f216,plain,
    ( ~ spl6_15
    | spl6_2 ),
    inference(avatar_split_clause,[],[f135,f67,f207])).

fof(f207,plain,
    ( spl6_15
  <=> v1_funct_2(sK5,k1_relat_1(sK5),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f67,plain,
    ( spl6_2
  <=> v1_funct_2(sK5,k1_relat_1(sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f135,plain,
    ( ~ v1_funct_2(sK5,k1_relat_1(sK5),k1_xboole_0)
    | spl6_2 ),
    inference(backward_demodulation,[],[f69,f132])).

fof(f132,plain,
    ( k1_xboole_0 = sK4
    | spl6_2 ),
    inference(resolution,[],[f131,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f131,plain,
    ( sP1(k1_relat_1(sK5),sK4)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f130,f34])).

fof(f34,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4)))
      | ~ v1_funct_2(sK5,k1_relat_1(sK5),sK4)
      | ~ v1_funct_1(sK5) )
    & r1_tarski(k2_relat_1(sK5),sK4)
    & v1_funct_1(sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f10,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4)))
        | ~ v1_funct_2(sK5,k1_relat_1(sK5),sK4)
        | ~ v1_funct_1(sK5) )
      & r1_tarski(k2_relat_1(sK5),sK4)
      & v1_funct_1(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f130,plain,
    ( sP1(k1_relat_1(sK5),sK4)
    | ~ v1_relat_1(sK5)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f129,f56])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f129,plain,
    ( sP1(k1_relat_1(sK5),sK4)
    | ~ r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f128,f36])).

fof(f36,plain,(
    r1_tarski(k2_relat_1(sK5),sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f128,plain,
    ( sP1(k1_relat_1(sK5),sK4)
    | ~ r1_tarski(k2_relat_1(sK5),sK4)
    | ~ r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | spl6_2 ),
    inference(trivial_inequality_removal,[],[f123])).

fof(f123,plain,
    ( sP1(k1_relat_1(sK5),sK4)
    | k1_relat_1(sK5) != k1_relat_1(sK5)
    | ~ r1_tarski(k2_relat_1(sK5),sK4)
    | ~ r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | spl6_2 ),
    inference(resolution,[],[f120,f69])).

fof(f120,plain,(
    ! [X2,X3,X1] :
      ( v1_funct_2(X1,X2,X3)
      | sP1(X2,X3)
      | k1_relat_1(X1) != X2
      | ~ r1_tarski(k2_relat_1(X1),X3)
      | ~ r1_tarski(k1_relat_1(X1),X2)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f116,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f116,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | k1_relat_1(X5) != X3 ) ),
    inference(subsumption_resolution,[],[f114,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X2,X1,X0)
        & sP2(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f17,f22,f21,f20])).

fof(f21,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP3(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f114,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) != X3
      | v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | ~ sP2(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f51,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) != X0
      | v1_funct_2(X1,X0,X2)
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f69,plain,
    ( ~ v1_funct_2(sK5,k1_relat_1(sK5),sK4)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f214,plain,
    ( ~ spl6_1
    | spl6_11 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | ~ spl6_1
    | spl6_11 ),
    inference(subsumption_resolution,[],[f212,f34])).

fof(f212,plain,
    ( ~ v1_relat_1(sK5)
    | ~ spl6_1
    | spl6_11 ),
    inference(subsumption_resolution,[],[f211,f64])).

fof(f64,plain,
    ( v1_funct_1(sK5)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl6_1
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f211,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | spl6_11 ),
    inference(resolution,[],[f190,f42])).

fof(f42,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f12,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f12,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f190,plain,
    ( ~ sP0(sK5)
    | spl6_11 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl6_11
  <=> sP0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f210,plain,
    ( ~ spl6_11
    | spl6_15
    | spl6_2 ),
    inference(avatar_split_clause,[],[f182,f67,f207,f188])).

fof(f182,plain,
    ( v1_funct_2(sK5,k1_relat_1(sK5),k1_xboole_0)
    | ~ sP0(sK5)
    | spl6_2 ),
    inference(superposition,[],[f40,f160])).

fof(f160,plain,
    ( k1_xboole_0 = k2_relat_1(sK5)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f150,f38])).

% (23231)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f150,plain,
    ( k1_xboole_0 = k2_relat_1(sK5)
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(sK5))
    | spl6_2 ),
    inference(resolution,[],[f136,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f136,plain,
    ( r1_tarski(k2_relat_1(sK5),k1_xboole_0)
    | spl6_2 ),
    inference(backward_demodulation,[],[f36,f132])).

fof(f40,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f146,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl6_3 ),
    inference(subsumption_resolution,[],[f144,f34])).

fof(f144,plain,
    ( ~ v1_relat_1(sK5)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f143,f56])).

fof(f143,plain,
    ( ~ r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f142,f36])).

fof(f142,plain,
    ( ~ r1_tarski(k2_relat_1(sK5),sK4)
    | ~ r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | spl6_3 ),
    inference(resolution,[],[f73,f46])).

fof(f73,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl6_3
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f75,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f35,f63])).

fof(f35,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f37,f71,f67,f63])).

fof(f37,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4)))
    | ~ v1_funct_2(sK5,k1_relat_1(sK5),sK4)
    | ~ v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:47:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.47  % (23230)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.19/0.48  % (23243)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.19/0.48  % (23228)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.48  % (23230)Refutation found. Thanks to Tanya!
% 0.19/0.48  % SZS status Theorem for theBenchmark
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f217,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(avatar_sat_refutation,[],[f74,f75,f146,f210,f214,f216])).
% 0.19/0.48  fof(f216,plain,(
% 0.19/0.48    ~spl6_15 | spl6_2),
% 0.19/0.48    inference(avatar_split_clause,[],[f135,f67,f207])).
% 0.19/0.48  fof(f207,plain,(
% 0.19/0.48    spl6_15 <=> v1_funct_2(sK5,k1_relat_1(sK5),k1_xboole_0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.19/0.48  fof(f67,plain,(
% 0.19/0.48    spl6_2 <=> v1_funct_2(sK5,k1_relat_1(sK5),sK4)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.19/0.48  fof(f135,plain,(
% 0.19/0.48    ~v1_funct_2(sK5,k1_relat_1(sK5),k1_xboole_0) | spl6_2),
% 0.19/0.48    inference(backward_demodulation,[],[f69,f132])).
% 0.19/0.48  fof(f132,plain,(
% 0.19/0.48    k1_xboole_0 = sK4 | spl6_2),
% 0.19/0.48    inference(resolution,[],[f131,f52])).
% 0.19/0.48  fof(f52,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~sP1(X0,X1) | k1_xboole_0 = X1) )),
% 0.19/0.48    inference(cnf_transformation,[],[f33])).
% 0.19/0.48  fof(f33,plain,(
% 0.19/0.48    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 0.19/0.48    inference(nnf_transformation,[],[f20])).
% 0.19/0.48  fof(f20,plain,(
% 0.19/0.48    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 0.19/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.19/0.48  fof(f131,plain,(
% 0.19/0.48    sP1(k1_relat_1(sK5),sK4) | spl6_2),
% 0.19/0.48    inference(subsumption_resolution,[],[f130,f34])).
% 0.19/0.48  fof(f34,plain,(
% 0.19/0.48    v1_relat_1(sK5)),
% 0.19/0.48    inference(cnf_transformation,[],[f25])).
% 0.19/0.48  fof(f25,plain,(
% 0.19/0.48    (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4))) | ~v1_funct_2(sK5,k1_relat_1(sK5),sK4) | ~v1_funct_1(sK5)) & r1_tarski(k2_relat_1(sK5),sK4) & v1_funct_1(sK5) & v1_relat_1(sK5)),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f10,f24])).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4))) | ~v1_funct_2(sK5,k1_relat_1(sK5),sK4) | ~v1_funct_1(sK5)) & r1_tarski(k2_relat_1(sK5),sK4) & v1_funct_1(sK5) & v1_relat_1(sK5))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f10,plain,(
% 0.19/0.48    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.19/0.48    inference(flattening,[],[f9])).
% 0.19/0.48  fof(f9,plain,(
% 0.19/0.48    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.19/0.48    inference(ennf_transformation,[],[f8])).
% 0.19/0.48  fof(f8,negated_conjecture,(
% 0.19/0.48    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.19/0.48    inference(negated_conjecture,[],[f7])).
% 0.19/0.48  fof(f7,conjecture,(
% 0.19/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.19/0.48  fof(f130,plain,(
% 0.19/0.48    sP1(k1_relat_1(sK5),sK4) | ~v1_relat_1(sK5) | spl6_2),
% 0.19/0.48    inference(subsumption_resolution,[],[f129,f56])).
% 0.19/0.48  fof(f56,plain,(
% 0.19/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.48    inference(equality_resolution,[],[f44])).
% 0.19/0.48  fof(f44,plain,(
% 0.19/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.48    inference(cnf_transformation,[],[f28])).
% 0.19/0.48  fof(f28,plain,(
% 0.19/0.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.48    inference(flattening,[],[f27])).
% 0.19/0.48  fof(f27,plain,(
% 0.19/0.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.48    inference(nnf_transformation,[],[f1])).
% 0.19/0.48  fof(f1,axiom,(
% 0.19/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.48  fof(f129,plain,(
% 0.19/0.48    sP1(k1_relat_1(sK5),sK4) | ~r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5)) | ~v1_relat_1(sK5) | spl6_2),
% 0.19/0.48    inference(subsumption_resolution,[],[f128,f36])).
% 0.19/0.48  fof(f36,plain,(
% 0.19/0.48    r1_tarski(k2_relat_1(sK5),sK4)),
% 0.19/0.48    inference(cnf_transformation,[],[f25])).
% 0.19/0.48  fof(f128,plain,(
% 0.19/0.48    sP1(k1_relat_1(sK5),sK4) | ~r1_tarski(k2_relat_1(sK5),sK4) | ~r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5)) | ~v1_relat_1(sK5) | spl6_2),
% 0.19/0.48    inference(trivial_inequality_removal,[],[f123])).
% 0.19/0.48  fof(f123,plain,(
% 0.19/0.48    sP1(k1_relat_1(sK5),sK4) | k1_relat_1(sK5) != k1_relat_1(sK5) | ~r1_tarski(k2_relat_1(sK5),sK4) | ~r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5)) | ~v1_relat_1(sK5) | spl6_2),
% 0.19/0.48    inference(resolution,[],[f120,f69])).
% 0.19/0.48  fof(f120,plain,(
% 0.19/0.48    ( ! [X2,X3,X1] : (v1_funct_2(X1,X2,X3) | sP1(X2,X3) | k1_relat_1(X1) != X2 | ~r1_tarski(k2_relat_1(X1),X3) | ~r1_tarski(k1_relat_1(X1),X2) | ~v1_relat_1(X1)) )),
% 0.19/0.48    inference(resolution,[],[f116,f46])).
% 0.19/0.48  fof(f46,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f14])).
% 0.19/0.48  fof(f14,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.19/0.48    inference(flattening,[],[f13])).
% 0.19/0.48  fof(f13,plain,(
% 0.19/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.19/0.48    inference(ennf_transformation,[],[f4])).
% 0.19/0.48  fof(f4,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.19/0.48  fof(f116,plain,(
% 0.19/0.48    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | v1_funct_2(X5,X3,X4) | sP1(X3,X4) | k1_relat_1(X5) != X3) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f114,f54])).
% 0.19/0.48  fof(f54,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X0,X2,X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f23])).
% 0.19/0.48  fof(f23,plain,(
% 0.19/0.48    ! [X0,X1,X2] : ((sP3(X2,X1,X0) & sP2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    inference(definition_folding,[],[f17,f22,f21,f20])).
% 0.19/0.48  fof(f21,plain,(
% 0.19/0.48    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 0.19/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.19/0.48  fof(f22,plain,(
% 0.19/0.48    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP3(X2,X1,X0))),
% 0.19/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.19/0.48  fof(f17,plain,(
% 0.19/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    inference(flattening,[],[f16])).
% 0.19/0.48  fof(f16,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    inference(ennf_transformation,[],[f5])).
% 0.19/0.48  fof(f5,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.19/0.48  fof(f114,plain,(
% 0.19/0.48    ( ! [X4,X5,X3] : (k1_relat_1(X5) != X3 | v1_funct_2(X5,X3,X4) | sP1(X3,X4) | ~sP2(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.19/0.48    inference(superposition,[],[f51,f47])).
% 0.19/0.48  fof(f47,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f15])).
% 0.19/0.48  fof(f15,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    inference(ennf_transformation,[],[f3])).
% 0.19/0.48  fof(f3,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.19/0.48  fof(f51,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) != X0 | v1_funct_2(X1,X0,X2) | sP1(X0,X2) | ~sP2(X0,X1,X2)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f32])).
% 0.19/0.48  fof(f32,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP1(X0,X2) | ~sP2(X0,X1,X2))),
% 0.19/0.48    inference(rectify,[],[f31])).
% 0.19/0.48  fof(f31,plain,(
% 0.19/0.48    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 0.19/0.48    inference(nnf_transformation,[],[f21])).
% 0.19/0.48  fof(f69,plain,(
% 0.19/0.48    ~v1_funct_2(sK5,k1_relat_1(sK5),sK4) | spl6_2),
% 0.19/0.48    inference(avatar_component_clause,[],[f67])).
% 0.19/0.48  fof(f214,plain,(
% 0.19/0.48    ~spl6_1 | spl6_11),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f213])).
% 0.19/0.48  fof(f213,plain,(
% 0.19/0.48    $false | (~spl6_1 | spl6_11)),
% 0.19/0.48    inference(subsumption_resolution,[],[f212,f34])).
% 0.19/0.48  fof(f212,plain,(
% 0.19/0.48    ~v1_relat_1(sK5) | (~spl6_1 | spl6_11)),
% 0.19/0.48    inference(subsumption_resolution,[],[f211,f64])).
% 0.19/0.48  fof(f64,plain,(
% 0.19/0.48    v1_funct_1(sK5) | ~spl6_1),
% 0.19/0.48    inference(avatar_component_clause,[],[f63])).
% 0.19/0.48  fof(f63,plain,(
% 0.19/0.48    spl6_1 <=> v1_funct_1(sK5)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.19/0.48  fof(f211,plain,(
% 0.19/0.48    ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | spl6_11),
% 0.19/0.48    inference(resolution,[],[f190,f42])).
% 0.19/0.48  fof(f42,plain,(
% 0.19/0.48    ( ! [X0] : (sP0(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f19])).
% 0.19/0.48  fof(f19,plain,(
% 0.19/0.48    ! [X0] : (sP0(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(definition_folding,[],[f12,f18])).
% 0.19/0.48  fof(f18,plain,(
% 0.19/0.48    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~sP0(X0))),
% 0.19/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.19/0.48  fof(f12,plain,(
% 0.19/0.48    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(flattening,[],[f11])).
% 0.19/0.48  fof(f11,plain,(
% 0.19/0.48    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f6])).
% 0.19/0.48  fof(f6,axiom,(
% 0.19/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.19/0.48  fof(f190,plain,(
% 0.19/0.48    ~sP0(sK5) | spl6_11),
% 0.19/0.48    inference(avatar_component_clause,[],[f188])).
% 0.19/0.48  fof(f188,plain,(
% 0.19/0.48    spl6_11 <=> sP0(sK5)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.19/0.48  fof(f210,plain,(
% 0.19/0.48    ~spl6_11 | spl6_15 | spl6_2),
% 0.19/0.48    inference(avatar_split_clause,[],[f182,f67,f207,f188])).
% 0.19/0.48  fof(f182,plain,(
% 0.19/0.48    v1_funct_2(sK5,k1_relat_1(sK5),k1_xboole_0) | ~sP0(sK5) | spl6_2),
% 0.19/0.48    inference(superposition,[],[f40,f160])).
% 0.19/0.48  fof(f160,plain,(
% 0.19/0.48    k1_xboole_0 = k2_relat_1(sK5) | spl6_2),
% 0.19/0.48    inference(subsumption_resolution,[],[f150,f38])).
% 0.19/0.49  % (23231)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.49  fof(f38,plain,(
% 0.19/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.19/0.49  fof(f150,plain,(
% 0.19/0.49    k1_xboole_0 = k2_relat_1(sK5) | ~r1_tarski(k1_xboole_0,k2_relat_1(sK5)) | spl6_2),
% 0.19/0.49    inference(resolution,[],[f136,f45])).
% 0.19/0.49  fof(f45,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f28])).
% 0.19/0.49  fof(f136,plain,(
% 0.19/0.49    r1_tarski(k2_relat_1(sK5),k1_xboole_0) | spl6_2),
% 0.19/0.49    inference(backward_demodulation,[],[f36,f132])).
% 0.19/0.49  fof(f40,plain,(
% 0.19/0.49    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~sP0(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f26])).
% 0.19/0.49  fof(f26,plain,(
% 0.19/0.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~sP0(X0))),
% 0.19/0.49    inference(nnf_transformation,[],[f18])).
% 0.19/0.49  fof(f146,plain,(
% 0.19/0.49    spl6_3),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f145])).
% 0.19/0.49  fof(f145,plain,(
% 0.19/0.49    $false | spl6_3),
% 0.19/0.49    inference(subsumption_resolution,[],[f144,f34])).
% 0.19/0.49  fof(f144,plain,(
% 0.19/0.49    ~v1_relat_1(sK5) | spl6_3),
% 0.19/0.49    inference(subsumption_resolution,[],[f143,f56])).
% 0.19/0.49  fof(f143,plain,(
% 0.19/0.49    ~r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5)) | ~v1_relat_1(sK5) | spl6_3),
% 0.19/0.49    inference(subsumption_resolution,[],[f142,f36])).
% 0.19/0.49  fof(f142,plain,(
% 0.19/0.49    ~r1_tarski(k2_relat_1(sK5),sK4) | ~r1_tarski(k1_relat_1(sK5),k1_relat_1(sK5)) | ~v1_relat_1(sK5) | spl6_3),
% 0.19/0.49    inference(resolution,[],[f73,f46])).
% 0.19/0.49  fof(f73,plain,(
% 0.19/0.49    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4))) | spl6_3),
% 0.19/0.49    inference(avatar_component_clause,[],[f71])).
% 0.19/0.49  fof(f71,plain,(
% 0.19/0.49    spl6_3 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4)))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.19/0.49  fof(f75,plain,(
% 0.19/0.49    spl6_1),
% 0.19/0.49    inference(avatar_split_clause,[],[f35,f63])).
% 0.19/0.49  fof(f35,plain,(
% 0.19/0.49    v1_funct_1(sK5)),
% 0.19/0.49    inference(cnf_transformation,[],[f25])).
% 0.19/0.49  fof(f74,plain,(
% 0.19/0.49    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 0.19/0.49    inference(avatar_split_clause,[],[f37,f71,f67,f63])).
% 0.19/0.49  fof(f37,plain,(
% 0.19/0.49    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),sK4))) | ~v1_funct_2(sK5,k1_relat_1(sK5),sK4) | ~v1_funct_1(sK5)),
% 0.19/0.49    inference(cnf_transformation,[],[f25])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (23230)------------------------------
% 0.19/0.49  % (23230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (23230)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (23230)Memory used [KB]: 6140
% 0.19/0.49  % (23230)Time elapsed: 0.085 s
% 0.19/0.49  % (23230)------------------------------
% 0.19/0.49  % (23230)------------------------------
% 0.19/0.49  % (23231)Refutation not found, incomplete strategy% (23231)------------------------------
% 0.19/0.49  % (23231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (23231)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (23231)Memory used [KB]: 6140
% 0.19/0.49  % (23231)Time elapsed: 0.093 s
% 0.19/0.49  % (23231)------------------------------
% 0.19/0.49  % (23231)------------------------------
% 0.19/0.49  % (23223)Success in time 0.141 s
%------------------------------------------------------------------------------
