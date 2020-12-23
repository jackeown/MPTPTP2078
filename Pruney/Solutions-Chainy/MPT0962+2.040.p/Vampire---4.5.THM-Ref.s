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
% DateTime   : Thu Dec  3 13:00:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 364 expanded)
%              Number of leaves         :   18 ( 102 expanded)
%              Depth                    :   20
%              Number of atoms          :  368 (1572 expanded)
%              Number of equality atoms :   94 ( 297 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f477,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f77,f371,f400,f408,f458,f475])).

fof(f475,plain,
    ( spl5_2
    | ~ spl5_16
    | ~ spl5_18 ),
    inference(avatar_contradiction_clause,[],[f474])).

fof(f474,plain,
    ( $false
    | spl5_2
    | ~ spl5_16
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f465,f63])).

fof(f63,plain,(
    ! [X1] : ~ sP0(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f465,plain,
    ( sP0(k1_xboole_0,k1_xboole_0)
    | spl5_2
    | ~ spl5_16
    | ~ spl5_18 ),
    inference(backward_demodulation,[],[f429,f205])).

fof(f205,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl5_16
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f429,plain,
    ( sP0(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl5_2
    | ~ spl5_18 ),
    inference(backward_demodulation,[],[f355,f386])).

fof(f386,plain,
    ( k1_xboole_0 = sK4
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f384])).

fof(f384,plain,
    ( spl5_18
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f355,plain,
    ( sP0(k1_relat_1(sK4),k1_xboole_0)
    | spl5_2 ),
    inference(backward_demodulation,[],[f353,f354])).

fof(f354,plain,
    ( k1_xboole_0 = sK3
    | spl5_2 ),
    inference(resolution,[],[f353,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f353,plain,
    ( sP0(k1_relat_1(sK4),sK3)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f352,f33])).

fof(f33,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
      | ~ v1_funct_2(sK4,k1_relat_1(sK4),sK3)
      | ~ v1_funct_1(sK4) )
    & r1_tarski(k2_relat_1(sK4),sK3)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f11,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
        | ~ v1_funct_2(sK4,k1_relat_1(sK4),sK3)
        | ~ v1_funct_1(sK4) )
      & r1_tarski(k2_relat_1(sK4),sK3)
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f352,plain,
    ( sP0(k1_relat_1(sK4),sK3)
    | ~ v1_relat_1(sK4)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f351,f56])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f351,plain,
    ( sP0(k1_relat_1(sK4),sK3)
    | ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f344,f35])).

fof(f35,plain,(
    r1_tarski(k2_relat_1(sK4),sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f344,plain,
    ( sP0(k1_relat_1(sK4),sK3)
    | ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl5_2 ),
    inference(trivial_inequality_removal,[],[f343])).

fof(f343,plain,
    ( sP0(k1_relat_1(sK4),sK3)
    | k1_relat_1(sK4) != k1_relat_1(sK4)
    | ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl5_2 ),
    inference(resolution,[],[f225,f71])).

fof(f71,plain,
    ( ~ v1_funct_2(sK4,k1_relat_1(sK4),sK3)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl5_2
  <=> v1_funct_2(sK4,k1_relat_1(sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f225,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X0,X1,X2)
      | sP0(X1,X2)
      | k1_relat_1(X0) != X1
      | ~ r1_tarski(k2_relat_1(X0),X2)
      | ~ r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f155,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f155,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | k1_relat_1(X5) != X3 ) ),
    inference(subsumption_resolution,[],[f153,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f16,f19,f18,f17])).

fof(f18,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f153,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) != X3
      | v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | ~ sP1(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f51,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) != X0
      | v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f458,plain,
    ( spl5_16
    | spl5_2
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f444,f384,f69,f204])).

fof(f444,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | spl5_2
    | ~ spl5_18 ),
    inference(resolution,[],[f433,f113])).

fof(f113,plain,(
    ! [X2] :
      ( v1_funct_2(k1_xboole_0,X2,k1_xboole_0)
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f61,f105])).

fof(f105,plain,(
    ! [X0,X1] : sP2(k1_xboole_0,X0,X1) ),
    inference(resolution,[],[f102,f37])).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X2,X1))
      | sP2(X0,X1,X2) ) ),
    inference(resolution,[],[f55,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,(
    ! [X2] :
      ( v1_funct_2(k1_xboole_0,X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | ~ sP2(k1_xboole_0,k1_xboole_0,X2) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X1] :
      ( v1_funct_2(k1_xboole_0,X2,X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X0,X2,X1)
      | k1_xboole_0 != X0
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X0,X2,X1)
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | ~ v1_funct_2(X0,X2,X1) ) )
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | ~ v1_funct_2(X2,X0,X1) ) )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f433,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl5_2
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f357,f386])).

fof(f357,plain,
    ( ~ v1_funct_2(sK4,k1_relat_1(sK4),k1_xboole_0)
    | spl5_2 ),
    inference(backward_demodulation,[],[f71,f354])).

fof(f408,plain,(
    ~ spl5_17 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | ~ spl5_17 ),
    inference(resolution,[],[f382,f56])).

fof(f382,plain,
    ( ! [X0] : ~ r1_tarski(k1_relat_1(sK4),X0)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f381])).

fof(f381,plain,
    ( spl5_17
  <=> ! [X0] : ~ r1_tarski(k1_relat_1(sK4),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f400,plain,
    ( spl5_17
    | spl5_18
    | spl5_2 ),
    inference(avatar_split_clause,[],[f399,f69,f384,f381])).

fof(f399,plain,
    ( ! [X1] :
        ( k1_xboole_0 = sK4
        | ~ r1_tarski(k1_relat_1(sK4),X1) )
    | spl5_2 ),
    inference(subsumption_resolution,[],[f398,f33])).

fof(f398,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK4)
        | k1_xboole_0 = sK4
        | ~ r1_tarski(k1_relat_1(sK4),X1) )
    | spl5_2 ),
    inference(subsumption_resolution,[],[f395,f37])).

fof(f395,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
        | ~ v1_relat_1(sK4)
        | k1_xboole_0 = sK4
        | ~ r1_tarski(k1_relat_1(sK4),X1) )
    | spl5_2 ),
    inference(superposition,[],[f317,f390])).

fof(f390,plain,
    ( k1_xboole_0 = k2_relat_1(sK4)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f378,f37])).

fof(f378,plain,
    ( k1_xboole_0 = k2_relat_1(sK4)
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(sK4))
    | spl5_2 ),
    inference(resolution,[],[f358,f40])).

% (19051)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f358,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_xboole_0)
    | spl5_2 ),
    inference(backward_demodulation,[],[f35,f354])).

fof(f317,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),k1_xboole_0)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k1_relat_1(X1),X0) ) ),
    inference(subsumption_resolution,[],[f315,f37])).

fof(f315,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),k1_xboole_0)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k1_relat_1(X1),X0) ) ),
    inference(superposition,[],[f148,f58])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f148,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(k2_zfmisc_1(X7,X8),X6)
      | ~ v1_relat_1(X6)
      | ~ r1_tarski(k2_relat_1(X6),X8)
      | k2_zfmisc_1(X7,X8) = X6
      | ~ r1_tarski(k1_relat_1(X6),X7) ) ),
    inference(resolution,[],[f124,f40])).

fof(f124,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(X6,k2_zfmisc_1(X8,X7))
      | ~ r1_tarski(k1_relat_1(X6),X8)
      | ~ v1_relat_1(X6)
      | ~ r1_tarski(k2_relat_1(X6),X7) ) ),
    inference(resolution,[],[f46,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f371,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f369,f33])).

fof(f369,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f368,f56])).

fof(f368,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f366,f35])).

fof(f366,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl5_3 ),
    inference(resolution,[],[f75,f46])).

fof(f75,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl5_3
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

% (19036)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f77,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f34,f65])).

fof(f65,plain,
    ( spl5_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f34,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f22])).

fof(f76,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f36,f73,f69,f65])).

fof(f36,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
    | ~ v1_funct_2(sK4,k1_relat_1(sK4),sK3)
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f22])).
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
% 0.14/0.34  % DateTime   : Tue Dec  1 12:57:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (19056)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.49  % (19035)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (19048)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (19038)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (19039)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (19039)Refutation not found, incomplete strategy% (19039)------------------------------
% 0.21/0.50  % (19039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (19039)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (19039)Memory used [KB]: 6140
% 0.21/0.50  % (19039)Time elapsed: 0.084 s
% 0.21/0.50  % (19039)------------------------------
% 0.21/0.50  % (19039)------------------------------
% 0.21/0.50  % (19057)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (19034)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (19038)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (19045)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (19037)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (19049)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (19053)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (19035)Refutation not found, incomplete strategy% (19035)------------------------------
% 0.21/0.51  % (19035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19035)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (19035)Memory used [KB]: 10618
% 0.21/0.51  % (19035)Time elapsed: 0.103 s
% 0.21/0.51  % (19035)------------------------------
% 0.21/0.51  % (19035)------------------------------
% 0.21/0.51  % (19041)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (19042)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f477,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f76,f77,f371,f400,f408,f458,f475])).
% 0.21/0.52  fof(f475,plain,(
% 0.21/0.52    spl5_2 | ~spl5_16 | ~spl5_18),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f474])).
% 0.21/0.52  fof(f474,plain,(
% 0.21/0.52    $false | (spl5_2 | ~spl5_16 | ~spl5_18)),
% 0.21/0.52    inference(subsumption_resolution,[],[f465,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X1] : (~sP0(k1_xboole_0,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.52  fof(f465,plain,(
% 0.21/0.52    sP0(k1_xboole_0,k1_xboole_0) | (spl5_2 | ~spl5_16 | ~spl5_18)),
% 0.21/0.52    inference(backward_demodulation,[],[f429,f205])).
% 0.21/0.52  fof(f205,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl5_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f204])).
% 0.21/0.52  fof(f204,plain,(
% 0.21/0.52    spl5_16 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.52  fof(f429,plain,(
% 0.21/0.52    sP0(k1_relat_1(k1_xboole_0),k1_xboole_0) | (spl5_2 | ~spl5_18)),
% 0.21/0.52    inference(backward_demodulation,[],[f355,f386])).
% 0.21/0.52  fof(f386,plain,(
% 0.21/0.52    k1_xboole_0 = sK4 | ~spl5_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f384])).
% 0.21/0.52  fof(f384,plain,(
% 0.21/0.52    spl5_18 <=> k1_xboole_0 = sK4),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.52  fof(f355,plain,(
% 0.21/0.52    sP0(k1_relat_1(sK4),k1_xboole_0) | spl5_2),
% 0.21/0.52    inference(backward_demodulation,[],[f353,f354])).
% 0.21/0.52  fof(f354,plain,(
% 0.21/0.52    k1_xboole_0 = sK3 | spl5_2),
% 0.21/0.52    inference(resolution,[],[f353,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~sP0(X0,X1) | k1_xboole_0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f353,plain,(
% 0.21/0.52    sP0(k1_relat_1(sK4),sK3) | spl5_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f352,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    v1_relat_1(sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) | ~v1_funct_2(sK4,k1_relat_1(sK4),sK3) | ~v1_funct_1(sK4)) & r1_tarski(k2_relat_1(sK4),sK3) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f11,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) | ~v1_funct_2(sK4,k1_relat_1(sK4),sK3) | ~v1_funct_1(sK4)) & r1_tarski(k2_relat_1(sK4),sK3) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.52    inference(negated_conjecture,[],[f8])).
% 0.21/0.52  fof(f8,conjecture,(
% 0.21/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.52  fof(f352,plain,(
% 0.21/0.52    sP0(k1_relat_1(sK4),sK3) | ~v1_relat_1(sK4) | spl5_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f351,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f351,plain,(
% 0.21/0.52    sP0(k1_relat_1(sK4),sK3) | ~r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl5_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f344,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    r1_tarski(k2_relat_1(sK4),sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f344,plain,(
% 0.21/0.52    sP0(k1_relat_1(sK4),sK3) | ~r1_tarski(k2_relat_1(sK4),sK3) | ~r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl5_2),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f343])).
% 0.21/0.52  fof(f343,plain,(
% 0.21/0.52    sP0(k1_relat_1(sK4),sK3) | k1_relat_1(sK4) != k1_relat_1(sK4) | ~r1_tarski(k2_relat_1(sK4),sK3) | ~r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl5_2),
% 0.21/0.52    inference(resolution,[],[f225,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ~v1_funct_2(sK4,k1_relat_1(sK4),sK3) | spl5_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    spl5_2 <=> v1_funct_2(sK4,k1_relat_1(sK4),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.52  fof(f225,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_funct_2(X0,X1,X2) | sP0(X1,X2) | k1_relat_1(X0) != X1 | ~r1_tarski(k2_relat_1(X0),X2) | ~r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(resolution,[],[f155,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | v1_funct_2(X5,X3,X4) | sP0(X3,X4) | k1_relat_1(X5) != X3) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f153,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(definition_folding,[],[f16,f19,f18,f17])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (k1_relat_1(X5) != X3 | v1_funct_2(X5,X3,X4) | sP0(X3,X4) | ~sP1(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.52    inference(superposition,[],[f51,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) != X0 | v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 0.21/0.52    inference(rectify,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f18])).
% 0.21/0.52  fof(f458,plain,(
% 0.21/0.52    spl5_16 | spl5_2 | ~spl5_18),
% 0.21/0.52    inference(avatar_split_clause,[],[f444,f384,f69,f204])).
% 0.21/0.52  fof(f444,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (spl5_2 | ~spl5_18)),
% 0.21/0.52    inference(resolution,[],[f433,f113])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    ( ! [X2] : (v1_funct_2(k1_xboole_0,X2,k1_xboole_0) | k1_xboole_0 = X2) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f61,f105])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sP2(k1_xboole_0,X0,X1)) )),
% 0.21/0.52    inference(resolution,[],[f102,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X2,X1)) | sP2(X0,X1,X2)) )),
% 0.21/0.52    inference(resolution,[],[f55,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X2,X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X2] : (v1_funct_2(k1_xboole_0,X2,k1_xboole_0) | k1_xboole_0 = X2 | ~sP2(k1_xboole_0,k1_xboole_0,X2)) )),
% 0.21/0.52    inference(equality_resolution,[],[f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X2,X1] : (v1_funct_2(k1_xboole_0,X2,X1) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(k1_xboole_0,X1,X2)) )),
% 0.21/0.52    inference(equality_resolution,[],[f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0 | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1))) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(X0,X1,X2))),
% 0.21/0.52    inference(rectify,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f19])).
% 0.21/0.52  fof(f433,plain,(
% 0.21/0.52    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (spl5_2 | ~spl5_18)),
% 0.21/0.52    inference(forward_demodulation,[],[f357,f386])).
% 0.21/0.52  fof(f357,plain,(
% 0.21/0.52    ~v1_funct_2(sK4,k1_relat_1(sK4),k1_xboole_0) | spl5_2),
% 0.21/0.52    inference(backward_demodulation,[],[f71,f354])).
% 0.21/0.52  fof(f408,plain,(
% 0.21/0.52    ~spl5_17),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f406])).
% 0.21/0.52  fof(f406,plain,(
% 0.21/0.52    $false | ~spl5_17),
% 0.21/0.52    inference(resolution,[],[f382,f56])).
% 0.21/0.52  fof(f382,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(k1_relat_1(sK4),X0)) ) | ~spl5_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f381])).
% 0.21/0.52  fof(f381,plain,(
% 0.21/0.52    spl5_17 <=> ! [X0] : ~r1_tarski(k1_relat_1(sK4),X0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.52  fof(f400,plain,(
% 0.21/0.52    spl5_17 | spl5_18 | spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f399,f69,f384,f381])).
% 0.21/0.52  fof(f399,plain,(
% 0.21/0.52    ( ! [X1] : (k1_xboole_0 = sK4 | ~r1_tarski(k1_relat_1(sK4),X1)) ) | spl5_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f398,f33])).
% 0.21/0.52  fof(f398,plain,(
% 0.21/0.52    ( ! [X1] : (~v1_relat_1(sK4) | k1_xboole_0 = sK4 | ~r1_tarski(k1_relat_1(sK4),X1)) ) | spl5_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f395,f37])).
% 0.21/0.52  fof(f395,plain,(
% 0.21/0.52    ( ! [X1] : (~r1_tarski(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(sK4) | k1_xboole_0 = sK4 | ~r1_tarski(k1_relat_1(sK4),X1)) ) | spl5_2),
% 0.21/0.52    inference(superposition,[],[f317,f390])).
% 0.21/0.52  fof(f390,plain,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(sK4) | spl5_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f378,f37])).
% 0.21/0.52  fof(f378,plain,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(sK4) | ~r1_tarski(k1_xboole_0,k2_relat_1(sK4)) | spl5_2),
% 0.21/0.52    inference(resolution,[],[f358,f40])).
% 0.21/0.52  % (19051)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f358,plain,(
% 0.21/0.52    r1_tarski(k2_relat_1(sK4),k1_xboole_0) | spl5_2),
% 0.21/0.52    inference(backward_demodulation,[],[f35,f354])).
% 0.21/0.52  fof(f317,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),k1_xboole_0) | ~v1_relat_1(X1) | k1_xboole_0 = X1 | ~r1_tarski(k1_relat_1(X1),X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f315,f37])).
% 0.21/0.52  fof(f315,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X1) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_xboole_0) | k1_xboole_0 = X1 | ~r1_tarski(k1_relat_1(X1),X0)) )),
% 0.21/0.52    inference(superposition,[],[f148,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    inference(flattening,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    ( ! [X6,X8,X7] : (~r1_tarski(k2_zfmisc_1(X7,X8),X6) | ~v1_relat_1(X6) | ~r1_tarski(k2_relat_1(X6),X8) | k2_zfmisc_1(X7,X8) = X6 | ~r1_tarski(k1_relat_1(X6),X7)) )),
% 0.21/0.52    inference(resolution,[],[f124,f40])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    ( ! [X6,X8,X7] : (r1_tarski(X6,k2_zfmisc_1(X8,X7)) | ~r1_tarski(k1_relat_1(X6),X8) | ~v1_relat_1(X6) | ~r1_tarski(k2_relat_1(X6),X7)) )),
% 0.21/0.52    inference(resolution,[],[f46,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f371,plain,(
% 0.21/0.52    spl5_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f370])).
% 0.21/0.52  fof(f370,plain,(
% 0.21/0.52    $false | spl5_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f369,f33])).
% 0.21/0.52  fof(f369,plain,(
% 0.21/0.52    ~v1_relat_1(sK4) | spl5_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f368,f56])).
% 0.21/0.52  fof(f368,plain,(
% 0.21/0.52    ~r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl5_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f366,f35])).
% 0.21/0.52  fof(f366,plain,(
% 0.21/0.52    ~r1_tarski(k2_relat_1(sK4),sK3) | ~r1_tarski(k1_relat_1(sK4),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl5_3),
% 0.21/0.52    inference(resolution,[],[f75,f46])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) | spl5_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    spl5_3 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.52  % (19036)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    spl5_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f34,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    spl5_1 <=> v1_funct_1(sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    v1_funct_1(sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f36,f73,f69,f65])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) | ~v1_funct_2(sK4,k1_relat_1(sK4),sK3) | ~v1_funct_1(sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (19038)------------------------------
% 0.21/0.52  % (19038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19038)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (19038)Memory used [KB]: 6268
% 0.21/0.52  % (19038)Time elapsed: 0.095 s
% 0.21/0.52  % (19038)------------------------------
% 0.21/0.52  % (19038)------------------------------
% 0.21/0.52  % (19033)Success in time 0.16 s
%------------------------------------------------------------------------------
