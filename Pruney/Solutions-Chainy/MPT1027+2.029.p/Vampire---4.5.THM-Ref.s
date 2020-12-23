%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 210 expanded)
%              Number of leaves         :   13 (  64 expanded)
%              Depth                    :   20
%              Number of atoms          :  263 ( 887 expanded)
%              Number of equality atoms :   85 ( 269 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f171,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f74,f75,f170])).

fof(f170,plain,
    ( spl6_2
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f168,f60])).

fof(f60,plain,(
    ! [X1] : ~ sP0(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f168,plain,
    ( sP0(k1_xboole_0,k1_xboole_0)
    | spl6_2
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f146,f165])).

fof(f165,plain,
    ( k1_xboole_0 = sK3
    | spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f162,f122])).

fof(f122,plain,(
    ! [X2] :
      ( v1_funct_2(k1_xboole_0,X2,k1_xboole_0)
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f58,f99])).

fof(f99,plain,(
    ! [X0,X1] : sP2(k1_xboole_0,X0,X1) ),
    inference(resolution,[],[f51,f35])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f12,f17,f16,f15])).

fof(f16,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

% (26069)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f58,plain,(
    ! [X2] :
      ( v1_funct_2(k1_xboole_0,X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | ~ sP2(k1_xboole_0,k1_xboole_0,X2) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X1] :
      ( v1_funct_2(k1_xboole_0,X2,X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X0,X2,X1)
      | k1_xboole_0 != X0
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X0,X2,X1)
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | ~ v1_funct_2(X0,X2,X1) ) )
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | ~ v1_funct_2(X2,X0,X1) ) )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f162,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK3,k1_xboole_0)
    | spl6_2
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f139,f160])).

fof(f160,plain,
    ( k1_xboole_0 = sK5
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f159,f77])).

fof(f77,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f39,f35])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f159,plain,
    ( k1_xboole_0 = sK5
    | ~ r1_tarski(k1_xboole_0,sK5)
    | spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f148,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f148,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | spl6_2
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f141,f55])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f141,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK3,k1_xboole_0))
    | spl6_2
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f76,f137])).

fof(f137,plain,
    ( k1_xboole_0 = sK4
    | spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f136,f48])).

% (26066)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f48,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f136,plain,
    ( sP0(sK3,sK4)
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f135,f93])).

fof(f93,plain,
    ( sP1(sK3,sK5,sK4)
    | ~ spl6_3 ),
    inference(resolution,[],[f50,f71])).

fof(f71,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl6_3
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f135,plain,
    ( sP0(sK3,sK4)
    | ~ sP1(sK3,sK5,sK4)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f134,f68])).

fof(f68,plain,
    ( ~ v1_funct_2(sK5,sK3,sK4)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl6_2
  <=> v1_funct_2(sK5,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f134,plain,
    ( v1_funct_2(sK5,sK3,sK4)
    | sP0(sK3,sK4)
    | ~ sP1(sK3,sK5,sK4) ),
    inference(trivial_inequality_removal,[],[f131])).

fof(f131,plain,
    ( sK3 != sK3
    | v1_funct_2(sK5,sK3,sK4)
    | sP0(sK3,sK4)
    | ~ sP1(sK3,sK5,sK4) ),
    inference(superposition,[],[f47,f33])).

fof(f33,plain,(
    sK3 = k1_relset_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      | ~ v1_funct_2(sK5,sK3,sK4)
      | ~ v1_funct_1(sK5) )
    & sK3 = k1_relset_1(sK3,sK4,sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f10,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & k1_relset_1(X0,X1,X2) = X0
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
        | ~ v1_funct_2(sK5,sK3,sK4)
        | ~ v1_funct_1(sK5) )
      & sK3 = k1_relset_1(sK3,sK4,sK5)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( k1_relset_1(X0,X1,X2) = X0
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) != X0
      | v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

% (26063)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f76,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK4))
    | ~ spl6_3 ),
    inference(resolution,[],[f39,f71])).

fof(f139,plain,
    ( ~ v1_funct_2(sK5,sK3,k1_xboole_0)
    | spl6_2
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f68,f137])).

fof(f146,plain,
    ( sP0(sK3,k1_xboole_0)
    | spl6_2
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f136,f137])).

fof(f75,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f31,f62])).

fof(f62,plain,
    ( spl6_1
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f31,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f20])).

fof(f74,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f32,f70])).

fof(f32,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f34,f70,f66,f62])).

fof(f34,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_2(sK5,sK3,sK4)
    | ~ v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:52:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (26064)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.50  % (26057)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (26055)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (26057)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (26067)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (26053)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.50  % (26058)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (26078)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.50  % (26073)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.50  % (26074)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (26058)Refutation not found, incomplete strategy% (26058)------------------------------
% 0.22/0.51  % (26058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (26072)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.51  % (26065)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f171,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f73,f74,f75,f170])).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    spl6_2 | ~spl6_3),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f169])).
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    $false | (spl6_2 | ~spl6_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f168,f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X1] : (~sP0(k1_xboole_0,X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.51  fof(f168,plain,(
% 0.22/0.51    sP0(k1_xboole_0,k1_xboole_0) | (spl6_2 | ~spl6_3)),
% 0.22/0.51    inference(backward_demodulation,[],[f146,f165])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    k1_xboole_0 = sK3 | (spl6_2 | ~spl6_3)),
% 0.22/0.51    inference(resolution,[],[f162,f122])).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    ( ! [X2] : (v1_funct_2(k1_xboole_0,X2,k1_xboole_0) | k1_xboole_0 = X2) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f58,f99])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sP2(k1_xboole_0,X0,X1)) )),
% 0.22/0.51    inference(resolution,[],[f51,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X2,X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(definition_folding,[],[f12,f17,f16,f15])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.51  % (26069)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(flattening,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X2] : (v1_funct_2(k1_xboole_0,X2,k1_xboole_0) | k1_xboole_0 = X2 | ~sP2(k1_xboole_0,k1_xboole_0,X2)) )),
% 0.22/0.51    inference(equality_resolution,[],[f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X2,X1] : (v1_funct_2(k1_xboole_0,X2,X1) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(k1_xboole_0,X1,X2)) )),
% 0.22/0.51    inference(equality_resolution,[],[f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0 | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1))) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(X0,X1,X2))),
% 0.22/0.51    inference(rectify,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X2,X1,X0] : (((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f17])).
% 0.22/0.51  fof(f162,plain,(
% 0.22/0.51    ~v1_funct_2(k1_xboole_0,sK3,k1_xboole_0) | (spl6_2 | ~spl6_3)),
% 0.22/0.51    inference(backward_demodulation,[],[f139,f160])).
% 0.22/0.51  fof(f160,plain,(
% 0.22/0.51    k1_xboole_0 = sK5 | (spl6_2 | ~spl6_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f159,f77])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.51    inference(resolution,[],[f39,f35])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.51    inference(nnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.51  fof(f159,plain,(
% 0.22/0.51    k1_xboole_0 = sK5 | ~r1_tarski(k1_xboole_0,sK5) | (spl6_2 | ~spl6_3)),
% 0.22/0.51    inference(resolution,[],[f148,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(flattening,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    r1_tarski(sK5,k1_xboole_0) | (spl6_2 | ~spl6_3)),
% 0.22/0.51    inference(forward_demodulation,[],[f141,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f43])).
% 1.20/0.51  fof(f43,plain,(
% 1.20/0.51    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.20/0.51    inference(cnf_transformation,[],[f25])).
% 1.20/0.51  fof(f25,plain,(
% 1.20/0.51    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.20/0.51    inference(flattening,[],[f24])).
% 1.20/0.51  fof(f24,plain,(
% 1.20/0.51    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.20/0.51    inference(nnf_transformation,[],[f2])).
% 1.20/0.51  fof(f2,axiom,(
% 1.20/0.51    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.20/0.51  fof(f141,plain,(
% 1.20/0.51    r1_tarski(sK5,k2_zfmisc_1(sK3,k1_xboole_0)) | (spl6_2 | ~spl6_3)),
% 1.20/0.51    inference(backward_demodulation,[],[f76,f137])).
% 1.20/0.51  fof(f137,plain,(
% 1.20/0.51    k1_xboole_0 = sK4 | (spl6_2 | ~spl6_3)),
% 1.20/0.51    inference(resolution,[],[f136,f48])).
% 1.20/0.51  % (26066)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.20/0.51  fof(f48,plain,(
% 1.20/0.51    ( ! [X0,X1] : (~sP0(X0,X1) | k1_xboole_0 = X1) )),
% 1.20/0.51    inference(cnf_transformation,[],[f30])).
% 1.20/0.51  fof(f136,plain,(
% 1.20/0.51    sP0(sK3,sK4) | (spl6_2 | ~spl6_3)),
% 1.20/0.51    inference(subsumption_resolution,[],[f135,f93])).
% 1.20/0.51  fof(f93,plain,(
% 1.20/0.51    sP1(sK3,sK5,sK4) | ~spl6_3),
% 1.20/0.51    inference(resolution,[],[f50,f71])).
% 1.20/0.51  fof(f71,plain,(
% 1.20/0.51    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~spl6_3),
% 1.20/0.51    inference(avatar_component_clause,[],[f70])).
% 1.20/0.51  fof(f70,plain,(
% 1.20/0.51    spl6_3 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 1.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.20/0.51  fof(f50,plain,(
% 1.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 1.20/0.51    inference(cnf_transformation,[],[f18])).
% 1.20/0.51  fof(f135,plain,(
% 1.20/0.51    sP0(sK3,sK4) | ~sP1(sK3,sK5,sK4) | spl6_2),
% 1.20/0.51    inference(subsumption_resolution,[],[f134,f68])).
% 1.20/0.51  fof(f68,plain,(
% 1.20/0.51    ~v1_funct_2(sK5,sK3,sK4) | spl6_2),
% 1.20/0.51    inference(avatar_component_clause,[],[f66])).
% 1.20/0.51  fof(f66,plain,(
% 1.20/0.51    spl6_2 <=> v1_funct_2(sK5,sK3,sK4)),
% 1.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.20/0.51  fof(f134,plain,(
% 1.20/0.51    v1_funct_2(sK5,sK3,sK4) | sP0(sK3,sK4) | ~sP1(sK3,sK5,sK4)),
% 1.20/0.51    inference(trivial_inequality_removal,[],[f131])).
% 1.20/0.51  fof(f131,plain,(
% 1.20/0.51    sK3 != sK3 | v1_funct_2(sK5,sK3,sK4) | sP0(sK3,sK4) | ~sP1(sK3,sK5,sK4)),
% 1.20/0.51    inference(superposition,[],[f47,f33])).
% 1.20/0.51  fof(f33,plain,(
% 1.20/0.51    sK3 = k1_relset_1(sK3,sK4,sK5)),
% 1.20/0.51    inference(cnf_transformation,[],[f20])).
% 1.20/0.51  fof(f20,plain,(
% 1.20/0.51    (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(sK5,sK3,sK4) | ~v1_funct_1(sK5)) & sK3 = k1_relset_1(sK3,sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK5)),
% 1.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f10,f19])).
% 1.20/0.51  fof(f19,plain,(
% 1.20/0.51    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(sK5,sK3,sK4) | ~v1_funct_1(sK5)) & sK3 = k1_relset_1(sK3,sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK5))),
% 1.20/0.51    introduced(choice_axiom,[])).
% 1.20/0.51  fof(f10,plain,(
% 1.20/0.51    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 1.20/0.51    inference(flattening,[],[f9])).
% 1.20/0.51  fof(f9,plain,(
% 1.20/0.51    ? [X0,X1,X2] : (((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 1.20/0.51    inference(ennf_transformation,[],[f8])).
% 1.20/0.51  fof(f8,negated_conjecture,(
% 1.20/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.20/0.51    inference(negated_conjecture,[],[f7])).
% 1.20/0.51  fof(f7,conjecture,(
% 1.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).
% 1.20/0.51  fof(f47,plain,(
% 1.20/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) != X0 | v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 1.20/0.51    inference(cnf_transformation,[],[f29])).
% 1.20/0.51  % (26063)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.20/0.51  fof(f29,plain,(
% 1.20/0.51    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 1.20/0.51    inference(rectify,[],[f28])).
% 1.20/0.51  fof(f28,plain,(
% 1.20/0.51    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 1.20/0.51    inference(nnf_transformation,[],[f16])).
% 1.20/0.51  fof(f76,plain,(
% 1.20/0.51    r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) | ~spl6_3),
% 1.20/0.51    inference(resolution,[],[f39,f71])).
% 1.20/0.51  fof(f139,plain,(
% 1.20/0.51    ~v1_funct_2(sK5,sK3,k1_xboole_0) | (spl6_2 | ~spl6_3)),
% 1.20/0.51    inference(backward_demodulation,[],[f68,f137])).
% 1.20/0.51  fof(f146,plain,(
% 1.20/0.51    sP0(sK3,k1_xboole_0) | (spl6_2 | ~spl6_3)),
% 1.20/0.51    inference(backward_demodulation,[],[f136,f137])).
% 1.20/0.51  fof(f75,plain,(
% 1.20/0.51    spl6_1),
% 1.20/0.51    inference(avatar_split_clause,[],[f31,f62])).
% 1.20/0.51  fof(f62,plain,(
% 1.20/0.51    spl6_1 <=> v1_funct_1(sK5)),
% 1.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.20/0.51  fof(f31,plain,(
% 1.20/0.51    v1_funct_1(sK5)),
% 1.20/0.51    inference(cnf_transformation,[],[f20])).
% 1.20/0.51  fof(f74,plain,(
% 1.20/0.51    spl6_3),
% 1.20/0.51    inference(avatar_split_clause,[],[f32,f70])).
% 1.20/0.51  fof(f32,plain,(
% 1.20/0.51    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 1.20/0.51    inference(cnf_transformation,[],[f20])).
% 1.20/0.51  fof(f73,plain,(
% 1.20/0.51    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 1.20/0.51    inference(avatar_split_clause,[],[f34,f70,f66,f62])).
% 1.20/0.51  fof(f34,plain,(
% 1.20/0.51    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(sK5,sK3,sK4) | ~v1_funct_1(sK5)),
% 1.20/0.51    inference(cnf_transformation,[],[f20])).
% 1.20/0.51  % SZS output end Proof for theBenchmark
% 1.20/0.51  % (26057)------------------------------
% 1.20/0.51  % (26057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.51  % (26057)Termination reason: Refutation
% 1.20/0.51  
% 1.20/0.51  % (26057)Memory used [KB]: 6140
% 1.20/0.51  % (26057)Time elapsed: 0.099 s
% 1.20/0.51  % (26057)------------------------------
% 1.20/0.51  % (26057)------------------------------
% 1.20/0.51  % (26066)Refutation not found, incomplete strategy% (26066)------------------------------
% 1.20/0.51  % (26066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.51  % (26058)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.51  
% 1.20/0.51  % (26058)Memory used [KB]: 6140
% 1.20/0.51  % (26058)Time elapsed: 0.094 s
% 1.20/0.51  % (26058)------------------------------
% 1.20/0.51  % (26058)------------------------------
% 1.20/0.51  % (26052)Success in time 0.15 s
%------------------------------------------------------------------------------
