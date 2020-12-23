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
% DateTime   : Thu Dec  3 13:06:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 413 expanded)
%              Number of leaves         :   26 ( 146 expanded)
%              Depth                    :   15
%              Number of atoms          :  529 (2432 expanded)
%              Number of equality atoms :  137 ( 485 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f777,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f338,f422,f544,f585,f597,f628,f749,f750,f755,f759,f776])).

fof(f776,plain,
    ( ~ spl8_27
    | spl8_16
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f774,f415,f326,f582])).

fof(f582,plain,
    ( spl8_27
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f326,plain,
    ( spl8_16
  <=> sK5 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f415,plain,
    ( spl8_21
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f774,plain,
    ( k1_xboole_0 != sK6
    | spl8_16
    | ~ spl8_21 ),
    inference(backward_demodulation,[],[f327,f417])).

fof(f417,plain,
    ( k1_xboole_0 = sK5
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f415])).

fof(f327,plain,
    ( sK5 != sK6
    | spl8_16 ),
    inference(avatar_component_clause,[],[f326])).

fof(f759,plain,(
    spl8_28 ),
    inference(avatar_split_clause,[],[f52,f752])).

fof(f752,plain,
    ( spl8_28
  <=> v1_funct_2(sK6,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f52,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6)
    & ! [X4] :
        ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
        | ~ m1_subset_1(X4,sK3) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f17,f37,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK3,sK4,sK5,X3)
          & ! [X4] :
              ( k1_funct_1(X3,X4) = k1_funct_1(sK5,X4)
              | ~ m1_subset_1(X4,sK3) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
          & v1_funct_2(X3,sK3,sK4)
          & v1_funct_1(X3) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

% (31791)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f37,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK3,sK4,sK5,X3)
        & ! [X4] :
            ( k1_funct_1(X3,X4) = k1_funct_1(sK5,X4)
            | ~ m1_subset_1(X4,sK3) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
        & v1_funct_2(X3,sK3,sK4)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK3,sK4,sK5,sK6)
      & ! [X4] :
          ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
          | ~ m1_subset_1(X4,sK3) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

fof(f755,plain,
    ( spl8_20
    | spl8_19
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f475,f752,f360,f366])).

fof(f366,plain,
    ( spl8_20
  <=> sK3 = k1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f360,plain,
    ( spl8_19
  <=> sP0(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f475,plain,
    ( ~ v1_funct_2(sK6,sK3,sK4)
    | sP0(sK3,sK4)
    | sK3 = k1_relat_1(sK6) ),
    inference(resolution,[],[f53,f197])).

fof(f197,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f195,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f27,f34,f33,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f33,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f195,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | ~ sP1(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f72,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

% (31793)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f53,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f38])).

fof(f750,plain,
    ( spl8_18
    | spl8_19 ),
    inference(avatar_split_clause,[],[f738,f360,f356])).

fof(f356,plain,
    ( spl8_18
  <=> sK3 = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f738,plain,
    ( sP0(sK3,sK4)
    | sK3 = k1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f735,f49])).

fof(f49,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f735,plain,
    ( ~ v1_funct_2(sK5,sK3,sK4)
    | sP0(sK3,sK4)
    | sK3 = k1_relat_1(sK5) ),
    inference(resolution,[],[f50,f197])).

fof(f50,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f38])).

fof(f749,plain,(
    ~ spl8_16 ),
    inference(avatar_contradiction_clause,[],[f748])).

fof(f748,plain,
    ( $false
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f698,f160])).

fof(f160,plain,(
    r2_relset_1(sK3,sK4,sK5,sK5) ),
    inference(resolution,[],[f84,f50])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f698,plain,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK5)
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f55,f328])).

fof(f328,plain,
    ( sK5 = sK6
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f326])).

fof(f55,plain,(
    ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f628,plain,
    ( spl8_16
    | spl8_17
    | ~ spl8_18
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f538,f366,f356,f335,f326])).

fof(f335,plain,
    ( spl8_17
  <=> m1_subset_1(sK7(sK5,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f538,plain,
    ( sK5 = sK6
    | spl8_17
    | ~ spl8_18
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f537,f490])).

fof(f490,plain,
    ( r1_tarski(sK3,sK3)
    | ~ spl8_18 ),
    inference(resolution,[],[f456,f99])).

fof(f99,plain,(
    v4_relat_1(sK5,sK3) ),
    inference(resolution,[],[f68,f50])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f456,plain,
    ( ! [X2] :
        ( ~ v4_relat_1(sK5,X2)
        | r1_tarski(sK3,X2) )
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f451,f89])).

fof(f89,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f66,f50])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f451,plain,
    ( ! [X2] :
        ( r1_tarski(sK3,X2)
        | ~ v4_relat_1(sK5,X2)
        | ~ v1_relat_1(sK5) )
    | ~ spl8_18 ),
    inference(superposition,[],[f60,f358])).

fof(f358,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f356])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f537,plain,
    ( sK5 = sK6
    | ~ r1_tarski(sK3,sK3)
    | spl8_17
    | ~ spl8_18
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f536,f90])).

fof(f90,plain,(
    v1_relat_1(sK6) ),
    inference(resolution,[],[f66,f53])).

fof(f536,plain,
    ( ~ v1_relat_1(sK6)
    | sK5 = sK6
    | ~ r1_tarski(sK3,sK3)
    | spl8_17
    | ~ spl8_18
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f535,f51])).

fof(f51,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f535,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | sK5 = sK6
    | ~ r1_tarski(sK3,sK3)
    | spl8_17
    | ~ spl8_18
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f520,f368])).

fof(f368,plain,
    ( sK3 = k1_relat_1(sK6)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f366])).

fof(f520,plain,
    ( sK3 != k1_relat_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | sK5 = sK6
    | ~ r1_tarski(sK3,sK3)
    | spl8_17
    | ~ spl8_18 ),
    inference(resolution,[],[f508,f337])).

fof(f337,plain,
    ( ~ m1_subset_1(sK7(sK5,sK6),sK3)
    | spl8_17 ),
    inference(avatar_component_clause,[],[f335])).

fof(f508,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK7(sK5,X0),X1)
        | k1_relat_1(X0) != sK3
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | sK5 = X0
        | ~ r1_tarski(sK3,X1) )
    | ~ spl8_18 ),
    inference(resolution,[],[f454,f156])).

fof(f156,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X4,X6)
      | m1_subset_1(X4,X5)
      | ~ r1_tarski(X6,X5) ) ),
    inference(resolution,[],[f78,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f454,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(sK5,X0),sK3)
        | sK5 = X0
        | k1_relat_1(X0) != sK3
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f453,f89])).

fof(f453,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(sK5,X0),sK3)
        | sK5 = X0
        | k1_relat_1(X0) != sK3
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK5) )
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f449,f48])).

fof(f48,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f449,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(sK5,X0),sK3)
        | sK5 = X0
        | k1_relat_1(X0) != sK3
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(sK5)
        | ~ v1_relat_1(sK5) )
    | ~ spl8_18 ),
    inference(superposition,[],[f58,f358])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1))
            & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f19,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1))
        & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f597,plain,
    ( ~ spl8_19
    | ~ spl8_22 ),
    inference(avatar_contradiction_clause,[],[f596])).

fof(f596,plain,
    ( $false
    | ~ spl8_19
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f588,f83])).

fof(f83,plain,(
    ! [X1] : ~ sP0(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f588,plain,
    ( sP0(k1_xboole_0,k1_xboole_0)
    | ~ spl8_19
    | ~ spl8_22 ),
    inference(backward_demodulation,[],[f389,f421])).

fof(f421,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f419])).

fof(f419,plain,
    ( spl8_22
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f389,plain,
    ( sP0(sK3,k1_xboole_0)
    | ~ spl8_19 ),
    inference(backward_demodulation,[],[f362,f370])).

fof(f370,plain,
    ( k1_xboole_0 = sK4
    | ~ spl8_19 ),
    inference(resolution,[],[f362,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f362,plain,
    ( sP0(sK3,sK4)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f360])).

fof(f585,plain,
    ( spl8_27
    | spl8_22
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f580,f360,f419,f582])).

fof(f580,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK6
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f579,f568])).

fof(f568,plain,
    ( v1_funct_2(sK6,sK3,k1_xboole_0)
    | ~ spl8_19 ),
    inference(backward_demodulation,[],[f52,f370])).

fof(f579,plain,
    ( ~ v1_funct_2(sK6,sK3,k1_xboole_0)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK6
    | ~ spl8_19 ),
    inference(resolution,[],[f574,f82])).

fof(f82,plain,(
    ! [X2,X0] :
      ( ~ sP2(X0,k1_xboole_0,X2)
      | ~ v1_funct_2(X0,X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ v1_funct_2(X0,X2,X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X0,X2,X1)
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | ~ v1_funct_2(X0,X2,X1) ) )
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | ~ v1_funct_2(X2,X0,X1) ) )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f574,plain,
    ( sP2(sK6,k1_xboole_0,sK3)
    | ~ spl8_19 ),
    inference(backward_demodulation,[],[f146,f370])).

fof(f146,plain,(
    sP2(sK6,sK4,sK3) ),
    inference(resolution,[],[f77,f53])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f544,plain,
    ( ~ spl8_18
    | spl8_15
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f543,f366,f322,f356])).

fof(f322,plain,
    ( spl8_15
  <=> k1_relat_1(sK6) = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f543,plain,
    ( sK3 != k1_relat_1(sK5)
    | spl8_15
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f324,f368])).

fof(f324,plain,
    ( k1_relat_1(sK6) != k1_relat_1(sK5)
    | spl8_15 ),
    inference(avatar_component_clause,[],[f322])).

fof(f422,plain,
    ( spl8_21
    | spl8_22
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f413,f360,f419,f415])).

fof(f413,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f412,f371])).

fof(f371,plain,
    ( v1_funct_2(sK5,sK3,k1_xboole_0)
    | ~ spl8_19 ),
    inference(backward_demodulation,[],[f49,f370])).

fof(f412,plain,
    ( ~ v1_funct_2(sK5,sK3,k1_xboole_0)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | ~ spl8_19 ),
    inference(resolution,[],[f383,f82])).

fof(f383,plain,
    ( sP2(sK5,k1_xboole_0,sK3)
    | ~ spl8_19 ),
    inference(backward_demodulation,[],[f145,f370])).

fof(f145,plain,(
    sP2(sK5,sK4,sK3) ),
    inference(resolution,[],[f77,f50])).

fof(f338,plain,
    ( ~ spl8_17
    | ~ spl8_15
    | spl8_16 ),
    inference(avatar_split_clause,[],[f333,f326,f322,f335])).

fof(f333,plain,
    ( sK5 = sK6
    | k1_relat_1(sK6) != k1_relat_1(sK5)
    | ~ m1_subset_1(sK7(sK5,sK6),sK3) ),
    inference(subsumption_resolution,[],[f332,f89])).

fof(f332,plain,
    ( sK5 = sK6
    | k1_relat_1(sK6) != k1_relat_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ m1_subset_1(sK7(sK5,sK6),sK3) ),
    inference(subsumption_resolution,[],[f331,f48])).

fof(f331,plain,
    ( sK5 = sK6
    | k1_relat_1(sK6) != k1_relat_1(sK5)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ m1_subset_1(sK7(sK5,sK6),sK3) ),
    inference(equality_resolution,[],[f312])).

fof(f312,plain,(
    ! [X0] :
      ( k1_funct_1(sK5,sK7(X0,sK6)) != k1_funct_1(X0,sK7(X0,sK6))
      | sK6 = X0
      | k1_relat_1(X0) != k1_relat_1(sK6)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(sK7(X0,sK6),sK3) ) ),
    inference(subsumption_resolution,[],[f311,f90])).

fof(f311,plain,(
    ! [X0] :
      ( k1_funct_1(sK5,sK7(X0,sK6)) != k1_funct_1(X0,sK7(X0,sK6))
      | sK6 = X0
      | k1_relat_1(X0) != k1_relat_1(sK6)
      | ~ v1_relat_1(sK6)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(sK7(X0,sK6),sK3) ) ),
    inference(subsumption_resolution,[],[f306,f51])).

fof(f306,plain,(
    ! [X0] :
      ( k1_funct_1(sK5,sK7(X0,sK6)) != k1_funct_1(X0,sK7(X0,sK6))
      | sK6 = X0
      | k1_relat_1(X0) != k1_relat_1(sK6)
      | ~ v1_funct_1(sK6)
      | ~ v1_relat_1(sK6)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(sK7(X0,sK6),sK3) ) ),
    inference(superposition,[],[f59,f54])).

fof(f54,plain,(
    ! [X4] :
      ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
      | ~ m1_subset_1(X4,sK3) ) ),
    inference(cnf_transformation,[],[f38])).

% (31796)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f59,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1))
      | X0 = X1
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:26:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (31790)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (31790)Refutation not found, incomplete strategy% (31790)------------------------------
% 0.21/0.51  % (31790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31790)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31790)Memory used [KB]: 10618
% 0.21/0.51  % (31790)Time elapsed: 0.080 s
% 0.21/0.51  % (31790)------------------------------
% 0.21/0.51  % (31790)------------------------------
% 0.21/0.52  % (31794)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (31802)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.54  % (31794)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f777,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f338,f422,f544,f585,f597,f628,f749,f750,f755,f759,f776])).
% 0.21/0.54  fof(f776,plain,(
% 0.21/0.54    ~spl8_27 | spl8_16 | ~spl8_21),
% 0.21/0.54    inference(avatar_split_clause,[],[f774,f415,f326,f582])).
% 0.21/0.54  fof(f582,plain,(
% 0.21/0.54    spl8_27 <=> k1_xboole_0 = sK6),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.21/0.54  fof(f326,plain,(
% 0.21/0.54    spl8_16 <=> sK5 = sK6),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.21/0.54  fof(f415,plain,(
% 0.21/0.54    spl8_21 <=> k1_xboole_0 = sK5),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.21/0.54  fof(f774,plain,(
% 0.21/0.54    k1_xboole_0 != sK6 | (spl8_16 | ~spl8_21)),
% 0.21/0.54    inference(backward_demodulation,[],[f327,f417])).
% 0.21/0.54  fof(f417,plain,(
% 0.21/0.54    k1_xboole_0 = sK5 | ~spl8_21),
% 0.21/0.54    inference(avatar_component_clause,[],[f415])).
% 0.21/0.54  fof(f327,plain,(
% 0.21/0.54    sK5 != sK6 | spl8_16),
% 0.21/0.54    inference(avatar_component_clause,[],[f326])).
% 0.21/0.54  fof(f759,plain,(
% 0.21/0.54    spl8_28),
% 0.21/0.54    inference(avatar_split_clause,[],[f52,f752])).
% 0.21/0.54  fof(f752,plain,(
% 0.21/0.54    spl8_28 <=> v1_funct_2(sK6,sK3,sK4)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    v1_funct_2(sK6,sK3,sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    (~r2_relset_1(sK3,sK4,sK5,sK6) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~m1_subset_1(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f17,f37,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK5,X4) | ~m1_subset_1(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  % (31791)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK5,X4) | ~m1_subset_1(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) => (~r2_relset_1(sK3,sK4,sK5,sK6) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~m1_subset_1(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.54    inference(flattening,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.21/0.54    inference(negated_conjecture,[],[f14])).
% 0.21/0.54  fof(f14,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).
% 0.21/0.54  fof(f755,plain,(
% 0.21/0.54    spl8_20 | spl8_19 | ~spl8_28),
% 0.21/0.54    inference(avatar_split_clause,[],[f475,f752,f360,f366])).
% 0.21/0.54  fof(f366,plain,(
% 0.21/0.54    spl8_20 <=> sK3 = k1_relat_1(sK6)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.21/0.54  fof(f360,plain,(
% 0.21/0.54    spl8_19 <=> sP0(sK3,sK4)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.21/0.54  fof(f475,plain,(
% 0.21/0.54    ~v1_funct_2(sK6,sK3,sK4) | sP0(sK3,sK4) | sK3 = k1_relat_1(sK6)),
% 0.21/0.54    inference(resolution,[],[f53,f197])).
% 0.21/0.54  fof(f197,plain,(
% 0.21/0.54    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | k1_relat_1(X5) = X3) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f195,f76])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(definition_folding,[],[f27,f34,f33,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(flattening,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.54  fof(f195,plain,(
% 0.21/0.54    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | ~sP1(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.54    inference(superposition,[],[f72,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  % (31793)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 0.21/0.54    inference(rectify,[],[f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f33])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f750,plain,(
% 0.21/0.54    spl8_18 | spl8_19),
% 0.21/0.54    inference(avatar_split_clause,[],[f738,f360,f356])).
% 0.21/0.54  fof(f356,plain,(
% 0.21/0.54    spl8_18 <=> sK3 = k1_relat_1(sK5)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.54  fof(f738,plain,(
% 0.21/0.54    sP0(sK3,sK4) | sK3 = k1_relat_1(sK5)),
% 0.21/0.54    inference(subsumption_resolution,[],[f735,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    v1_funct_2(sK5,sK3,sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f735,plain,(
% 0.21/0.54    ~v1_funct_2(sK5,sK3,sK4) | sP0(sK3,sK4) | sK3 = k1_relat_1(sK5)),
% 0.21/0.54    inference(resolution,[],[f50,f197])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f749,plain,(
% 0.21/0.54    ~spl8_16),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f748])).
% 0.21/0.54  fof(f748,plain,(
% 0.21/0.54    $false | ~spl8_16),
% 0.21/0.54    inference(subsumption_resolution,[],[f698,f160])).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    r2_relset_1(sK3,sK4,sK5,sK5)),
% 0.21/0.54    inference(resolution,[],[f84,f50])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.21/0.54    inference(condensation,[],[f79])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(flattening,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.21/0.54  fof(f698,plain,(
% 0.21/0.54    ~r2_relset_1(sK3,sK4,sK5,sK5) | ~spl8_16),
% 0.21/0.54    inference(forward_demodulation,[],[f55,f328])).
% 0.21/0.54  fof(f328,plain,(
% 0.21/0.54    sK5 = sK6 | ~spl8_16),
% 0.21/0.54    inference(avatar_component_clause,[],[f326])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ~r2_relset_1(sK3,sK4,sK5,sK6)),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f628,plain,(
% 0.21/0.54    spl8_16 | spl8_17 | ~spl8_18 | ~spl8_20),
% 0.21/0.54    inference(avatar_split_clause,[],[f538,f366,f356,f335,f326])).
% 0.21/0.54  fof(f335,plain,(
% 0.21/0.54    spl8_17 <=> m1_subset_1(sK7(sK5,sK6),sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.54  fof(f538,plain,(
% 0.21/0.54    sK5 = sK6 | (spl8_17 | ~spl8_18 | ~spl8_20)),
% 0.21/0.54    inference(subsumption_resolution,[],[f537,f490])).
% 0.21/0.54  fof(f490,plain,(
% 0.21/0.54    r1_tarski(sK3,sK3) | ~spl8_18),
% 0.21/0.54    inference(resolution,[],[f456,f99])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    v4_relat_1(sK5,sK3)),
% 0.21/0.54    inference(resolution,[],[f68,f50])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.54  fof(f456,plain,(
% 0.21/0.54    ( ! [X2] : (~v4_relat_1(sK5,X2) | r1_tarski(sK3,X2)) ) | ~spl8_18),
% 0.21/0.54    inference(subsumption_resolution,[],[f451,f89])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    v1_relat_1(sK5)),
% 0.21/0.54    inference(resolution,[],[f66,f50])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.54  fof(f451,plain,(
% 0.21/0.54    ( ! [X2] : (r1_tarski(sK3,X2) | ~v4_relat_1(sK5,X2) | ~v1_relat_1(sK5)) ) | ~spl8_18),
% 0.21/0.54    inference(superposition,[],[f60,f358])).
% 0.21/0.54  fof(f358,plain,(
% 0.21/0.54    sK3 = k1_relat_1(sK5) | ~spl8_18),
% 0.21/0.54    inference(avatar_component_clause,[],[f356])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.54  fof(f537,plain,(
% 0.21/0.54    sK5 = sK6 | ~r1_tarski(sK3,sK3) | (spl8_17 | ~spl8_18 | ~spl8_20)),
% 0.21/0.54    inference(subsumption_resolution,[],[f536,f90])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    v1_relat_1(sK6)),
% 0.21/0.54    inference(resolution,[],[f66,f53])).
% 0.21/0.54  fof(f536,plain,(
% 0.21/0.54    ~v1_relat_1(sK6) | sK5 = sK6 | ~r1_tarski(sK3,sK3) | (spl8_17 | ~spl8_18 | ~spl8_20)),
% 0.21/0.54    inference(subsumption_resolution,[],[f535,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    v1_funct_1(sK6)),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f535,plain,(
% 0.21/0.54    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | sK5 = sK6 | ~r1_tarski(sK3,sK3) | (spl8_17 | ~spl8_18 | ~spl8_20)),
% 0.21/0.54    inference(subsumption_resolution,[],[f520,f368])).
% 0.21/0.54  fof(f368,plain,(
% 0.21/0.54    sK3 = k1_relat_1(sK6) | ~spl8_20),
% 0.21/0.54    inference(avatar_component_clause,[],[f366])).
% 0.21/0.54  fof(f520,plain,(
% 0.21/0.54    sK3 != k1_relat_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | sK5 = sK6 | ~r1_tarski(sK3,sK3) | (spl8_17 | ~spl8_18)),
% 0.21/0.54    inference(resolution,[],[f508,f337])).
% 0.21/0.54  fof(f337,plain,(
% 0.21/0.54    ~m1_subset_1(sK7(sK5,sK6),sK3) | spl8_17),
% 0.21/0.54    inference(avatar_component_clause,[],[f335])).
% 0.21/0.54  fof(f508,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(sK7(sK5,X0),X1) | k1_relat_1(X0) != sK3 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK5 = X0 | ~r1_tarski(sK3,X1)) ) | ~spl8_18),
% 0.21/0.54    inference(resolution,[],[f454,f156])).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    ( ! [X6,X4,X5] : (~r2_hidden(X4,X6) | m1_subset_1(X4,X5) | ~r1_tarski(X6,X5)) )),
% 0.21/0.54    inference(resolution,[],[f78,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.54    inference(nnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.54  fof(f454,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK7(sK5,X0),sK3) | sK5 = X0 | k1_relat_1(X0) != sK3 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl8_18),
% 0.21/0.54    inference(subsumption_resolution,[],[f453,f89])).
% 0.21/0.54  fof(f453,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK7(sK5,X0),sK3) | sK5 = X0 | k1_relat_1(X0) != sK3 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK5)) ) | ~spl8_18),
% 0.21/0.54    inference(subsumption_resolution,[],[f449,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    v1_funct_1(sK5)),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f449,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK7(sK5,X0),sK3) | sK5 = X0 | k1_relat_1(X0) != sK3 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)) ) | ~spl8_18),
% 0.21/0.54    inference(superposition,[],[f58,f358])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),k1_relat_1(X0)) | X0 = X1 | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f19,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) => X0 = X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 0.21/0.54  fof(f597,plain,(
% 0.21/0.54    ~spl8_19 | ~spl8_22),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f596])).
% 0.21/0.54  fof(f596,plain,(
% 0.21/0.54    $false | (~spl8_19 | ~spl8_22)),
% 0.21/0.54    inference(subsumption_resolution,[],[f588,f83])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ( ! [X1] : (~sP0(k1_xboole_0,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f75])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f32])).
% 0.21/0.54  fof(f588,plain,(
% 0.21/0.54    sP0(k1_xboole_0,k1_xboole_0) | (~spl8_19 | ~spl8_22)),
% 0.21/0.54    inference(backward_demodulation,[],[f389,f421])).
% 0.21/0.54  fof(f421,plain,(
% 0.21/0.54    k1_xboole_0 = sK3 | ~spl8_22),
% 0.21/0.54    inference(avatar_component_clause,[],[f419])).
% 0.21/0.54  fof(f419,plain,(
% 0.21/0.54    spl8_22 <=> k1_xboole_0 = sK3),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.21/0.54  fof(f389,plain,(
% 0.21/0.54    sP0(sK3,k1_xboole_0) | ~spl8_19),
% 0.21/0.54    inference(backward_demodulation,[],[f362,f370])).
% 0.21/0.54  fof(f370,plain,(
% 0.21/0.54    k1_xboole_0 = sK4 | ~spl8_19),
% 0.21/0.54    inference(resolution,[],[f362,f74])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~sP0(X0,X1) | k1_xboole_0 = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f47])).
% 0.21/0.54  fof(f362,plain,(
% 0.21/0.54    sP0(sK3,sK4) | ~spl8_19),
% 0.21/0.54    inference(avatar_component_clause,[],[f360])).
% 0.21/0.54  fof(f585,plain,(
% 0.21/0.54    spl8_27 | spl8_22 | ~spl8_19),
% 0.21/0.54    inference(avatar_split_clause,[],[f580,f360,f419,f582])).
% 0.21/0.54  fof(f580,plain,(
% 0.21/0.54    k1_xboole_0 = sK3 | k1_xboole_0 = sK6 | ~spl8_19),
% 0.21/0.54    inference(subsumption_resolution,[],[f579,f568])).
% 0.21/0.54  fof(f568,plain,(
% 0.21/0.54    v1_funct_2(sK6,sK3,k1_xboole_0) | ~spl8_19),
% 0.21/0.54    inference(backward_demodulation,[],[f52,f370])).
% 0.21/0.54  fof(f579,plain,(
% 0.21/0.54    ~v1_funct_2(sK6,sK3,k1_xboole_0) | k1_xboole_0 = sK3 | k1_xboole_0 = sK6 | ~spl8_19),
% 0.21/0.54    inference(resolution,[],[f574,f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X2,X0] : (~sP2(X0,k1_xboole_0,X2) | ~v1_funct_2(X0,X2,k1_xboole_0) | k1_xboole_0 = X2 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(equality_resolution,[],[f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1))) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(X0,X1,X2))),
% 0.21/0.54    inference(rectify,[],[f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f34])).
% 0.21/0.54  fof(f574,plain,(
% 0.21/0.54    sP2(sK6,k1_xboole_0,sK3) | ~spl8_19),
% 0.21/0.54    inference(backward_demodulation,[],[f146,f370])).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    sP2(sK6,sK4,sK3)),
% 0.21/0.54    inference(resolution,[],[f77,f53])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X2,X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f544,plain,(
% 0.21/0.54    ~spl8_18 | spl8_15 | ~spl8_20),
% 0.21/0.54    inference(avatar_split_clause,[],[f543,f366,f322,f356])).
% 0.21/0.54  fof(f322,plain,(
% 0.21/0.54    spl8_15 <=> k1_relat_1(sK6) = k1_relat_1(sK5)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.54  fof(f543,plain,(
% 0.21/0.54    sK3 != k1_relat_1(sK5) | (spl8_15 | ~spl8_20)),
% 0.21/0.54    inference(forward_demodulation,[],[f324,f368])).
% 0.21/0.54  fof(f324,plain,(
% 0.21/0.54    k1_relat_1(sK6) != k1_relat_1(sK5) | spl8_15),
% 0.21/0.54    inference(avatar_component_clause,[],[f322])).
% 0.21/0.54  fof(f422,plain,(
% 0.21/0.54    spl8_21 | spl8_22 | ~spl8_19),
% 0.21/0.54    inference(avatar_split_clause,[],[f413,f360,f419,f415])).
% 0.21/0.54  fof(f413,plain,(
% 0.21/0.54    k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | ~spl8_19),
% 0.21/0.54    inference(subsumption_resolution,[],[f412,f371])).
% 0.21/0.54  fof(f371,plain,(
% 0.21/0.54    v1_funct_2(sK5,sK3,k1_xboole_0) | ~spl8_19),
% 0.21/0.54    inference(backward_demodulation,[],[f49,f370])).
% 0.21/0.54  fof(f412,plain,(
% 0.21/0.54    ~v1_funct_2(sK5,sK3,k1_xboole_0) | k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | ~spl8_19),
% 0.21/0.54    inference(resolution,[],[f383,f82])).
% 0.21/0.54  fof(f383,plain,(
% 0.21/0.54    sP2(sK5,k1_xboole_0,sK3) | ~spl8_19),
% 0.21/0.54    inference(backward_demodulation,[],[f145,f370])).
% 0.21/0.54  fof(f145,plain,(
% 0.21/0.54    sP2(sK5,sK4,sK3)),
% 0.21/0.54    inference(resolution,[],[f77,f50])).
% 0.21/0.54  fof(f338,plain,(
% 0.21/0.54    ~spl8_17 | ~spl8_15 | spl8_16),
% 0.21/0.54    inference(avatar_split_clause,[],[f333,f326,f322,f335])).
% 0.21/0.54  fof(f333,plain,(
% 0.21/0.54    sK5 = sK6 | k1_relat_1(sK6) != k1_relat_1(sK5) | ~m1_subset_1(sK7(sK5,sK6),sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f332,f89])).
% 0.21/0.54  fof(f332,plain,(
% 0.21/0.54    sK5 = sK6 | k1_relat_1(sK6) != k1_relat_1(sK5) | ~v1_relat_1(sK5) | ~m1_subset_1(sK7(sK5,sK6),sK3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f331,f48])).
% 0.21/0.54  fof(f331,plain,(
% 0.21/0.54    sK5 = sK6 | k1_relat_1(sK6) != k1_relat_1(sK5) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | ~m1_subset_1(sK7(sK5,sK6),sK3)),
% 0.21/0.54    inference(equality_resolution,[],[f312])).
% 0.21/0.54  fof(f312,plain,(
% 0.21/0.54    ( ! [X0] : (k1_funct_1(sK5,sK7(X0,sK6)) != k1_funct_1(X0,sK7(X0,sK6)) | sK6 = X0 | k1_relat_1(X0) != k1_relat_1(sK6) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~m1_subset_1(sK7(X0,sK6),sK3)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f311,f90])).
% 0.21/0.54  fof(f311,plain,(
% 0.21/0.54    ( ! [X0] : (k1_funct_1(sK5,sK7(X0,sK6)) != k1_funct_1(X0,sK7(X0,sK6)) | sK6 = X0 | k1_relat_1(X0) != k1_relat_1(sK6) | ~v1_relat_1(sK6) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~m1_subset_1(sK7(X0,sK6),sK3)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f306,f51])).
% 0.21/0.54  fof(f306,plain,(
% 0.21/0.54    ( ! [X0] : (k1_funct_1(sK5,sK7(X0,sK6)) != k1_funct_1(X0,sK7(X0,sK6)) | sK6 = X0 | k1_relat_1(X0) != k1_relat_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~m1_subset_1(sK7(X0,sK6),sK3)) )),
% 0.21/0.54    inference(superposition,[],[f59,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~m1_subset_1(X4,sK3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  % (31796)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1)) | X0 = X1 | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (31794)------------------------------
% 0.21/0.54  % (31794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31794)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (31794)Memory used [KB]: 6396
% 0.21/0.54  % (31794)Time elapsed: 0.105 s
% 0.21/0.54  % (31794)------------------------------
% 0.21/0.54  % (31794)------------------------------
% 0.21/0.54  % (31789)Success in time 0.178 s
%------------------------------------------------------------------------------
