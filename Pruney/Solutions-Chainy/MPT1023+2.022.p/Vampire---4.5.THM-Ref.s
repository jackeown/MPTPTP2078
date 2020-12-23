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
% DateTime   : Thu Dec  3 13:06:10 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 350 expanded)
%              Number of leaves         :   25 ( 119 expanded)
%              Depth                    :   15
%              Number of atoms          :  517 (2016 expanded)
%              Number of equality atoms :  148 ( 396 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f495,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f258,f406,f412,f435,f449,f450,f456,f462,f488])).

fof(f488,plain,
    ( ~ spl8_13
    | spl8_9
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f479,f295,f286,f311])).

fof(f311,plain,
    ( spl8_13
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f286,plain,
    ( spl8_9
  <=> sK5 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f295,plain,
    ( spl8_11
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f479,plain,
    ( k1_xboole_0 != sK6
    | spl8_9
    | ~ spl8_11 ),
    inference(backward_demodulation,[],[f287,f297])).

fof(f297,plain,
    ( k1_xboole_0 = sK5
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f295])).

fof(f287,plain,
    ( sK5 != sK6
    | spl8_9 ),
    inference(avatar_component_clause,[],[f286])).

fof(f462,plain,
    ( spl8_13
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f461,f202,f311])).

fof(f202,plain,
    ( spl8_6
  <=> sP0(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f461,plain,
    ( k1_xboole_0 = sK6
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f459,f89])).

fof(f89,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f59,f53])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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

fof(f459,plain,
    ( k1_xboole_0 = sK6
    | ~ r1_tarski(k1_xboole_0,sK6)
    | ~ spl8_6 ),
    inference(resolution,[],[f235,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f235,plain,
    ( r1_tarski(sK6,k1_xboole_0)
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f220,f79])).

fof(f79,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f37])).

% (13727)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f37,plain,(
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

fof(f220,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK3,k1_xboole_0))
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f88,f213])).

fof(f213,plain,
    ( k1_xboole_0 = sK4
    | ~ spl8_6 ),
    inference(resolution,[],[f204,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f204,plain,
    ( sP0(sK3,sK4)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f202])).

fof(f88,plain,(
    r1_tarski(sK6,k2_zfmisc_1(sK3,sK4)) ),
    inference(resolution,[],[f59,f50])).

fof(f50,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f14,f30,f29])).

fof(f29,plain,
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

fof(f30,plain,
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

% (13717)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f456,plain,
    ( spl8_11
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f455,f202,f295])).

fof(f455,plain,
    ( k1_xboole_0 = sK5
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f453,f89])).

fof(f453,plain,
    ( k1_xboole_0 = sK5
    | ~ r1_tarski(k1_xboole_0,sK5)
    | ~ spl8_6 ),
    inference(resolution,[],[f234,f58])).

fof(f234,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f219,f79])).

fof(f219,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK3,k1_xboole_0))
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f87,f213])).

fof(f87,plain,(
    r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) ),
    inference(resolution,[],[f59,f47])).

fof(f47,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f31])).

fof(f450,plain,(
    spl8_21 ),
    inference(avatar_split_clause,[],[f49,f446])).

% (13721)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f446,plain,
    ( spl8_21
  <=> v1_funct_2(sK6,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f49,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f449,plain,
    ( spl8_7
    | spl8_6
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f264,f446,f202,f208])).

fof(f208,plain,
    ( spl8_7
  <=> sK3 = k1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f264,plain,
    ( ~ v1_funct_2(sK6,sK3,sK4)
    | sP0(sK3,sK4)
    | sK3 = k1_relat_1(sK6) ),
    inference(resolution,[],[f50,f184])).

fof(f184,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f182,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f20,f27,f26,f25])).

fof(f26,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f182,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | ~ sP1(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f68,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f435,plain,(
    ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f434])).

fof(f434,plain,
    ( $false
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f416,f168])).

fof(f168,plain,(
    r2_relset_1(sK3,sK4,sK5,sK5) ),
    inference(resolution,[],[f86,f47])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f416,plain,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK5)
    | ~ spl8_9 ),
    inference(backward_demodulation,[],[f52,f288])).

fof(f288,plain,
    ( sK5 = sK6
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f286])).

fof(f52,plain,(
    ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f31])).

fof(f412,plain,
    ( spl8_9
    | ~ spl8_5
    | ~ spl8_7
    | spl8_20 ),
    inference(avatar_split_clause,[],[f411,f403,f208,f198,f286])).

fof(f198,plain,
    ( spl8_5
  <=> sK3 = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f403,plain,
    ( spl8_20
  <=> m1_subset_1(sK7(sK6,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f411,plain,
    ( sK5 = sK6
    | ~ spl8_5
    | ~ spl8_7
    | spl8_20 ),
    inference(subsumption_resolution,[],[f410,f77])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f410,plain,
    ( sK5 = sK6
    | ~ r1_tarski(sK3,sK3)
    | ~ spl8_5
    | ~ spl8_7
    | spl8_20 ),
    inference(subsumption_resolution,[],[f409,f91])).

fof(f91,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f64,f47])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f409,plain,
    ( ~ v1_relat_1(sK5)
    | sK5 = sK6
    | ~ r1_tarski(sK3,sK3)
    | ~ spl8_5
    | ~ spl8_7
    | spl8_20 ),
    inference(subsumption_resolution,[],[f408,f45])).

fof(f45,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f408,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | sK5 = sK6
    | ~ r1_tarski(sK3,sK3)
    | ~ spl8_5
    | ~ spl8_7
    | spl8_20 ),
    inference(subsumption_resolution,[],[f407,f200])).

fof(f200,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f198])).

fof(f407,plain,
    ( sK3 != k1_relat_1(sK5)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | sK5 = sK6
    | ~ r1_tarski(sK3,sK3)
    | ~ spl8_7
    | spl8_20 ),
    inference(resolution,[],[f405,f326])).

fof(f326,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK7(sK6,X0),X1)
        | k1_relat_1(X0) != sK3
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | sK6 = X0
        | ~ r1_tarski(sK3,X1) )
    | ~ spl8_7 ),
    inference(resolution,[],[f321,f148])).

fof(f148,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X4,X6)
      | m1_subset_1(X4,X5)
      | ~ r1_tarski(X6,X5) ) ),
    inference(resolution,[],[f74,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f321,plain,
    ( ! [X1] :
        ( r2_hidden(sK7(sK6,X1),sK3)
        | sK6 = X1
        | k1_relat_1(X1) != sK3
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f320,f92])).

fof(f92,plain,(
    v1_relat_1(sK6) ),
    inference(resolution,[],[f64,f50])).

fof(f320,plain,
    ( ! [X1] :
        ( r2_hidden(sK7(sK6,X1),sK3)
        | sK6 = X1
        | k1_relat_1(X1) != sK3
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(sK6) )
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f317,f48])).

fof(f48,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f31])).

fof(f317,plain,
    ( ! [X1] :
        ( r2_hidden(sK7(sK6,X1),sK3)
        | sK6 = X1
        | k1_relat_1(X1) != sK3
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(sK6)
        | ~ v1_relat_1(sK6) )
    | ~ spl8_7 ),
    inference(superposition,[],[f54,f210])).

fof(f210,plain,
    ( sK3 = k1_relat_1(sK6)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f208])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1))
            & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f16,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1))
        & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f405,plain,
    ( ~ m1_subset_1(sK7(sK6,sK5),sK3)
    | spl8_20 ),
    inference(avatar_component_clause,[],[f403])).

fof(f406,plain,
    ( ~ spl8_20
    | spl8_9
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f401,f208,f198,f286,f403])).

fof(f401,plain,
    ( sK5 = sK6
    | ~ m1_subset_1(sK7(sK6,sK5),sK3)
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f400,f91])).

fof(f400,plain,
    ( sK5 = sK6
    | ~ v1_relat_1(sK5)
    | ~ m1_subset_1(sK7(sK6,sK5),sK3)
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f399,f45])).

fof(f399,plain,
    ( sK5 = sK6
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ m1_subset_1(sK7(sK6,sK5),sK3)
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f398,f200])).

fof(f398,plain,
    ( sK3 != k1_relat_1(sK5)
    | sK5 = sK6
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ m1_subset_1(sK7(sK6,sK5),sK3)
    | ~ spl8_7 ),
    inference(equality_resolution,[],[f370])).

fof(f370,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,sK7(sK6,X0)) != k1_funct_1(X0,sK7(sK6,X0))
        | k1_relat_1(X0) != sK3
        | sK6 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ m1_subset_1(sK7(sK6,X0),sK3) )
    | ~ spl8_7 ),
    inference(forward_demodulation,[],[f369,f210])).

fof(f369,plain,(
    ! [X0] :
      ( k1_funct_1(sK5,sK7(sK6,X0)) != k1_funct_1(X0,sK7(sK6,X0))
      | sK6 = X0
      | k1_relat_1(X0) != k1_relat_1(sK6)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(sK7(sK6,X0),sK3) ) ),
    inference(subsumption_resolution,[],[f368,f92])).

fof(f368,plain,(
    ! [X0] :
      ( k1_funct_1(sK5,sK7(sK6,X0)) != k1_funct_1(X0,sK7(sK6,X0))
      | sK6 = X0
      | k1_relat_1(X0) != k1_relat_1(sK6)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK6)
      | ~ m1_subset_1(sK7(sK6,X0),sK3) ) ),
    inference(subsumption_resolution,[],[f364,f48])).

fof(f364,plain,(
    ! [X0] :
      ( k1_funct_1(sK5,sK7(sK6,X0)) != k1_funct_1(X0,sK7(sK6,X0))
      | sK6 = X0
      | k1_relat_1(X0) != k1_relat_1(sK6)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK6)
      | ~ v1_relat_1(sK6)
      | ~ m1_subset_1(sK7(sK6,X0),sK3) ) ),
    inference(superposition,[],[f55,f51])).

fof(f51,plain,(
    ! [X4] :
      ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
      | ~ m1_subset_1(X4,sK3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f258,plain,
    ( spl8_5
    | spl8_6 ),
    inference(avatar_split_clause,[],[f257,f202,f198])).

fof(f257,plain,
    ( sK3 = k1_relat_1(sK5)
    | spl8_6 ),
    inference(subsumption_resolution,[],[f256,f203])).

fof(f203,plain,
    ( ~ sP0(sK3,sK4)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f202])).

fof(f256,plain,
    ( sP0(sK3,sK4)
    | sK3 = k1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f249,f46])).

fof(f46,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f249,plain,
    ( ~ v1_funct_2(sK5,sK3,sK4)
    | sP0(sK3,sK4)
    | sK3 = k1_relat_1(sK5) ),
    inference(resolution,[],[f47,f184])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:24:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (13714)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (13713)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (13709)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (13714)Refutation not found, incomplete strategy% (13714)------------------------------
% 0.22/0.53  % (13714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (13712)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.54  % (13730)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.54  % (13709)Refutation not found, incomplete strategy% (13709)------------------------------
% 0.22/0.54  % (13709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (13709)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (13709)Memory used [KB]: 10618
% 0.22/0.54  % (13709)Time elapsed: 0.114 s
% 0.22/0.54  % (13709)------------------------------
% 0.22/0.54  % (13709)------------------------------
% 0.22/0.55  % (13710)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.40/0.55  % (13722)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.40/0.55  % (13714)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (13714)Memory used [KB]: 10618
% 1.40/0.55  % (13714)Time elapsed: 0.110 s
% 1.40/0.55  % (13714)------------------------------
% 1.40/0.55  % (13714)------------------------------
% 1.40/0.55  % (13713)Refutation not found, incomplete strategy% (13713)------------------------------
% 1.40/0.55  % (13713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (13713)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (13713)Memory used [KB]: 6140
% 1.40/0.55  % (13713)Time elapsed: 0.138 s
% 1.40/0.55  % (13713)------------------------------
% 1.40/0.55  % (13713)------------------------------
% 1.40/0.56  % (13708)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.40/0.56  % (13732)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.40/0.56  % (13711)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.40/0.56  % (13718)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.61/0.57  % (13724)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.61/0.57  % (13712)Refutation found. Thanks to Tanya!
% 1.61/0.57  % SZS status Theorem for theBenchmark
% 1.61/0.57  % SZS output start Proof for theBenchmark
% 1.61/0.57  fof(f495,plain,(
% 1.61/0.57    $false),
% 1.61/0.57    inference(avatar_sat_refutation,[],[f258,f406,f412,f435,f449,f450,f456,f462,f488])).
% 1.61/0.57  fof(f488,plain,(
% 1.61/0.57    ~spl8_13 | spl8_9 | ~spl8_11),
% 1.61/0.57    inference(avatar_split_clause,[],[f479,f295,f286,f311])).
% 1.61/0.57  fof(f311,plain,(
% 1.61/0.57    spl8_13 <=> k1_xboole_0 = sK6),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.61/0.57  fof(f286,plain,(
% 1.61/0.57    spl8_9 <=> sK5 = sK6),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.61/0.57  fof(f295,plain,(
% 1.61/0.57    spl8_11 <=> k1_xboole_0 = sK5),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.61/0.57  fof(f479,plain,(
% 1.61/0.57    k1_xboole_0 != sK6 | (spl8_9 | ~spl8_11)),
% 1.61/0.57    inference(backward_demodulation,[],[f287,f297])).
% 1.61/0.57  fof(f297,plain,(
% 1.61/0.57    k1_xboole_0 = sK5 | ~spl8_11),
% 1.61/0.57    inference(avatar_component_clause,[],[f295])).
% 1.61/0.57  fof(f287,plain,(
% 1.61/0.57    sK5 != sK6 | spl8_9),
% 1.61/0.57    inference(avatar_component_clause,[],[f286])).
% 1.61/0.57  fof(f462,plain,(
% 1.61/0.57    spl8_13 | ~spl8_6),
% 1.61/0.57    inference(avatar_split_clause,[],[f461,f202,f311])).
% 1.61/0.57  fof(f202,plain,(
% 1.61/0.57    spl8_6 <=> sP0(sK3,sK4)),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.61/0.57  fof(f461,plain,(
% 1.61/0.57    k1_xboole_0 = sK6 | ~spl8_6),
% 1.61/0.57    inference(subsumption_resolution,[],[f459,f89])).
% 1.61/0.57  fof(f89,plain,(
% 1.61/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.61/0.57    inference(resolution,[],[f59,f53])).
% 1.61/0.57  fof(f53,plain,(
% 1.61/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f3])).
% 1.61/0.57  fof(f3,axiom,(
% 1.61/0.57    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.61/0.57  fof(f59,plain,(
% 1.61/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f36])).
% 1.61/0.57  fof(f36,plain,(
% 1.61/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.61/0.57    inference(nnf_transformation,[],[f4])).
% 1.61/0.57  fof(f4,axiom,(
% 1.61/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.61/0.57  fof(f459,plain,(
% 1.61/0.57    k1_xboole_0 = sK6 | ~r1_tarski(k1_xboole_0,sK6) | ~spl8_6),
% 1.61/0.57    inference(resolution,[],[f235,f58])).
% 1.61/0.57  fof(f58,plain,(
% 1.61/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f35])).
% 1.61/0.57  fof(f35,plain,(
% 1.61/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.61/0.57    inference(flattening,[],[f34])).
% 1.61/0.57  fof(f34,plain,(
% 1.61/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.61/0.57    inference(nnf_transformation,[],[f1])).
% 1.61/0.57  fof(f1,axiom,(
% 1.61/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.61/0.57  fof(f235,plain,(
% 1.61/0.57    r1_tarski(sK6,k1_xboole_0) | ~spl8_6),
% 1.61/0.57    inference(forward_demodulation,[],[f220,f79])).
% 1.61/0.57  fof(f79,plain,(
% 1.61/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.61/0.57    inference(equality_resolution,[],[f63])).
% 1.61/0.57  fof(f63,plain,(
% 1.61/0.57    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.61/0.57    inference(cnf_transformation,[],[f38])).
% 1.61/0.57  fof(f38,plain,(
% 1.61/0.57    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.61/0.57    inference(flattening,[],[f37])).
% 1.61/0.57  % (13727)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.61/0.57  fof(f37,plain,(
% 1.61/0.57    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.61/0.57    inference(nnf_transformation,[],[f2])).
% 1.61/0.57  fof(f2,axiom,(
% 1.61/0.57    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.61/0.57  fof(f220,plain,(
% 1.61/0.57    r1_tarski(sK6,k2_zfmisc_1(sK3,k1_xboole_0)) | ~spl8_6),
% 1.61/0.57    inference(backward_demodulation,[],[f88,f213])).
% 1.61/0.57  fof(f213,plain,(
% 1.61/0.57    k1_xboole_0 = sK4 | ~spl8_6),
% 1.61/0.57    inference(resolution,[],[f204,f70])).
% 1.61/0.57  fof(f70,plain,(
% 1.61/0.57    ( ! [X0,X1] : (~sP0(X0,X1) | k1_xboole_0 = X1) )),
% 1.61/0.57    inference(cnf_transformation,[],[f43])).
% 1.61/0.57  fof(f43,plain,(
% 1.61/0.57    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 1.61/0.57    inference(nnf_transformation,[],[f25])).
% 1.61/0.57  fof(f25,plain,(
% 1.61/0.57    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 1.61/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.61/0.57  fof(f204,plain,(
% 1.61/0.57    sP0(sK3,sK4) | ~spl8_6),
% 1.61/0.57    inference(avatar_component_clause,[],[f202])).
% 1.61/0.57  fof(f88,plain,(
% 1.61/0.57    r1_tarski(sK6,k2_zfmisc_1(sK3,sK4))),
% 1.61/0.57    inference(resolution,[],[f59,f50])).
% 1.61/0.57  fof(f50,plain,(
% 1.61/0.57    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 1.61/0.57    inference(cnf_transformation,[],[f31])).
% 1.61/0.57  fof(f31,plain,(
% 1.61/0.57    (~r2_relset_1(sK3,sK4,sK5,sK6) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~m1_subset_1(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 1.61/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f14,f30,f29])).
% 1.61/0.57  fof(f29,plain,(
% 1.61/0.57    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK5,X4) | ~m1_subset_1(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 1.61/0.57    introduced(choice_axiom,[])).
% 1.61/0.57  fof(f30,plain,(
% 1.61/0.57    ? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK5,X4) | ~m1_subset_1(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) => (~r2_relset_1(sK3,sK4,sK5,sK6) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~m1_subset_1(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 1.61/0.57    introduced(choice_axiom,[])).
% 1.61/0.57  % (13717)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.61/0.57  fof(f14,plain,(
% 1.61/0.57    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.61/0.57    inference(flattening,[],[f13])).
% 1.61/0.57  fof(f13,plain,(
% 1.61/0.57    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.61/0.57    inference(ennf_transformation,[],[f12])).
% 1.61/0.57  fof(f12,negated_conjecture,(
% 1.61/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.61/0.57    inference(negated_conjecture,[],[f11])).
% 1.61/0.57  fof(f11,conjecture,(
% 1.61/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).
% 1.61/0.57  fof(f456,plain,(
% 1.61/0.57    spl8_11 | ~spl8_6),
% 1.61/0.57    inference(avatar_split_clause,[],[f455,f202,f295])).
% 1.61/0.57  fof(f455,plain,(
% 1.61/0.57    k1_xboole_0 = sK5 | ~spl8_6),
% 1.61/0.57    inference(subsumption_resolution,[],[f453,f89])).
% 1.61/0.57  fof(f453,plain,(
% 1.61/0.57    k1_xboole_0 = sK5 | ~r1_tarski(k1_xboole_0,sK5) | ~spl8_6),
% 1.61/0.57    inference(resolution,[],[f234,f58])).
% 1.61/0.57  fof(f234,plain,(
% 1.61/0.57    r1_tarski(sK5,k1_xboole_0) | ~spl8_6),
% 1.61/0.57    inference(forward_demodulation,[],[f219,f79])).
% 1.61/0.57  fof(f219,plain,(
% 1.61/0.57    r1_tarski(sK5,k2_zfmisc_1(sK3,k1_xboole_0)) | ~spl8_6),
% 1.61/0.57    inference(backward_demodulation,[],[f87,f213])).
% 1.61/0.57  fof(f87,plain,(
% 1.61/0.57    r1_tarski(sK5,k2_zfmisc_1(sK3,sK4))),
% 1.61/0.57    inference(resolution,[],[f59,f47])).
% 1.61/0.57  fof(f47,plain,(
% 1.61/0.57    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 1.61/0.57    inference(cnf_transformation,[],[f31])).
% 1.61/0.57  fof(f450,plain,(
% 1.61/0.57    spl8_21),
% 1.61/0.57    inference(avatar_split_clause,[],[f49,f446])).
% 1.61/0.57  % (13721)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.61/0.57  fof(f446,plain,(
% 1.61/0.57    spl8_21 <=> v1_funct_2(sK6,sK3,sK4)),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 1.61/0.57  fof(f49,plain,(
% 1.61/0.57    v1_funct_2(sK6,sK3,sK4)),
% 1.61/0.57    inference(cnf_transformation,[],[f31])).
% 1.61/0.57  fof(f449,plain,(
% 1.61/0.57    spl8_7 | spl8_6 | ~spl8_21),
% 1.61/0.57    inference(avatar_split_clause,[],[f264,f446,f202,f208])).
% 1.61/0.57  fof(f208,plain,(
% 1.61/0.57    spl8_7 <=> sK3 = k1_relat_1(sK6)),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.61/0.57  fof(f264,plain,(
% 1.61/0.57    ~v1_funct_2(sK6,sK3,sK4) | sP0(sK3,sK4) | sK3 = k1_relat_1(sK6)),
% 1.61/0.57    inference(resolution,[],[f50,f184])).
% 1.61/0.57  fof(f184,plain,(
% 1.61/0.57    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | k1_relat_1(X5) = X3) )),
% 1.61/0.57    inference(subsumption_resolution,[],[f182,f72])).
% 1.61/0.57  fof(f72,plain,(
% 1.61/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f28])).
% 1.61/0.57  fof(f28,plain,(
% 1.61/0.57    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.61/0.57    inference(definition_folding,[],[f20,f27,f26,f25])).
% 1.61/0.57  fof(f26,plain,(
% 1.61/0.57    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 1.61/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.61/0.57  fof(f27,plain,(
% 1.61/0.57    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 1.61/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.61/0.57  fof(f20,plain,(
% 1.61/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.61/0.57    inference(flattening,[],[f19])).
% 1.61/0.57  fof(f19,plain,(
% 1.61/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.61/0.57    inference(ennf_transformation,[],[f10])).
% 1.61/0.57  fof(f10,axiom,(
% 1.61/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.61/0.57  fof(f182,plain,(
% 1.61/0.57    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | ~sP1(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 1.61/0.57    inference(superposition,[],[f68,f65])).
% 1.61/0.57  fof(f65,plain,(
% 1.61/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f18])).
% 1.61/0.57  fof(f18,plain,(
% 1.61/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.61/0.57    inference(ennf_transformation,[],[f8])).
% 1.61/0.57  fof(f8,axiom,(
% 1.61/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.61/0.57  fof(f68,plain,(
% 1.61/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f42])).
% 1.61/0.57  fof(f42,plain,(
% 1.61/0.57    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 1.61/0.57    inference(rectify,[],[f41])).
% 1.61/0.57  fof(f41,plain,(
% 1.61/0.57    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 1.61/0.57    inference(nnf_transformation,[],[f26])).
% 1.61/0.57  fof(f435,plain,(
% 1.61/0.57    ~spl8_9),
% 1.61/0.57    inference(avatar_contradiction_clause,[],[f434])).
% 1.61/0.57  fof(f434,plain,(
% 1.61/0.57    $false | ~spl8_9),
% 1.61/0.57    inference(subsumption_resolution,[],[f416,f168])).
% 1.61/0.57  fof(f168,plain,(
% 1.61/0.57    r2_relset_1(sK3,sK4,sK5,sK5)),
% 1.61/0.57    inference(resolution,[],[f86,f47])).
% 1.61/0.57  fof(f86,plain,(
% 1.61/0.57    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.61/0.57    inference(duplicate_literal_removal,[],[f85])).
% 1.61/0.57  fof(f85,plain,(
% 1.61/0.57    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.61/0.57    inference(equality_resolution,[],[f76])).
% 1.61/0.57  fof(f76,plain,(
% 1.61/0.57    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f44])).
% 1.61/0.57  fof(f44,plain,(
% 1.61/0.57    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.61/0.57    inference(nnf_transformation,[],[f24])).
% 1.61/0.57  fof(f24,plain,(
% 1.61/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.61/0.57    inference(flattening,[],[f23])).
% 1.61/0.57  fof(f23,plain,(
% 1.61/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.61/0.57    inference(ennf_transformation,[],[f9])).
% 1.61/0.57  fof(f9,axiom,(
% 1.61/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.61/0.57  fof(f416,plain,(
% 1.61/0.57    ~r2_relset_1(sK3,sK4,sK5,sK5) | ~spl8_9),
% 1.61/0.57    inference(backward_demodulation,[],[f52,f288])).
% 1.61/0.57  fof(f288,plain,(
% 1.61/0.57    sK5 = sK6 | ~spl8_9),
% 1.61/0.57    inference(avatar_component_clause,[],[f286])).
% 1.61/0.57  fof(f52,plain,(
% 1.61/0.57    ~r2_relset_1(sK3,sK4,sK5,sK6)),
% 1.61/0.57    inference(cnf_transformation,[],[f31])).
% 1.61/0.57  fof(f412,plain,(
% 1.61/0.57    spl8_9 | ~spl8_5 | ~spl8_7 | spl8_20),
% 1.61/0.57    inference(avatar_split_clause,[],[f411,f403,f208,f198,f286])).
% 1.61/0.57  fof(f198,plain,(
% 1.61/0.57    spl8_5 <=> sK3 = k1_relat_1(sK5)),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.61/0.57  fof(f403,plain,(
% 1.61/0.57    spl8_20 <=> m1_subset_1(sK7(sK6,sK5),sK3)),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.61/0.57  fof(f411,plain,(
% 1.61/0.57    sK5 = sK6 | (~spl8_5 | ~spl8_7 | spl8_20)),
% 1.61/0.57    inference(subsumption_resolution,[],[f410,f77])).
% 1.61/0.57  fof(f77,plain,(
% 1.61/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.61/0.57    inference(equality_resolution,[],[f57])).
% 1.61/0.57  fof(f57,plain,(
% 1.61/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.61/0.57    inference(cnf_transformation,[],[f35])).
% 1.61/0.57  fof(f410,plain,(
% 1.61/0.57    sK5 = sK6 | ~r1_tarski(sK3,sK3) | (~spl8_5 | ~spl8_7 | spl8_20)),
% 1.61/0.57    inference(subsumption_resolution,[],[f409,f91])).
% 1.61/0.57  fof(f91,plain,(
% 1.61/0.57    v1_relat_1(sK5)),
% 1.61/0.57    inference(resolution,[],[f64,f47])).
% 1.61/0.57  fof(f64,plain,(
% 1.61/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f17])).
% 1.61/0.57  fof(f17,plain,(
% 1.61/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.61/0.57    inference(ennf_transformation,[],[f7])).
% 1.61/0.57  fof(f7,axiom,(
% 1.61/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.61/0.57  fof(f409,plain,(
% 1.61/0.57    ~v1_relat_1(sK5) | sK5 = sK6 | ~r1_tarski(sK3,sK3) | (~spl8_5 | ~spl8_7 | spl8_20)),
% 1.61/0.57    inference(subsumption_resolution,[],[f408,f45])).
% 1.61/0.57  fof(f45,plain,(
% 1.61/0.57    v1_funct_1(sK5)),
% 1.61/0.57    inference(cnf_transformation,[],[f31])).
% 1.61/0.57  fof(f408,plain,(
% 1.61/0.57    ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | sK5 = sK6 | ~r1_tarski(sK3,sK3) | (~spl8_5 | ~spl8_7 | spl8_20)),
% 1.61/0.57    inference(subsumption_resolution,[],[f407,f200])).
% 1.61/0.57  fof(f200,plain,(
% 1.61/0.57    sK3 = k1_relat_1(sK5) | ~spl8_5),
% 1.61/0.57    inference(avatar_component_clause,[],[f198])).
% 1.61/0.57  fof(f407,plain,(
% 1.61/0.57    sK3 != k1_relat_1(sK5) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | sK5 = sK6 | ~r1_tarski(sK3,sK3) | (~spl8_7 | spl8_20)),
% 1.61/0.57    inference(resolution,[],[f405,f326])).
% 1.61/0.57  fof(f326,plain,(
% 1.61/0.57    ( ! [X0,X1] : (m1_subset_1(sK7(sK6,X0),X1) | k1_relat_1(X0) != sK3 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK6 = X0 | ~r1_tarski(sK3,X1)) ) | ~spl8_7),
% 1.61/0.57    inference(resolution,[],[f321,f148])).
% 1.61/0.57  fof(f148,plain,(
% 1.61/0.57    ( ! [X6,X4,X5] : (~r2_hidden(X4,X6) | m1_subset_1(X4,X5) | ~r1_tarski(X6,X5)) )),
% 1.61/0.57    inference(resolution,[],[f74,f60])).
% 1.61/0.57  fof(f60,plain,(
% 1.61/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f36])).
% 1.61/0.57  fof(f74,plain,(
% 1.61/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f22])).
% 1.61/0.57  fof(f22,plain,(
% 1.61/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.61/0.57    inference(flattening,[],[f21])).
% 1.61/0.57  fof(f21,plain,(
% 1.61/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.61/0.57    inference(ennf_transformation,[],[f5])).
% 1.61/0.57  fof(f5,axiom,(
% 1.61/0.57    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.61/0.57  fof(f321,plain,(
% 1.61/0.57    ( ! [X1] : (r2_hidden(sK7(sK6,X1),sK3) | sK6 = X1 | k1_relat_1(X1) != sK3 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | ~spl8_7),
% 1.61/0.57    inference(subsumption_resolution,[],[f320,f92])).
% 1.61/0.57  fof(f92,plain,(
% 1.61/0.57    v1_relat_1(sK6)),
% 1.61/0.57    inference(resolution,[],[f64,f50])).
% 1.61/0.57  fof(f320,plain,(
% 1.61/0.57    ( ! [X1] : (r2_hidden(sK7(sK6,X1),sK3) | sK6 = X1 | k1_relat_1(X1) != sK3 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(sK6)) ) | ~spl8_7),
% 1.61/0.57    inference(subsumption_resolution,[],[f317,f48])).
% 1.61/0.57  fof(f48,plain,(
% 1.61/0.57    v1_funct_1(sK6)),
% 1.61/0.57    inference(cnf_transformation,[],[f31])).
% 1.61/0.57  fof(f317,plain,(
% 1.61/0.57    ( ! [X1] : (r2_hidden(sK7(sK6,X1),sK3) | sK6 = X1 | k1_relat_1(X1) != sK3 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)) ) | ~spl8_7),
% 1.61/0.57    inference(superposition,[],[f54,f210])).
% 1.61/0.57  fof(f210,plain,(
% 1.61/0.57    sK3 = k1_relat_1(sK6) | ~spl8_7),
% 1.61/0.57    inference(avatar_component_clause,[],[f208])).
% 1.61/0.57  fof(f54,plain,(
% 1.61/0.57    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),k1_relat_1(X0)) | X0 = X1 | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f33])).
% 1.61/0.57  fof(f33,plain,(
% 1.61/0.57    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.61/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f16,f32])).
% 1.61/0.57  fof(f32,plain,(
% 1.61/0.57    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))))),
% 1.61/0.57    introduced(choice_axiom,[])).
% 1.61/0.57  fof(f16,plain,(
% 1.61/0.57    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.61/0.57    inference(flattening,[],[f15])).
% 1.61/0.57  fof(f15,plain,(
% 1.61/0.57    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.61/0.57    inference(ennf_transformation,[],[f6])).
% 1.61/0.57  fof(f6,axiom,(
% 1.61/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 1.61/0.57  fof(f405,plain,(
% 1.61/0.57    ~m1_subset_1(sK7(sK6,sK5),sK3) | spl8_20),
% 1.61/0.57    inference(avatar_component_clause,[],[f403])).
% 1.61/0.57  fof(f406,plain,(
% 1.61/0.57    ~spl8_20 | spl8_9 | ~spl8_5 | ~spl8_7),
% 1.61/0.57    inference(avatar_split_clause,[],[f401,f208,f198,f286,f403])).
% 1.61/0.57  fof(f401,plain,(
% 1.61/0.57    sK5 = sK6 | ~m1_subset_1(sK7(sK6,sK5),sK3) | (~spl8_5 | ~spl8_7)),
% 1.61/0.57    inference(subsumption_resolution,[],[f400,f91])).
% 1.61/0.57  fof(f400,plain,(
% 1.61/0.57    sK5 = sK6 | ~v1_relat_1(sK5) | ~m1_subset_1(sK7(sK6,sK5),sK3) | (~spl8_5 | ~spl8_7)),
% 1.61/0.57    inference(subsumption_resolution,[],[f399,f45])).
% 1.61/0.57  fof(f399,plain,(
% 1.61/0.57    sK5 = sK6 | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | ~m1_subset_1(sK7(sK6,sK5),sK3) | (~spl8_5 | ~spl8_7)),
% 1.61/0.57    inference(subsumption_resolution,[],[f398,f200])).
% 1.61/0.57  fof(f398,plain,(
% 1.61/0.57    sK3 != k1_relat_1(sK5) | sK5 = sK6 | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | ~m1_subset_1(sK7(sK6,sK5),sK3) | ~spl8_7),
% 1.61/0.57    inference(equality_resolution,[],[f370])).
% 1.61/0.57  fof(f370,plain,(
% 1.61/0.57    ( ! [X0] : (k1_funct_1(sK5,sK7(sK6,X0)) != k1_funct_1(X0,sK7(sK6,X0)) | k1_relat_1(X0) != sK3 | sK6 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~m1_subset_1(sK7(sK6,X0),sK3)) ) | ~spl8_7),
% 1.61/0.57    inference(forward_demodulation,[],[f369,f210])).
% 1.61/0.57  fof(f369,plain,(
% 1.61/0.57    ( ! [X0] : (k1_funct_1(sK5,sK7(sK6,X0)) != k1_funct_1(X0,sK7(sK6,X0)) | sK6 = X0 | k1_relat_1(X0) != k1_relat_1(sK6) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~m1_subset_1(sK7(sK6,X0),sK3)) )),
% 1.61/0.57    inference(subsumption_resolution,[],[f368,f92])).
% 1.61/0.57  fof(f368,plain,(
% 1.61/0.57    ( ! [X0] : (k1_funct_1(sK5,sK7(sK6,X0)) != k1_funct_1(X0,sK7(sK6,X0)) | sK6 = X0 | k1_relat_1(X0) != k1_relat_1(sK6) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK6) | ~m1_subset_1(sK7(sK6,X0),sK3)) )),
% 1.61/0.57    inference(subsumption_resolution,[],[f364,f48])).
% 1.61/0.57  fof(f364,plain,(
% 1.61/0.57    ( ! [X0] : (k1_funct_1(sK5,sK7(sK6,X0)) != k1_funct_1(X0,sK7(sK6,X0)) | sK6 = X0 | k1_relat_1(X0) != k1_relat_1(sK6) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~m1_subset_1(sK7(sK6,X0),sK3)) )),
% 1.61/0.57    inference(superposition,[],[f55,f51])).
% 1.61/0.57  fof(f51,plain,(
% 1.61/0.57    ( ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~m1_subset_1(X4,sK3)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f31])).
% 1.61/0.57  fof(f55,plain,(
% 1.61/0.57    ( ! [X0,X1] : (k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1)) | X0 = X1 | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f33])).
% 1.61/0.57  fof(f258,plain,(
% 1.61/0.57    spl8_5 | spl8_6),
% 1.61/0.57    inference(avatar_split_clause,[],[f257,f202,f198])).
% 1.61/0.57  fof(f257,plain,(
% 1.61/0.57    sK3 = k1_relat_1(sK5) | spl8_6),
% 1.61/0.57    inference(subsumption_resolution,[],[f256,f203])).
% 1.61/0.57  fof(f203,plain,(
% 1.61/0.57    ~sP0(sK3,sK4) | spl8_6),
% 1.61/0.57    inference(avatar_component_clause,[],[f202])).
% 1.61/0.57  fof(f256,plain,(
% 1.61/0.57    sP0(sK3,sK4) | sK3 = k1_relat_1(sK5)),
% 1.61/0.57    inference(subsumption_resolution,[],[f249,f46])).
% 1.61/0.57  fof(f46,plain,(
% 1.61/0.57    v1_funct_2(sK5,sK3,sK4)),
% 1.61/0.57    inference(cnf_transformation,[],[f31])).
% 1.61/0.57  fof(f249,plain,(
% 1.61/0.57    ~v1_funct_2(sK5,sK3,sK4) | sP0(sK3,sK4) | sK3 = k1_relat_1(sK5)),
% 1.61/0.57    inference(resolution,[],[f47,f184])).
% 1.61/0.57  % SZS output end Proof for theBenchmark
% 1.61/0.57  % (13712)------------------------------
% 1.61/0.57  % (13712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (13712)Termination reason: Refutation
% 1.61/0.57  
% 1.61/0.57  % (13712)Memory used [KB]: 6396
% 1.61/0.57  % (13712)Time elapsed: 0.149 s
% 1.61/0.57  % (13712)------------------------------
% 1.61/0.57  % (13712)------------------------------
% 1.61/0.58  % (13707)Success in time 0.211 s
%------------------------------------------------------------------------------
