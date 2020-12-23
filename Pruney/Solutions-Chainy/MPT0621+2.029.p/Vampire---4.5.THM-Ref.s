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
% DateTime   : Thu Dec  3 12:51:58 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 116 expanded)
%              Number of leaves         :   15 (  35 expanded)
%              Depth                    :   17
%              Number of atoms          :  317 ( 591 expanded)
%              Number of equality atoms :  120 ( 239 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f267,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f192,f251])).

fof(f251,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f33,f97])).

fof(f97,plain,
    ( ! [X1] : k1_xboole_0 = X1
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl6_1
  <=> ! [X1] : k1_xboole_0 = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f33,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k1_xboole_0 != sK2
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK2
            | k1_relat_1(X1) != sK2
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k1_relat_1(X2) != X0
                | k1_relat_1(X1) != X0
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
   => ( k1_xboole_0 != sK2
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK2
              | k1_relat_1(X1) != sK2
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f7])).

% (26346)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f7,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

fof(f192,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | ~ spl6_2 ),
    inference(trivial_inequality_removal,[],[f177])).

fof(f177,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK2 != sK2
    | ~ spl6_2 ),
    inference(superposition,[],[f33,f139])).

fof(f139,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | sK2 != X0 )
    | ~ spl6_2 ),
    inference(resolution,[],[f138,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,k1_xboole_0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f55,f34])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f14,f13])).

fof(f13,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f138,plain,
    ( ! [X8,X7] :
        ( sP1(X7,k1_xboole_0,X8)
        | sK2 != X8 )
    | ~ spl6_2 ),
    inference(resolution,[],[f132,f59])).

fof(f59,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f39,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f39,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f132,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK5(X0,X1,X2),X1)
        | sP1(X0,X1,X2)
        | sK2 != X2 )
    | ~ spl6_2 ),
    inference(resolution,[],[f130,f100])).

fof(f100,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,X0)
        | sK2 != X0 )
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl6_2
  <=> ! [X0,X2] :
        ( sK2 != X0
        | ~ r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | sP1(X0,X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X1) ) ),
    inference(resolution,[],[f49,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,sK5(X0,X1,X2),X0)
      | sP1(X0,X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sP0(X1,sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f26])).

% (26332)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sP0(X1,sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f107,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f106,f99,f96])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( sK2 != X0
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( sK2 != X0
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(condensation,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( sK2 != X0
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X3)
      | sK2 != X3
      | ~ r2_hidden(X2,X0) ) ),
    inference(forward_demodulation,[],[f103,f45])).

fof(f45,plain,(
    ! [X0,X1] : k1_relat_1(sK4(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK4(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK4(X0,X1)) = X0
      & v1_funct_1(sK4(X0,X1))
      & v1_relat_1(sK4(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK4(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK4(X0,X1)) = X0
        & v1_funct_1(sK4(X0,X1))
        & v1_relat_1(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X1
      | ~ r2_hidden(X2,X3)
      | sK2 != X3
      | sK2 != k1_relat_1(sK4(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(subsumption_resolution,[],[f102,f43])).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X1
      | ~ r2_hidden(X2,X3)
      | sK2 != X3
      | sK2 != k1_relat_1(sK4(X0,X1))
      | ~ v1_relat_1(sK4(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(subsumption_resolution,[],[f89,f44])).

fof(f44,plain,(
    ! [X0,X1] : v1_funct_1(sK4(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X1
      | ~ r2_hidden(X2,X3)
      | sK2 != X3
      | sK2 != k1_relat_1(sK4(X0,X1))
      | ~ v1_funct_1(sK4(X0,X1))
      | ~ v1_relat_1(sK4(X0,X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f82,f46])).

% (26343)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f46,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK4(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,X0)
      | sK2 != X0
      | k1_relat_1(X1) != sK2
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f38,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( sK3(X0) = X1
      | sK2 != X0
      | k1_relat_1(X1) != sK2
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f64,f35])).

fof(f35,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK3(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK3(X0)) = X0
      & v1_funct_1(sK3(X0))
      & v1_relat_1(sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK3(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK3(X0)) = X0
        & v1_funct_1(sK3(X0))
        & v1_relat_1(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( sK2 != X0
      | sK3(X0) = X1
      | k1_relat_1(X1) != sK2
      | ~ v1_relat_1(sK3(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f62,f36])).

fof(f36,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,(
    ! [X0,X1] :
      ( sK2 != X0
      | sK3(X0) = X1
      | k1_relat_1(X1) != sK2
      | ~ v1_funct_1(sK3(X0))
      | ~ v1_relat_1(sK3(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f32,f37])).

fof(f37,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X2) != sK2
      | X1 = X2
      | k1_relat_1(X1) != sK2
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = k1_funct_1(sK3(X0),X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:15:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.50  % (26330)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (26337)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.50  % (26331)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (26329)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (26329)Refutation not found, incomplete strategy% (26329)------------------------------
% 0.20/0.51  % (26329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (26329)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (26329)Memory used [KB]: 10490
% 0.20/0.51  % (26329)Time elapsed: 0.092 s
% 0.20/0.51  % (26329)------------------------------
% 0.20/0.51  % (26329)------------------------------
% 0.20/0.51  % (26354)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (26345)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (26336)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.18/0.51  % (26353)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.18/0.51  % (26330)Refutation not found, incomplete strategy% (26330)------------------------------
% 1.18/0.51  % (26330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.51  % (26330)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.51  
% 1.18/0.51  % (26330)Memory used [KB]: 10618
% 1.18/0.51  % (26330)Time elapsed: 0.104 s
% 1.18/0.51  % (26330)------------------------------
% 1.18/0.51  % (26330)------------------------------
% 1.18/0.52  % (26338)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.18/0.52  % (26341)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.18/0.52  % (26342)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.18/0.52  % (26341)Refutation not found, incomplete strategy% (26341)------------------------------
% 1.18/0.52  % (26341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.52  % (26341)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.52  
% 1.18/0.52  % (26341)Memory used [KB]: 10490
% 1.18/0.52  % (26341)Time elapsed: 0.102 s
% 1.18/0.52  % (26341)------------------------------
% 1.18/0.52  % (26341)------------------------------
% 1.18/0.52  % (26340)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.18/0.52  % (26344)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.18/0.52  % (26348)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.18/0.52  % (26335)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.18/0.52  % (26333)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.18/0.52  % (26334)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.18/0.53  % (26334)Refutation not found, incomplete strategy% (26334)------------------------------
% 1.18/0.53  % (26334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.53  % (26334)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.53  
% 1.18/0.53  % (26334)Memory used [KB]: 6140
% 1.18/0.53  % (26334)Time elapsed: 0.114 s
% 1.18/0.53  % (26334)------------------------------
% 1.18/0.53  % (26334)------------------------------
% 1.18/0.53  % (26352)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.18/0.53  % (26350)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.18/0.53  % (26347)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.18/0.53  % (26349)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.18/0.53  % (26333)Refutation found. Thanks to Tanya!
% 1.18/0.53  % SZS status Theorem for theBenchmark
% 1.18/0.53  % SZS output start Proof for theBenchmark
% 1.34/0.53  fof(f267,plain,(
% 1.34/0.53    $false),
% 1.34/0.53    inference(avatar_sat_refutation,[],[f107,f192,f251])).
% 1.34/0.53  fof(f251,plain,(
% 1.34/0.53    ~spl6_1),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f223])).
% 1.34/0.53  fof(f223,plain,(
% 1.34/0.53    $false | ~spl6_1),
% 1.34/0.53    inference(subsumption_resolution,[],[f33,f97])).
% 1.34/0.53  fof(f97,plain,(
% 1.34/0.53    ( ! [X1] : (k1_xboole_0 = X1) ) | ~spl6_1),
% 1.34/0.53    inference(avatar_component_clause,[],[f96])).
% 1.34/0.53  fof(f96,plain,(
% 1.34/0.53    spl6_1 <=> ! [X1] : k1_xboole_0 = X1),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.34/0.53  fof(f33,plain,(
% 1.34/0.53    k1_xboole_0 != sK2),
% 1.34/0.53    inference(cnf_transformation,[],[f17])).
% 1.34/0.53  fof(f17,plain,(
% 1.34/0.53    k1_xboole_0 != sK2 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK2 | k1_relat_1(X1) != sK2 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.34/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f16])).
% 1.34/0.53  fof(f16,plain,(
% 1.34/0.53    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK2 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK2 | k1_relat_1(X1) != sK2 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f10,plain,(
% 1.34/0.53    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.34/0.53    inference(flattening,[],[f9])).
% 1.34/0.53  fof(f9,plain,(
% 1.34/0.53    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 1.34/0.53    inference(ennf_transformation,[],[f8])).
% 1.34/0.53  fof(f8,negated_conjecture,(
% 1.34/0.53    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 1.34/0.53    inference(negated_conjecture,[],[f7])).
% 1.34/0.53  % (26346)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.34/0.53  fof(f7,conjecture,(
% 1.34/0.53    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).
% 1.34/0.53  fof(f192,plain,(
% 1.34/0.53    ~spl6_2),
% 1.34/0.53    inference(avatar_contradiction_clause,[],[f191])).
% 1.34/0.53  fof(f191,plain,(
% 1.34/0.53    $false | ~spl6_2),
% 1.34/0.53    inference(trivial_inequality_removal,[],[f177])).
% 1.34/0.53  fof(f177,plain,(
% 1.34/0.53    k1_xboole_0 != k1_xboole_0 | sK2 != sK2 | ~spl6_2),
% 1.34/0.53    inference(superposition,[],[f33,f139])).
% 1.34/0.53  fof(f139,plain,(
% 1.34/0.53    ( ! [X0] : (k1_xboole_0 = X0 | sK2 != X0) ) | ~spl6_2),
% 1.34/0.53    inference(resolution,[],[f138,f83])).
% 1.34/0.53  fof(f83,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~sP1(X0,k1_xboole_0,X1) | k1_xboole_0 = X1) )),
% 1.34/0.53    inference(superposition,[],[f55,f34])).
% 1.34/0.53  fof(f34,plain,(
% 1.34/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f2])).
% 1.34/0.53  fof(f2,axiom,(
% 1.34/0.53    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.34/0.53  fof(f55,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f31])).
% 1.34/0.53  fof(f31,plain,(
% 1.34/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k3_xboole_0(X0,X1) != X2))),
% 1.34/0.53    inference(nnf_transformation,[],[f15])).
% 1.34/0.53  fof(f15,plain,(
% 1.34/0.53    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 1.34/0.53    inference(definition_folding,[],[f1,f14,f13])).
% 1.34/0.53  fof(f13,plain,(
% 1.34/0.53    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 1.34/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.34/0.53  fof(f14,plain,(
% 1.34/0.53    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 1.34/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.34/0.53  fof(f1,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.34/0.53  fof(f138,plain,(
% 1.34/0.53    ( ! [X8,X7] : (sP1(X7,k1_xboole_0,X8) | sK2 != X8) ) | ~spl6_2),
% 1.34/0.53    inference(resolution,[],[f132,f59])).
% 1.34/0.53  fof(f59,plain,(
% 1.34/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.34/0.53    inference(superposition,[],[f39,f56])).
% 1.34/0.53  fof(f56,plain,(
% 1.34/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.34/0.53    inference(equality_resolution,[],[f42])).
% 1.34/0.53  fof(f42,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.34/0.53    inference(cnf_transformation,[],[f21])).
% 1.34/0.53  fof(f21,plain,(
% 1.34/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.34/0.53    inference(flattening,[],[f20])).
% 1.34/0.53  fof(f20,plain,(
% 1.34/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.34/0.53    inference(nnf_transformation,[],[f3])).
% 1.34/0.53  fof(f3,axiom,(
% 1.34/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.34/0.53  fof(f39,plain,(
% 1.34/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f4])).
% 1.34/0.53  fof(f4,axiom,(
% 1.34/0.53    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.34/0.53  fof(f132,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X1) | sP1(X0,X1,X2) | sK2 != X2) ) | ~spl6_2),
% 1.34/0.53    inference(resolution,[],[f130,f100])).
% 1.34/0.53  fof(f100,plain,(
% 1.34/0.53    ( ! [X2,X0] : (~r2_hidden(X2,X0) | sK2 != X0) ) | ~spl6_2),
% 1.34/0.53    inference(avatar_component_clause,[],[f99])).
% 1.34/0.53  fof(f99,plain,(
% 1.34/0.53    spl6_2 <=> ! [X0,X2] : (sK2 != X0 | ~r2_hidden(X2,X0))),
% 1.34/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.34/0.53  fof(f130,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | sP1(X0,X1,X2) | r2_hidden(sK5(X0,X1,X2),X1)) )),
% 1.34/0.53    inference(resolution,[],[f49,f52])).
% 1.34/0.53  fof(f52,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f30])).
% 1.34/0.53  fof(f30,plain,(
% 1.34/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 1.34/0.53    inference(rectify,[],[f29])).
% 1.34/0.53  fof(f29,plain,(
% 1.34/0.53    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 1.34/0.53    inference(flattening,[],[f28])).
% 1.34/0.53  fof(f28,plain,(
% 1.34/0.53    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 1.34/0.53    inference(nnf_transformation,[],[f13])).
% 1.34/0.53  fof(f49,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (sP0(X1,sK5(X0,X1,X2),X0) | sP1(X0,X1,X2) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f27])).
% 1.34/0.53  fof(f27,plain,(
% 1.34/0.53    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sP0(X1,sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.34/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f26])).
% 1.34/0.54  % (26332)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.34/0.54  fof(f26,plain,(
% 1.34/0.54    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sP0(X1,sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.34/0.54    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f25,plain,(
% 1.34/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.34/0.54    inference(rectify,[],[f24])).
% 1.34/0.54  fof(f24,plain,(
% 1.34/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 1.34/0.54    inference(nnf_transformation,[],[f14])).
% 1.34/0.54  fof(f107,plain,(
% 1.34/0.54    spl6_1 | spl6_2),
% 1.34/0.54    inference(avatar_split_clause,[],[f106,f99,f96])).
% 1.34/0.54  fof(f106,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (sK2 != X0 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0)) )),
% 1.34/0.54    inference(duplicate_literal_removal,[],[f105])).
% 1.34/0.54  fof(f105,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (sK2 != X0 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~r2_hidden(X2,X0)) )),
% 1.34/0.54    inference(condensation,[],[f104])).
% 1.34/0.54  fof(f104,plain,(
% 1.34/0.54    ( ! [X2,X0,X3,X1] : (sK2 != X0 | k1_xboole_0 = X1 | ~r2_hidden(X2,X3) | sK2 != X3 | ~r2_hidden(X2,X0)) )),
% 1.34/0.54    inference(forward_demodulation,[],[f103,f45])).
% 1.34/0.54  fof(f45,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k1_relat_1(sK4(X0,X1)) = X0) )),
% 1.34/0.54    inference(cnf_transformation,[],[f23])).
% 1.34/0.54  fof(f23,plain,(
% 1.34/0.54    ! [X0,X1] : (! [X3] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK4(X0,X1)) = X0 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1)))),
% 1.34/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f22])).
% 1.34/0.54  fof(f22,plain,(
% 1.34/0.54    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK4(X0,X1)) = X0 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1))))),
% 1.34/0.54    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f12,plain,(
% 1.34/0.54    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.34/0.54    inference(ennf_transformation,[],[f5])).
% 1.34/0.54  fof(f5,axiom,(
% 1.34/0.54    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 1.34/0.54  fof(f103,plain,(
% 1.34/0.54    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X1 | ~r2_hidden(X2,X3) | sK2 != X3 | sK2 != k1_relat_1(sK4(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 1.34/0.54    inference(subsumption_resolution,[],[f102,f43])).
% 1.34/0.54  fof(f43,plain,(
% 1.34/0.54    ( ! [X0,X1] : (v1_relat_1(sK4(X0,X1))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f23])).
% 1.34/0.54  fof(f102,plain,(
% 1.34/0.54    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X1 | ~r2_hidden(X2,X3) | sK2 != X3 | sK2 != k1_relat_1(sK4(X0,X1)) | ~v1_relat_1(sK4(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 1.34/0.54    inference(subsumption_resolution,[],[f89,f44])).
% 1.34/0.54  fof(f44,plain,(
% 1.34/0.54    ( ! [X0,X1] : (v1_funct_1(sK4(X0,X1))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f23])).
% 1.34/0.54  fof(f89,plain,(
% 1.34/0.54    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X1 | ~r2_hidden(X2,X3) | sK2 != X3 | sK2 != k1_relat_1(sK4(X0,X1)) | ~v1_funct_1(sK4(X0,X1)) | ~v1_relat_1(sK4(X0,X1)) | ~r2_hidden(X2,X0)) )),
% 1.34/0.54    inference(superposition,[],[f82,f46])).
% 1.34/0.54  % (26343)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.34/0.54  fof(f46,plain,(
% 1.34/0.54    ( ! [X0,X3,X1] : (k1_funct_1(sK4(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f23])).
% 1.34/0.54  fof(f82,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0) | sK2 != X0 | k1_relat_1(X1) != sK2 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.34/0.54    inference(superposition,[],[f38,f65])).
% 1.34/0.54  fof(f65,plain,(
% 1.34/0.54    ( ! [X0,X1] : (sK3(X0) = X1 | sK2 != X0 | k1_relat_1(X1) != sK2 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.34/0.54    inference(subsumption_resolution,[],[f64,f35])).
% 1.34/0.54  fof(f35,plain,(
% 1.34/0.54    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f19])).
% 1.34/0.54  fof(f19,plain,(
% 1.34/0.54    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0)))),
% 1.34/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f18])).
% 1.34/0.54  fof(f18,plain,(
% 1.34/0.54    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0))))),
% 1.34/0.54    introduced(choice_axiom,[])).
% 1.34/0.54  fof(f11,plain,(
% 1.34/0.54    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.34/0.54    inference(ennf_transformation,[],[f6])).
% 1.34/0.54  fof(f6,axiom,(
% 1.34/0.54    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.34/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 1.34/0.54  fof(f64,plain,(
% 1.34/0.54    ( ! [X0,X1] : (sK2 != X0 | sK3(X0) = X1 | k1_relat_1(X1) != sK2 | ~v1_relat_1(sK3(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.34/0.54    inference(subsumption_resolution,[],[f62,f36])).
% 1.34/0.54  fof(f36,plain,(
% 1.34/0.54    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f19])).
% 1.34/0.54  fof(f62,plain,(
% 1.34/0.54    ( ! [X0,X1] : (sK2 != X0 | sK3(X0) = X1 | k1_relat_1(X1) != sK2 | ~v1_funct_1(sK3(X0)) | ~v1_relat_1(sK3(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.34/0.54    inference(superposition,[],[f32,f37])).
% 1.34/0.54  fof(f37,plain,(
% 1.34/0.54    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 1.34/0.54    inference(cnf_transformation,[],[f19])).
% 1.34/0.54  fof(f32,plain,(
% 1.34/0.54    ( ! [X2,X1] : (k1_relat_1(X2) != sK2 | X1 = X2 | k1_relat_1(X1) != sK2 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f17])).
% 1.34/0.54  fof(f38,plain,(
% 1.34/0.54    ( ! [X2,X0] : (k1_xboole_0 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f19])).
% 1.34/0.54  % SZS output end Proof for theBenchmark
% 1.34/0.54  % (26333)------------------------------
% 1.34/0.54  % (26333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (26333)Termination reason: Refutation
% 1.34/0.54  
% 1.34/0.54  % (26333)Memory used [KB]: 6268
% 1.34/0.54  % (26333)Time elapsed: 0.122 s
% 1.34/0.54  % (26333)------------------------------
% 1.34/0.54  % (26333)------------------------------
% 1.34/0.54  % (26343)Refutation not found, incomplete strategy% (26343)------------------------------
% 1.34/0.54  % (26343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (26335)Refutation not found, incomplete strategy% (26335)------------------------------
% 1.34/0.54  % (26335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (26335)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (26335)Memory used [KB]: 10618
% 1.34/0.54  % (26335)Time elapsed: 0.116 s
% 1.34/0.54  % (26335)------------------------------
% 1.34/0.54  % (26335)------------------------------
% 1.34/0.54  % (26326)Success in time 0.18 s
%------------------------------------------------------------------------------
