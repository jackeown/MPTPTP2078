%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 135 expanded)
%              Number of leaves         :   25 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  261 ( 361 expanded)
%              Number of equality atoms :   29 (  36 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f198,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f68,f78,f83,f89,f95,f105,f113,f118,f161,f197])).

fof(f197,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | ~ spl5_10
    | ~ spl5_11
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_10
    | ~ spl5_11
    | spl5_13 ),
    inference(subsumption_resolution,[],[f195,f67])).

fof(f67,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl5_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f195,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_11
    | spl5_13 ),
    inference(subsumption_resolution,[],[f194,f62])).

fof(f62,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl5_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f194,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_10
    | ~ spl5_11
    | spl5_13 ),
    inference(subsumption_resolution,[],[f193,f112])).

fof(f112,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl5_10
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f193,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_11
    | spl5_13 ),
    inference(subsumption_resolution,[],[f177,f117])).

fof(f117,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl5_11
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f177,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_13 ),
    inference(resolution,[],[f46,f160])).

fof(f160,plain,
    ( ~ sP1(k1_xboole_0,sK2)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl5_13
  <=> sP1(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f46,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f17,f19,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          | ~ r2_hidden(X2,k1_relat_1(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ( v5_funct_1(X1,X0)
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

% (17716)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

fof(f161,plain,
    ( ~ spl5_13
    | spl5_1
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f155,f75,f55,f158])).

fof(f55,plain,
    ( spl5_1
  <=> v5_funct_1(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f75,plain,
    ( spl5_5
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f155,plain,
    ( ~ sP1(k1_xboole_0,sK2)
    | spl5_1
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f57,f153,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v5_funct_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( v5_funct_1(X0,X1)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v5_funct_1(X0,X1) ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ( ( v5_funct_1(X1,X0)
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | ~ v5_funct_1(X1,X0) ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f153,plain,
    ( ! [X0] : sP0(X0,k1_xboole_0)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f151,f132])).

fof(f132,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f47,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f47,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f151,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0,k1_xboole_0),k1_xboole_0)
        | sP0(X0,k1_xboole_0) )
    | ~ spl5_5 ),
    inference(superposition,[],[f44,f77])).

fof(f77,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k1_relat_1(X1))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ r2_hidden(k1_funct_1(X1,sK3(X0,X1)),k1_funct_1(X0,sK3(X0,X1)))
          & r2_hidden(sK3(X0,X1),k1_relat_1(X1)) ) )
      & ( ! [X3] :
            ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
            | ~ r2_hidden(X3,k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK3(X0,X1)),k1_funct_1(X0,sK3(X0,X1)))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
            & r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ! [X3] :
            ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
            | ~ r2_hidden(X3,k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
            & r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ! [X2] :
            ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
            | ~ r2_hidden(X2,k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f57,plain,
    ( ~ v5_funct_1(k1_xboole_0,sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f118,plain,
    ( spl5_11
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f107,f102,f86,f115])).

fof(f86,plain,
    ( spl5_7
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f102,plain,
    ( spl5_9
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f107,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(backward_demodulation,[],[f88,f104])).

fof(f104,plain,
    ( k1_xboole_0 = sK4
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f102])).

fof(f88,plain,
    ( v1_funct_1(sK4)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f113,plain,
    ( spl5_10
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f106,f102,f92,f110])).

fof(f92,plain,
    ( spl5_8
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f106,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(backward_demodulation,[],[f94,f104])).

fof(f94,plain,
    ( v1_relat_1(sK4)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f105,plain,
    ( spl5_9
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f96,f80,f102])).

fof(f80,plain,
    ( spl5_6
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f96,plain,
    ( k1_xboole_0 = sK4
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f82,f40])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f82,plain,
    ( v1_xboole_0(sK4)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f95,plain,
    ( spl5_8
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f90,f80,f92])).

fof(f90,plain,
    ( v1_relat_1(sK4)
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f82,f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f89,plain,
    ( spl5_7
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f84,f80,f86])).

fof(f84,plain,
    ( v1_funct_1(sK4)
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f82,f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f83,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f51,f80])).

fof(f51,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f2,f31])).

fof(f31,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK4) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f78,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f36,f75])).

fof(f36,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f68,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f33,f65])).

fof(f33,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ v5_funct_1(k1_xboole_0,sK2)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ~ v5_funct_1(k1_xboole_0,X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v5_funct_1(k1_xboole_0,sK2)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => v5_funct_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

fof(f63,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f34,f60])).

fof(f34,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f35,f55])).

fof(f35,plain,(
    ~ v5_funct_1(k1_xboole_0,sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (17712)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (17717)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (17706)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (17718)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (17709)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (17720)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (17717)Refutation not found, incomplete strategy% (17717)------------------------------
% 0.22/0.49  % (17717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (17717)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (17717)Memory used [KB]: 1663
% 0.22/0.49  % (17717)Time elapsed: 0.003 s
% 0.22/0.49  % (17717)------------------------------
% 0.22/0.49  % (17717)------------------------------
% 0.22/0.49  % (17724)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (17724)Refutation not found, incomplete strategy% (17724)------------------------------
% 0.22/0.49  % (17724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (17724)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (17724)Memory used [KB]: 10490
% 0.22/0.49  % (17724)Time elapsed: 0.070 s
% 0.22/0.49  % (17724)------------------------------
% 0.22/0.49  % (17724)------------------------------
% 0.22/0.49  % (17720)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f198,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f58,f63,f68,f78,f83,f89,f95,f105,f113,f118,f161,f197])).
% 0.22/0.49  fof(f197,plain,(
% 0.22/0.49    ~spl5_2 | ~spl5_3 | ~spl5_10 | ~spl5_11 | spl5_13),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f196])).
% 0.22/0.49  fof(f196,plain,(
% 0.22/0.49    $false | (~spl5_2 | ~spl5_3 | ~spl5_10 | ~spl5_11 | spl5_13)),
% 0.22/0.49    inference(subsumption_resolution,[],[f195,f67])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    v1_relat_1(sK2) | ~spl5_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    spl5_3 <=> v1_relat_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.49  fof(f195,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | (~spl5_2 | ~spl5_10 | ~spl5_11 | spl5_13)),
% 0.22/0.49    inference(subsumption_resolution,[],[f194,f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    v1_funct_1(sK2) | ~spl5_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    spl5_2 <=> v1_funct_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.49  fof(f194,plain,(
% 0.22/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl5_10 | ~spl5_11 | spl5_13)),
% 0.22/0.49    inference(subsumption_resolution,[],[f193,f112])).
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    v1_relat_1(k1_xboole_0) | ~spl5_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f110])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    spl5_10 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.49  fof(f193,plain,(
% 0.22/0.49    ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl5_11 | spl5_13)),
% 0.22/0.49    inference(subsumption_resolution,[],[f177,f117])).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    v1_funct_1(k1_xboole_0) | ~spl5_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f115])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    spl5_11 <=> v1_funct_1(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.49  fof(f177,plain,(
% 0.22/0.49    ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl5_13),
% 0.22/0.49    inference(resolution,[],[f46,f160])).
% 0.22/0.49  fof(f160,plain,(
% 0.22/0.49    ~sP1(k1_xboole_0,sK2) | spl5_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f158])).
% 0.22/0.49  fof(f158,plain,(
% 0.22/0.49    spl5_13 <=> sP1(k1_xboole_0,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0,X1] : (sP1(X1,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (sP1(X1,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(definition_folding,[],[f17,f19,f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1))))),
% 0.22/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X1,X0] : ((v5_funct_1(X1,X0) <=> sP0(X0,X1)) | ~sP1(X1,X0))),
% 0.22/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  % (17716)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).
% 0.22/0.49  fof(f161,plain,(
% 0.22/0.49    ~spl5_13 | spl5_1 | ~spl5_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f155,f75,f55,f158])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    spl5_1 <=> v5_funct_1(k1_xboole_0,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    spl5_5 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    ~sP1(k1_xboole_0,sK2) | (spl5_1 | ~spl5_5)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f57,f153,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v5_funct_1(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1] : (((v5_funct_1(X0,X1) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v5_funct_1(X0,X1))) | ~sP1(X0,X1))),
% 0.22/0.49    inference(rectify,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X1,X0] : (((v5_funct_1(X1,X0) | ~sP0(X0,X1)) & (sP0(X0,X1) | ~v5_funct_1(X1,X0))) | ~sP1(X1,X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f19])).
% 0.22/0.49  fof(f153,plain,(
% 0.22/0.49    ( ! [X0] : (sP0(X0,k1_xboole_0)) ) | ~spl5_5),
% 0.22/0.49    inference(subsumption_resolution,[],[f151,f132])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.49    inference(superposition,[],[f47,f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.49    inference(flattening,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.49    inference(nnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.22/0.49  fof(f151,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK3(X0,k1_xboole_0),k1_xboole_0) | sP0(X0,k1_xboole_0)) ) | ~spl5_5),
% 0.22/0.49    inference(superposition,[],[f44,f77])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl5_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f75])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k1_relat_1(X1)) | sP0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0,X1] : ((sP0(X0,X1) | (~r2_hidden(k1_funct_1(X1,sK3(X0,X1)),k1_funct_1(X0,sK3(X0,X1))) & r2_hidden(sK3(X0,X1),k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1))) => (~r2_hidden(k1_funct_1(X1,sK3(X0,X1)),k1_funct_1(X0,sK3(X0,X1))) & r2_hidden(sK3(X0,X1),k1_relat_1(X1))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 0.22/0.49    inference(rectify,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 0.22/0.49    inference(nnf_transformation,[],[f18])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ~v5_funct_1(k1_xboole_0,sK2) | spl5_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f55])).
% 0.22/0.49  fof(f118,plain,(
% 0.22/0.49    spl5_11 | ~spl5_7 | ~spl5_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f107,f102,f86,f115])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    spl5_7 <=> v1_funct_1(sK4)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    spl5_9 <=> k1_xboole_0 = sK4),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    v1_funct_1(k1_xboole_0) | (~spl5_7 | ~spl5_9)),
% 0.22/0.49    inference(backward_demodulation,[],[f88,f104])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    k1_xboole_0 = sK4 | ~spl5_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f102])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    v1_funct_1(sK4) | ~spl5_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f86])).
% 0.22/0.49  fof(f113,plain,(
% 0.22/0.49    spl5_10 | ~spl5_8 | ~spl5_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f106,f102,f92,f110])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    spl5_8 <=> v1_relat_1(sK4)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    v1_relat_1(k1_xboole_0) | (~spl5_8 | ~spl5_9)),
% 0.22/0.49    inference(backward_demodulation,[],[f94,f104])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    v1_relat_1(sK4) | ~spl5_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f92])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    spl5_9 | ~spl5_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f96,f80,f102])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    spl5_6 <=> v1_xboole_0(sK4)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    k1_xboole_0 = sK4 | ~spl5_6),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f82,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    v1_xboole_0(sK4) | ~spl5_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f80])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    spl5_8 | ~spl5_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f90,f80,f92])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    v1_relat_1(sK4) | ~spl5_6),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f82,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    spl5_7 | ~spl5_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f84,f80,f86])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    v1_funct_1(sK4) | ~spl5_6),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f82,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    spl5_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f51,f80])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    v1_xboole_0(sK4)),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    v1_xboole_0(sK4)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f2,f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK4)),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ? [X0] : v1_xboole_0(X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    spl5_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f36,f75])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    spl5_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f33,f65])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    v1_relat_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ~v5_funct_1(k1_xboole_0,sK2) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v5_funct_1(k1_xboole_0,sK2) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.22/0.49    inference(negated_conjecture,[],[f9])).
% 0.22/0.49  fof(f9,conjecture,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    spl5_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f34,f60])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    v1_funct_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ~spl5_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f35,f55])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ~v5_funct_1(k1_xboole_0,sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (17720)------------------------------
% 0.22/0.49  % (17720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (17720)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (17720)Memory used [KB]: 10618
% 0.22/0.49  % (17720)Time elapsed: 0.074 s
% 0.22/0.49  % (17720)------------------------------
% 0.22/0.49  % (17720)------------------------------
% 0.22/0.49  % (17716)Refutation not found, incomplete strategy% (17716)------------------------------
% 0.22/0.49  % (17716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (17716)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (17716)Memory used [KB]: 6012
% 0.22/0.49  % (17716)Time elapsed: 0.002 s
% 0.22/0.49  % (17716)------------------------------
% 0.22/0.49  % (17716)------------------------------
% 0.22/0.49  % (17713)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (17703)Success in time 0.127 s
%------------------------------------------------------------------------------
