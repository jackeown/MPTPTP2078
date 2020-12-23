%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 228 expanded)
%              Number of leaves         :   15 (  73 expanded)
%              Depth                    :   14
%              Number of atoms          :  285 ( 961 expanded)
%              Number of equality atoms :   66 ( 124 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f163,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f60,f87,f101,f114,f138,f162])).

% (24776)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f162,plain,
    ( ~ spl6_2
    | ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f155,f48])).

fof(f48,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f155,plain,
    ( ! [X2] : ~ r1_tarski(k1_xboole_0,k1_tarski(X2))
    | ~ spl6_2
    | ~ spl6_7 ),
    inference(backward_demodulation,[],[f55,f150])).

fof(f150,plain,
    ( k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK1))
    | ~ spl6_2
    | ~ spl6_7 ),
    inference(duplicate_literal_removal,[],[f148])).

fof(f148,plain,
    ( k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK1))
    | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK1))
    | ~ spl6_2
    | ~ spl6_7 ),
    inference(resolution,[],[f145,f143])).

fof(f143,plain,
    ( ! [X6] :
        ( r1_tarski(k10_relat_1(sK0,k1_tarski(X6)),k10_relat_1(sK0,k1_tarski(X6)))
        | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(X6)) )
    | ~ spl6_7 ),
    inference(superposition,[],[f47,f113])).

fof(f113,plain,
    ( ! [X0] :
        ( k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK3(sK0,X0))
        | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(X0)) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl6_7
  <=> ! [X0] :
        ( k1_xboole_0 = k10_relat_1(sK0,k1_tarski(X0))
        | k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK3(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f47,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f145,plain,
    ( ! [X8] :
        ( ~ r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k10_relat_1(sK0,k1_tarski(X8)))
        | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(X8)) )
    | ~ spl6_2
    | ~ spl6_7 ),
    inference(superposition,[],[f55,f113])).

fof(f55,plain,
    ( ! [X2] : ~ r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl6_2
  <=> ! [X2] : ~ r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f138,plain,(
    ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | ~ spl6_5 ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,
    ( ! [X1] : k1_tarski(X1) != k1_tarski(sK2(sK4(sK0)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl6_5
  <=> ! [X1] : k1_tarski(X1) != k1_tarski(sK2(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f114,plain,
    ( ~ spl6_1
    | spl6_7 ),
    inference(avatar_split_clause,[],[f110,f112,f50])).

fof(f50,plain,
    ( spl6_1
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f110,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(sK0,k1_tarski(X0))
      | k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK3(sK0,X0))
      | ~ v2_funct_1(sK0) ) ),
    inference(subsumption_resolution,[],[f109,f32])).

fof(f32,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ! [X2] : ~ r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2))
      | ~ v2_funct_1(sK0) )
    & ( ! [X3] : r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(sK2(X3)))
      | v2_funct_1(sK0) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ( ? [X1] :
            ! [X2] : ~ r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))
          | ~ v2_funct_1(X0) )
        & ( ! [X3] :
            ? [X4] : r1_tarski(k10_relat_1(X0,k1_tarski(X3)),k1_tarski(X4))
          | v2_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ? [X1] :
          ! [X2] : ~ r1_tarski(k10_relat_1(sK0,k1_tarski(X1)),k1_tarski(X2))
        | ~ v2_funct_1(sK0) )
      & ( ! [X3] :
          ? [X4] : r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(X4))
        | v2_funct_1(sK0) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
      ! [X2] : ~ r1_tarski(k10_relat_1(sK0,k1_tarski(X1)),k1_tarski(X2))
   => ! [X2] : ~ r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X3] :
      ( ? [X4] : r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(X4))
     => r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(sK2(X3))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ( ? [X1] :
          ! [X2] : ~ r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))
        | ~ v2_funct_1(X0) )
      & ( ! [X3] :
          ? [X4] : r1_tarski(k10_relat_1(X0,k1_tarski(X3)),k1_tarski(X4))
        | v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ( ? [X1] :
          ! [X2] : ~ r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))
        | ~ v2_funct_1(X0) )
      & ( ! [X1] :
          ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))
        | v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( ? [X1] :
          ! [X2] : ~ r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))
        | ~ v2_funct_1(X0) )
      & ( ! [X1] :
          ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))
        | v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ( v2_funct_1(X0)
      <~> ! [X1] :
          ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ( v2_funct_1(X0)
      <~> ! [X1] :
          ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
        <=> ! [X1] :
            ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1] :
          ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_funct_1)).

fof(f109,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(sK0,k1_tarski(X0))
      | k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK3(sK0,X0))
      | ~ v2_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f70,f33])).

fof(f33,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(sK0,k1_tarski(X0))
      | k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK3(sK0,X0))
      | ~ v2_funct_1(sK0)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f61,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_relat_1(X0))
      | k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(sK3(X0,X1))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( ! [X1] :
              ( k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(sK3(X0,X1))
              | ~ r2_hidden(X1,k2_relat_1(X0)) )
          | ~ v2_funct_1(X0) )
        & ( v2_funct_1(X0)
          | ( ! [X4] : k1_tarski(X4) != k10_relat_1(X0,k1_tarski(sK4(X0)))
            & r2_hidden(sK4(X0),k2_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f21,f23,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2)
     => k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(sK3(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ! [X4] : k10_relat_1(X0,k1_tarski(X3)) != k1_tarski(X4)
          & r2_hidden(X3,k2_relat_1(X0)) )
     => ( ! [X4] : k1_tarski(X4) != k10_relat_1(X0,k1_tarski(sK4(X0)))
        & r2_hidden(sK4(X0),k2_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( ! [X1] :
              ( ? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2)
              | ~ r2_hidden(X1,k2_relat_1(X0)) )
          | ~ v2_funct_1(X0) )
        & ( v2_funct_1(X0)
          | ? [X3] :
              ( ! [X4] : k10_relat_1(X0,k1_tarski(X3)) != k1_tarski(X4)
              & r2_hidden(X3,k2_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( ( ! [X1] :
              ( ? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2)
              | ~ r2_hidden(X1,k2_relat_1(X0)) )
          | ~ v2_funct_1(X0) )
        & ( v2_funct_1(X0)
          | ? [X1] :
              ( ! [X2] : k10_relat_1(X0,k1_tarski(X1)) != k1_tarski(X2)
              & r2_hidden(X1,k2_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( ! [X1] :
            ( ? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2)
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( ! [X1] :
            ( ? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2)
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1] :
            ~ ( ! [X2] : k10_relat_1(X0,k1_tarski(X1)) != k1_tarski(X2)
              & r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_funct_1)).

fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_relat_1(sK0))
      | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(X0)) ) ),
    inference(resolution,[],[f32,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
      | r2_hidden(X0,k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k2_relat_1(X1))
          | k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(f101,plain,
    ( spl6_1
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f99,f32])).

fof(f99,plain,
    ( ~ v1_relat_1(sK0)
    | spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f95,f64])).

fof(f64,plain,
    ( r2_hidden(sK4(sK0),k2_relat_1(sK0))
    | spl6_1 ),
    inference(subsumption_resolution,[],[f63,f32])).

fof(f63,plain,
    ( r2_hidden(sK4(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f62,f33])).

fof(f62,plain,
    ( r2_hidden(sK4(sK0),k2_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl6_1 ),
    inference(resolution,[],[f52,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK4(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,
    ( ~ v2_funct_1(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f95,plain,
    ( ~ r2_hidden(sK4(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl6_4 ),
    inference(trivial_inequality_removal,[],[f94])).

fof(f94,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK4(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl6_4 ),
    inference(superposition,[],[f39,f83])).

fof(f83,plain,
    ( k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK4(sK0)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl6_4
  <=> k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f87,plain,
    ( spl6_4
    | spl6_5
    | spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f79,f58,f50,f85,f81])).

fof(f58,plain,
    ( spl6_3
  <=> ! [X3] : r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(sK2(X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f79,plain,
    ( ! [X1] :
        ( k1_tarski(X1) != k1_tarski(sK2(sK4(sK0)))
        | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK4(sK0))) )
    | spl6_1
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f78,f32])).

fof(f78,plain,
    ( ! [X1] :
        ( k1_tarski(X1) != k1_tarski(sK2(sK4(sK0)))
        | ~ v1_relat_1(sK0)
        | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK4(sK0))) )
    | spl6_1
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f77,f33])).

fof(f77,plain,
    ( ! [X1] :
        ( k1_tarski(X1) != k1_tarski(sK2(sK4(sK0)))
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0)
        | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK4(sK0))) )
    | spl6_1
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f74,f52])).

fof(f74,plain,
    ( ! [X1] :
        ( k1_tarski(X1) != k1_tarski(sK2(sK4(sK0)))
        | v2_funct_1(sK0)
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0)
        | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK4(sK0))) )
    | ~ spl6_3 ),
    inference(superposition,[],[f37,f67])).

fof(f67,plain,
    ( ! [X0] :
        ( k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK2(X0))
        | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(X0)) )
    | ~ spl6_3 ),
    inference(resolution,[],[f59,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,
    ( ! [X3] : r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(sK2(X3)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f37,plain,(
    ! [X4,X0] :
      ( k1_tarski(X4) != k10_relat_1(X0,k1_tarski(sK4(X0)))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f34,f58,f50])).

fof(f34,plain,(
    ! [X3] :
      ( r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(sK2(X3)))
      | v2_funct_1(sK0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f35,f54,f50])).

fof(f35,plain,(
    ! [X2] :
      ( ~ r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2))
      | ~ v2_funct_1(sK0) ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:28:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.52  % (24784)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (24782)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (24783)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (24799)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (24792)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (24784)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (24777)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f163,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f56,f60,f87,f101,f114,f138,f162])).
% 0.21/0.53  % (24776)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    ~spl6_2 | ~spl6_7),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f161])).
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    $false | (~spl6_2 | ~spl6_7)),
% 0.21/0.53    inference(subsumption_resolution,[],[f155,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 0.21/0.53    inference(equality_resolution,[],[f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.21/0.53    inference(flattening,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.21/0.53    inference(nnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).
% 0.21/0.53  fof(f155,plain,(
% 0.21/0.53    ( ! [X2] : (~r1_tarski(k1_xboole_0,k1_tarski(X2))) ) | (~spl6_2 | ~spl6_7)),
% 0.21/0.53    inference(backward_demodulation,[],[f55,f150])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK1)) | (~spl6_2 | ~spl6_7)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f148])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK1)) | (~spl6_2 | ~spl6_7)),
% 0.21/0.53    inference(resolution,[],[f145,f143])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    ( ! [X6] : (r1_tarski(k10_relat_1(sK0,k1_tarski(X6)),k10_relat_1(sK0,k1_tarski(X6))) | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(X6))) ) | ~spl6_7),
% 0.21/0.53    inference(superposition,[],[f47,f113])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    ( ! [X0] : (k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK3(sK0,X0)) | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(X0))) ) | ~spl6_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f112])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    spl6_7 <=> ! [X0] : (k1_xboole_0 = k10_relat_1(sK0,k1_tarski(X0)) | k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK3(sK0,X0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(k1_tarski(X1),k1_tarski(X1))) )),
% 0.21/0.53    inference(equality_resolution,[],[f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) != X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    ( ! [X8] : (~r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k10_relat_1(sK0,k1_tarski(X8))) | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(X8))) ) | (~spl6_2 | ~spl6_7)),
% 0.21/0.53    inference(superposition,[],[f55,f113])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X2] : (~r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2))) ) | ~spl6_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    spl6_2 <=> ! [X2] : ~r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    ~spl6_5),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f137])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    $false | ~spl6_5),
% 0.21/0.53    inference(equality_resolution,[],[f86])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ( ! [X1] : (k1_tarski(X1) != k1_tarski(sK2(sK4(sK0)))) ) | ~spl6_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f85])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    spl6_5 <=> ! [X1] : k1_tarski(X1) != k1_tarski(sK2(sK4(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    ~spl6_1 | spl6_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f110,f112,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    spl6_1 <=> v2_funct_1(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k10_relat_1(sK0,k1_tarski(X0)) | k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK3(sK0,X0)) | ~v2_funct_1(sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f109,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    v1_relat_1(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    (! [X2] : ~r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2)) | ~v2_funct_1(sK0)) & (! [X3] : r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(sK2(X3))) | v2_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18,f17,f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ? [X0] : ((? [X1] : ! [X2] : ~r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) | ~v2_funct_1(X0)) & (! [X3] : ? [X4] : r1_tarski(k10_relat_1(X0,k1_tarski(X3)),k1_tarski(X4)) | v2_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((? [X1] : ! [X2] : ~r1_tarski(k10_relat_1(sK0,k1_tarski(X1)),k1_tarski(X2)) | ~v2_funct_1(sK0)) & (! [X3] : ? [X4] : r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(X4)) | v2_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ? [X1] : ! [X2] : ~r1_tarski(k10_relat_1(sK0,k1_tarski(X1)),k1_tarski(X2)) => ! [X2] : ~r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X3] : (? [X4] : r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(X4)) => r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(sK2(X3))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0] : ((? [X1] : ! [X2] : ~r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) | ~v2_funct_1(X0)) & (! [X3] : ? [X4] : r1_tarski(k10_relat_1(X0,k1_tarski(X3)),k1_tarski(X4)) | v2_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.53    inference(rectify,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0] : ((? [X1] : ! [X2] : ~r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) | ~v2_funct_1(X0)) & (! [X1] : ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) | v2_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0] : (((? [X1] : ! [X2] : ~r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) | ~v2_funct_1(X0)) & (! [X1] : ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) | v2_funct_1(X0))) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,plain,(
% 0.21/0.53    ? [X0] : ((v2_funct_1(X0) <~> ! [X1] : ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f7])).
% 0.21/0.53  fof(f7,plain,(
% 0.21/0.53    ? [X0] : ((v2_funct_1(X0) <~> ! [X1] : ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1] : ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))))),
% 0.21/0.53    inference(negated_conjecture,[],[f5])).
% 0.21/0.53  fof(f5,conjecture,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1] : ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_funct_1)).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k10_relat_1(sK0,k1_tarski(X0)) | k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK3(sK0,X0)) | ~v2_funct_1(sK0) | ~v1_relat_1(sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f70,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    v1_funct_1(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k10_relat_1(sK0,k1_tarski(X0)) | k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK3(sK0,X0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) )),
% 0.21/0.53    inference(resolution,[],[f61,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k2_relat_1(X0)) | k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(sK3(X0,X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (((! [X1] : (k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(sK3(X0,X1)) | ~r2_hidden(X1,k2_relat_1(X0))) | ~v2_funct_1(X0)) & (v2_funct_1(X0) | (! [X4] : k1_tarski(X4) != k10_relat_1(X0,k1_tarski(sK4(X0))) & r2_hidden(sK4(X0),k2_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f21,f23,f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2) => k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(sK3(X0,X1)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (? [X3] : (! [X4] : k10_relat_1(X0,k1_tarski(X3)) != k1_tarski(X4) & r2_hidden(X3,k2_relat_1(X0))) => (! [X4] : k1_tarski(X4) != k10_relat_1(X0,k1_tarski(sK4(X0))) & r2_hidden(sK4(X0),k2_relat_1(X0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (((! [X1] : (? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2) | ~r2_hidden(X1,k2_relat_1(X0))) | ~v2_funct_1(X0)) & (v2_funct_1(X0) | ? [X3] : (! [X4] : k10_relat_1(X0,k1_tarski(X3)) != k1_tarski(X4) & r2_hidden(X3,k2_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(rectify,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (((! [X1] : (? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2) | ~r2_hidden(X1,k2_relat_1(X0))) | ~v2_funct_1(X0)) & (v2_funct_1(X0) | ? [X1] : (! [X2] : k10_relat_1(X0,k1_tarski(X1)) != k1_tarski(X2) & r2_hidden(X1,k2_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ! [X0] : ((! [X1] : (? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2) | ~r2_hidden(X1,k2_relat_1(X0))) <=> v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f9])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ! [X0] : ((! [X1] : (? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2) | ~r2_hidden(X1,k2_relat_1(X0))) <=> v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (! [X1] : ~(! [X2] : k10_relat_1(X0,k1_tarski(X1)) != k1_tarski(X2) & r2_hidden(X1,k2_relat_1(X0))) <=> v2_funct_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_funct_1)).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK0)) | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(X0))) )),
% 0.21/0.53    inference(resolution,[],[f32,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1] : (((r2_hidden(X0,k2_relat_1(X1)) | k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1)))) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    spl6_1 | ~spl6_4),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f100])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    $false | (spl6_1 | ~spl6_4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f99,f32])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    ~v1_relat_1(sK0) | (spl6_1 | ~spl6_4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f95,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    r2_hidden(sK4(sK0),k2_relat_1(sK0)) | spl6_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f63,f32])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    r2_hidden(sK4(sK0),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | spl6_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f62,f33])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    r2_hidden(sK4(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl6_1),
% 0.21/0.53    inference(resolution,[],[f52,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK4(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ~v2_funct_1(sK0) | spl6_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f50])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ~r2_hidden(sK4(sK0),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | ~spl6_4),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f94])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK4(sK0),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | ~spl6_4),
% 0.21/0.53    inference(superposition,[],[f39,f83])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK4(sK0))) | ~spl6_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f81])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    spl6_4 <=> k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK4(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    spl6_4 | spl6_5 | spl6_1 | ~spl6_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f79,f58,f50,f85,f81])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    spl6_3 <=> ! [X3] : r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(sK2(X3)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ( ! [X1] : (k1_tarski(X1) != k1_tarski(sK2(sK4(sK0))) | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK4(sK0)))) ) | (spl6_1 | ~spl6_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f78,f32])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ( ! [X1] : (k1_tarski(X1) != k1_tarski(sK2(sK4(sK0))) | ~v1_relat_1(sK0) | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK4(sK0)))) ) | (spl6_1 | ~spl6_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f77,f33])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X1] : (k1_tarski(X1) != k1_tarski(sK2(sK4(sK0))) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK4(sK0)))) ) | (spl6_1 | ~spl6_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f74,f52])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X1] : (k1_tarski(X1) != k1_tarski(sK2(sK4(sK0))) | v2_funct_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(sK4(sK0)))) ) | ~spl6_3),
% 0.21/0.53    inference(superposition,[],[f37,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X0] : (k10_relat_1(sK0,k1_tarski(X0)) = k1_tarski(sK2(X0)) | k1_xboole_0 = k10_relat_1(sK0,k1_tarski(X0))) ) | ~spl6_3),
% 0.21/0.53    inference(resolution,[],[f59,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X3] : (r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(sK2(X3)))) ) | ~spl6_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f58])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X4,X0] : (k1_tarski(X4) != k10_relat_1(X0,k1_tarski(sK4(X0))) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    spl6_1 | spl6_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f34,f58,f50])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X3] : (r1_tarski(k10_relat_1(sK0,k1_tarski(X3)),k1_tarski(sK2(X3))) | v2_funct_1(sK0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ~spl6_1 | spl6_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f35,f54,f50])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X2] : (~r1_tarski(k10_relat_1(sK0,k1_tarski(sK1)),k1_tarski(X2)) | ~v2_funct_1(sK0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (24784)------------------------------
% 0.21/0.53  % (24784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (24784)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (24784)Memory used [KB]: 10746
% 0.21/0.53  % (24784)Time elapsed: 0.118 s
% 0.21/0.53  % (24784)------------------------------
% 0.21/0.53  % (24784)------------------------------
% 0.21/0.53  % (24778)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (24775)Success in time 0.175 s
%------------------------------------------------------------------------------
