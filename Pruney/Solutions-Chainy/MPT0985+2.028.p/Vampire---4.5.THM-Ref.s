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
% DateTime   : Thu Dec  3 13:02:03 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  208 ( 481 expanded)
%              Number of leaves         :   41 ( 160 expanded)
%              Depth                    :   14
%              Number of atoms          :  681 (1830 expanded)
%              Number of equality atoms :  147 ( 389 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1657,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f125,f139,f149,f152,f164,f243,f264,f276,f298,f359,f383,f588,f594,f739,f754,f1106,f1120,f1121,f1314,f1460,f1622])).

fof(f1622,plain,
    ( ~ spl6_13
    | ~ spl6_1
    | spl6_3
    | ~ spl6_12
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f1607,f728,f355,f295,f240,f122,f114,f252])).

fof(f252,plain,
    ( spl6_13
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f114,plain,
    ( spl6_1
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f122,plain,
    ( spl6_3
  <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f240,plain,
    ( spl6_12
  <=> k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f295,plain,
    ( spl6_20
  <=> k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f355,plain,
    ( spl6_25
  <=> sK2 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f728,plain,
    ( spl6_40
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f1607,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl6_12
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_40 ),
    inference(forward_demodulation,[],[f1604,f755])).

fof(f755,plain,
    ( sK1 = k2_relat_1(k2_funct_1(sK3))
    | ~ spl6_20
    | ~ spl6_40 ),
    inference(backward_demodulation,[],[f297,f730])).

fof(f730,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f728])).

fof(f297,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f295])).

fof(f1604,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK3)))))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl6_12
    | ~ spl6_25 ),
    inference(superposition,[],[f71,f384])).

fof(f384,plain,
    ( sK2 = k1_relat_1(k2_funct_1(sK3))
    | ~ spl6_12
    | ~ spl6_25 ),
    inference(backward_demodulation,[],[f242,f357])).

fof(f357,plain,
    ( sK2 = k2_relat_1(sK3)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f355])).

fof(f242,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f240])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f1460,plain,
    ( spl6_3
    | ~ spl6_16
    | ~ spl6_45 ),
    inference(avatar_contradiction_clause,[],[f1455])).

fof(f1455,plain,
    ( $false
    | spl6_3
    | ~ spl6_16
    | ~ spl6_45 ),
    inference(resolution,[],[f1286,f614])).

fof(f614,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f607,f104])).

fof(f104,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f607,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f605,f104])).

fof(f605,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | ~ r1_tarski(X1,X0)
      | r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f603,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f603,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | ~ r1_tarski(X0,k1_xboole_0)
      | ~ r1_tarski(X2,X0) ) ),
    inference(resolution,[],[f184,f126])).

fof(f126,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f65,f64])).

fof(f64,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f184,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(X4,X3)
      | ~ r2_hidden(X5,X6)
      | ~ r1_tarski(X6,X4) ) ),
    inference(resolution,[],[f174,f79])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f174,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X3,X4)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(X4,X2) ) ),
    inference(resolution,[],[f172,f79])).

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f103,f63])).

fof(f63,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f1286,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl6_3
    | ~ spl6_16
    | ~ spl6_45 ),
    inference(backward_demodulation,[],[f1133,f1283])).

fof(f1283,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl6_16
    | ~ spl6_45 ),
    inference(forward_demodulation,[],[f268,f866])).

fof(f866,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f864])).

fof(f864,plain,
    ( spl6_45
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f268,plain,
    ( k1_xboole_0 = k2_funct_1(sK3)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl6_16
  <=> k1_xboole_0 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f1133,plain,
    ( ~ r1_tarski(k2_funct_1(k1_xboole_0),k1_xboole_0)
    | spl6_3
    | ~ spl6_45 ),
    inference(backward_demodulation,[],[f177,f866])).

fof(f177,plain,
    ( ~ r1_tarski(k2_funct_1(sK3),k1_xboole_0)
    | spl6_3 ),
    inference(resolution,[],[f175,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f175,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0))
    | spl6_3 ),
    inference(resolution,[],[f173,f153])).

fof(f153,plain,
    ( ~ r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,sK1))
    | spl6_3 ),
    inference(resolution,[],[f83,f124])).

fof(f124,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f122])).

fof(f173,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f172,f80])).

fof(f1314,plain,
    ( spl6_2
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_25
    | ~ spl6_39 ),
    inference(avatar_contradiction_clause,[],[f1311])).

fof(f1311,plain,
    ( $false
    | spl6_2
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_25
    | ~ spl6_39 ),
    inference(resolution,[],[f946,f544])).

fof(f544,plain,(
    ! [X1] : v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(superposition,[],[f92,f524])).

fof(f524,plain,(
    ! [X2] : k1_xboole_0 = sK5(k1_xboole_0,X2) ),
    inference(resolution,[],[f517,f158])).

fof(f158,plain,(
    ! [X1] : m1_subset_1(sK5(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f87,f107])).

fof(f107,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f87,plain,(
    ! [X0,X1] : m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK5(X0,X1),X0,X1)
      & v1_funct_1(sK5(X0,X1))
      & v5_relat_1(sK5(X0,X1),X1)
      & v4_relat_1(sK5(X0,X1),X0)
      & v1_relat_1(sK5(X0,X1))
      & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK5(X0,X1),X0,X1)
        & v1_funct_1(sK5(X0,X1))
        & v5_relat_1(sK5(X0,X1),X1)
        & v4_relat_1(sK5(X0,X1),X0)
        & v1_relat_1(sK5(X0,X1))
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f517,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f181,f126])).

fof(f181,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | X1 = X2 ) ),
    inference(resolution,[],[f170,f173])).

fof(f170,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | X1 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f78,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f92,plain,(
    ! [X0,X1] : v1_funct_2(sK5(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f53])).

fof(f946,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | spl6_2
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_25
    | ~ spl6_39 ),
    inference(forward_demodulation,[],[f945,f268])).

fof(f945,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1)
    | spl6_2
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_25
    | ~ spl6_39 ),
    inference(forward_demodulation,[],[f120,f892])).

fof(f892,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_25
    | ~ spl6_39 ),
    inference(forward_demodulation,[],[f891,f585])).

fof(f585,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f583])).

fof(f583,plain,
    ( spl6_39
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f891,plain,
    ( sK2 = k1_relat_1(k1_xboole_0)
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_25 ),
    inference(forward_demodulation,[],[f384,f268])).

fof(f120,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl6_2
  <=> v1_funct_2(k2_funct_1(sK3),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1121,plain,
    ( ~ spl6_13
    | spl6_16
    | ~ spl6_42
    | ~ spl6_12
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f431,f355,f240,f736,f266,f252])).

fof(f736,plain,
    ( spl6_42
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f431,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = k2_funct_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl6_12
    | ~ spl6_25 ),
    inference(superposition,[],[f67,f384])).

fof(f67,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f1120,plain,
    ( ~ spl6_6
    | spl6_45
    | ~ spl6_42
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f1067,f355,f736,f864,f142])).

fof(f142,plain,
    ( spl6_6
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f1067,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl6_25 ),
    inference(superposition,[],[f68,f357])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1106,plain,
    ( spl6_2
    | ~ spl6_15
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_40 ),
    inference(avatar_contradiction_clause,[],[f1105])).

fof(f1105,plain,
    ( $false
    | spl6_2
    | ~ spl6_15
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_40 ),
    inference(resolution,[],[f760,f120])).

fof(f760,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ spl6_15
    | ~ spl6_20
    | ~ spl6_25
    | ~ spl6_40 ),
    inference(backward_demodulation,[],[f388,f730])).

fof(f388,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3))
    | ~ spl6_15
    | ~ spl6_20
    | ~ spl6_25 ),
    inference(backward_demodulation,[],[f300,f357])).

fof(f300,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3))
    | ~ spl6_15
    | ~ spl6_20 ),
    inference(backward_demodulation,[],[f263,f297])).

fof(f263,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3)))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl6_15
  <=> v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f754,plain,(
    spl6_41 ),
    inference(avatar_contradiction_clause,[],[f752])).

fof(f752,plain,
    ( $false
    | spl6_41 ),
    inference(resolution,[],[f734,f58])).

fof(f58,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & sK2 = k2_relset_1(sK1,sK2,sK3)
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f41])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
        | ~ v1_funct_1(k2_funct_1(sK3)) )
      & sK2 = k2_relset_1(sK1,sK2,sK3)
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f734,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | spl6_41 ),
    inference(avatar_component_clause,[],[f732])).

fof(f732,plain,
    ( spl6_41
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f739,plain,
    ( spl6_40
    | ~ spl6_41
    | spl6_42 ),
    inference(avatar_split_clause,[],[f722,f736,f732,f728])).

fof(f722,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_funct_2(sK3,sK1,sK2)
    | sK1 = k1_relat_1(sK3) ),
    inference(resolution,[],[f651,f59])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f42])).

fof(f651,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_xboole_0 = X4
      | ~ v1_funct_2(X5,X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(duplicate_literal_removal,[],[f648])).

fof(f648,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | k1_xboole_0 = X4
      | ~ v1_funct_2(X5,X3,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f476,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f476,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X2,X0) = X1
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X0,X1,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f96,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f37,f39])).

fof(f39,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f594,plain,(
    ~ spl6_38 ),
    inference(avatar_contradiction_clause,[],[f589])).

fof(f589,plain,
    ( $false
    | ~ spl6_38 ),
    inference(resolution,[],[f581,f544])).

fof(f581,plain,
    ( ! [X1] : ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f580])).

fof(f580,plain,
    ( spl6_38
  <=> ! [X1] : ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f588,plain,
    ( spl6_38
    | spl6_39
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f587,f132,f583,f580])).

fof(f132,plain,
    ( spl6_5
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f587,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f577,f107])).

fof(f577,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(superposition,[],[f94,f574])).

fof(f574,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(resolution,[],[f427,f126])).

fof(f427,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_2(X0,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X0) ) ),
    inference(forward_demodulation,[],[f426,f107])).

fof(f426,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(resolution,[],[f109,f100])).

fof(f109,plain,(
    ! [X2,X1] :
      ( ~ sP0(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X1,k1_xboole_0,X2)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X1) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 != X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f383,plain,(
    spl6_24 ),
    inference(avatar_contradiction_clause,[],[f381])).

fof(f381,plain,
    ( $false
    | spl6_24 ),
    inference(resolution,[],[f353,f59])).

fof(f353,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl6_24 ),
    inference(avatar_component_clause,[],[f351])).

fof(f351,plain,
    ( spl6_24
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f359,plain,
    ( ~ spl6_24
    | spl6_25 ),
    inference(avatar_split_clause,[],[f349,f355,f351])).

fof(f349,plain,
    ( sK2 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(superposition,[],[f61,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f61,plain,(
    sK2 = k2_relset_1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f298,plain,
    ( ~ spl6_6
    | ~ spl6_7
    | spl6_20 ),
    inference(avatar_split_clause,[],[f293,f295,f146,f142])).

fof(f146,plain,
    ( spl6_7
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f293,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f75,f60])).

fof(f60,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f276,plain,
    ( ~ spl6_6
    | ~ spl6_7
    | spl6_13 ),
    inference(avatar_split_clause,[],[f274,f252,f146,f142])).

fof(f274,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl6_13 ),
    inference(resolution,[],[f254,f72])).

fof(f72,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f254,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | spl6_13 ),
    inference(avatar_component_clause,[],[f252])).

fof(f264,plain,
    ( ~ spl6_13
    | ~ spl6_1
    | spl6_15
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f249,f240,f261,f114,f252])).

fof(f249,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl6_12 ),
    inference(superposition,[],[f70,f242])).

fof(f70,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f243,plain,
    ( ~ spl6_6
    | ~ spl6_7
    | spl6_12 ),
    inference(avatar_split_clause,[],[f238,f240,f146,f142])).

fof(f238,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f74,f60])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f164,plain,(
    spl6_6 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | spl6_6 ),
    inference(resolution,[],[f159,f59])).

fof(f159,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_6 ),
    inference(resolution,[],[f93,f144])).

fof(f144,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f142])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f152,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl6_7 ),
    inference(resolution,[],[f148,f57])).

fof(f57,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f148,plain,
    ( ~ v1_funct_1(sK3)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f146])).

fof(f149,plain,
    ( ~ spl6_6
    | ~ spl6_7
    | spl6_1 ),
    inference(avatar_split_clause,[],[f140,f114,f146,f142])).

fof(f140,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl6_1 ),
    inference(resolution,[],[f73,f116])).

fof(f116,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f73,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f139,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | spl6_5 ),
    inference(resolution,[],[f134,f126])).

fof(f134,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f132])).

fof(f125,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f62,f122,f118,f114])).

fof(f62,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:50:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (20237)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (20261)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (20236)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.23/0.51  % (20238)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.23/0.52  % (20241)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.23/0.52  % (20245)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.23/0.52  % (20258)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.23/0.52  % (20251)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.23/0.52  % (20246)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.23/0.53  % (20234)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.23/0.53  % (20243)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.23/0.53  % (20255)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.23/0.53  % (20243)Refutation not found, incomplete strategy% (20243)------------------------------
% 1.23/0.53  % (20243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (20243)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  % (20243)Memory used [KB]: 10618
% 1.23/0.53  % (20243)Time elapsed: 0.109 s
% 1.23/0.53  % (20243)------------------------------
% 1.23/0.53  % (20243)------------------------------
% 1.23/0.53  % (20247)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.23/0.53  % (20262)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.23/0.53  % (20253)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.36/0.54  % (20233)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.36/0.54  % (20260)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.54  % (20241)Refutation not found, incomplete strategy% (20241)------------------------------
% 1.36/0.54  % (20241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (20241)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  % (20242)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.36/0.54  
% 1.36/0.54  % (20241)Memory used [KB]: 10746
% 1.36/0.54  % (20241)Time elapsed: 0.116 s
% 1.36/0.54  % (20241)------------------------------
% 1.36/0.54  % (20241)------------------------------
% 1.36/0.54  % (20240)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.36/0.54  % (20244)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.36/0.54  % (20239)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.36/0.54  % (20254)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.54  % (20249)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.54  % (20254)Refutation not found, incomplete strategy% (20254)------------------------------
% 1.36/0.54  % (20254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (20254)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (20254)Memory used [KB]: 1791
% 1.36/0.54  % (20254)Time elapsed: 0.142 s
% 1.36/0.54  % (20254)------------------------------
% 1.36/0.54  % (20254)------------------------------
% 1.36/0.55  % (20235)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.36/0.55  % (20252)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.36/0.55  % (20257)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.55  % (20255)Refutation not found, incomplete strategy% (20255)------------------------------
% 1.36/0.55  % (20255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (20255)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (20255)Memory used [KB]: 10874
% 1.36/0.55  % (20255)Time elapsed: 0.106 s
% 1.36/0.55  % (20255)------------------------------
% 1.36/0.55  % (20255)------------------------------
% 1.36/0.55  % (20250)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.55  % (20256)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.55  % (20250)Refutation not found, incomplete strategy% (20250)------------------------------
% 1.36/0.55  % (20250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (20259)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.56  % (20248)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.56  % (20250)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.56  
% 1.36/0.56  % (20250)Memory used [KB]: 10618
% 1.36/0.56  % (20250)Time elapsed: 0.151 s
% 1.36/0.56  % (20250)------------------------------
% 1.36/0.56  % (20250)------------------------------
% 1.36/0.57  % (20245)Refutation found. Thanks to Tanya!
% 1.36/0.57  % SZS status Theorem for theBenchmark
% 1.36/0.58  % SZS output start Proof for theBenchmark
% 1.36/0.58  fof(f1657,plain,(
% 1.36/0.58    $false),
% 1.36/0.58    inference(avatar_sat_refutation,[],[f125,f139,f149,f152,f164,f243,f264,f276,f298,f359,f383,f588,f594,f739,f754,f1106,f1120,f1121,f1314,f1460,f1622])).
% 1.36/0.58  fof(f1622,plain,(
% 1.36/0.58    ~spl6_13 | ~spl6_1 | spl6_3 | ~spl6_12 | ~spl6_20 | ~spl6_25 | ~spl6_40),
% 1.36/0.58    inference(avatar_split_clause,[],[f1607,f728,f355,f295,f240,f122,f114,f252])).
% 1.36/0.58  fof(f252,plain,(
% 1.36/0.58    spl6_13 <=> v1_relat_1(k2_funct_1(sK3))),
% 1.36/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.36/0.58  fof(f114,plain,(
% 1.36/0.58    spl6_1 <=> v1_funct_1(k2_funct_1(sK3))),
% 1.36/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.36/0.58  fof(f122,plain,(
% 1.36/0.58    spl6_3 <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.36/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.36/0.58  fof(f240,plain,(
% 1.36/0.58    spl6_12 <=> k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 1.36/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.36/0.58  fof(f295,plain,(
% 1.36/0.58    spl6_20 <=> k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)),
% 1.36/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 1.36/0.58  fof(f355,plain,(
% 1.36/0.58    spl6_25 <=> sK2 = k2_relat_1(sK3)),
% 1.36/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 1.36/0.58  fof(f728,plain,(
% 1.36/0.58    spl6_40 <=> sK1 = k1_relat_1(sK3)),
% 1.36/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 1.36/0.58  fof(f1607,plain,(
% 1.36/0.58    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl6_12 | ~spl6_20 | ~spl6_25 | ~spl6_40)),
% 1.36/0.58    inference(forward_demodulation,[],[f1604,f755])).
% 1.36/0.58  fof(f755,plain,(
% 1.36/0.58    sK1 = k2_relat_1(k2_funct_1(sK3)) | (~spl6_20 | ~spl6_40)),
% 1.36/0.58    inference(backward_demodulation,[],[f297,f730])).
% 1.36/0.58  fof(f730,plain,(
% 1.36/0.58    sK1 = k1_relat_1(sK3) | ~spl6_40),
% 1.36/0.58    inference(avatar_component_clause,[],[f728])).
% 1.36/0.58  fof(f297,plain,(
% 1.36/0.58    k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) | ~spl6_20),
% 1.36/0.58    inference(avatar_component_clause,[],[f295])).
% 1.36/0.58  fof(f1604,plain,(
% 1.36/0.58    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k2_relat_1(k2_funct_1(sK3))))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl6_12 | ~spl6_25)),
% 1.36/0.58    inference(superposition,[],[f71,f384])).
% 1.36/0.58  fof(f384,plain,(
% 1.36/0.58    sK2 = k1_relat_1(k2_funct_1(sK3)) | (~spl6_12 | ~spl6_25)),
% 1.36/0.58    inference(backward_demodulation,[],[f242,f357])).
% 1.36/0.58  fof(f357,plain,(
% 1.36/0.58    sK2 = k2_relat_1(sK3) | ~spl6_25),
% 1.36/0.58    inference(avatar_component_clause,[],[f355])).
% 1.36/0.58  fof(f242,plain,(
% 1.36/0.58    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~spl6_12),
% 1.36/0.58    inference(avatar_component_clause,[],[f240])).
% 1.36/0.58  fof(f71,plain,(
% 1.36/0.58    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f27])).
% 1.36/0.58  fof(f27,plain,(
% 1.36/0.58    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.58    inference(flattening,[],[f26])).
% 1.36/0.58  fof(f26,plain,(
% 1.36/0.58    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.58    inference(ennf_transformation,[],[f18])).
% 1.36/0.58  fof(f18,axiom,(
% 1.36/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 1.36/0.58  fof(f1460,plain,(
% 1.36/0.58    spl6_3 | ~spl6_16 | ~spl6_45),
% 1.36/0.58    inference(avatar_contradiction_clause,[],[f1455])).
% 1.36/0.58  fof(f1455,plain,(
% 1.36/0.58    $false | (spl6_3 | ~spl6_16 | ~spl6_45)),
% 1.36/0.58    inference(resolution,[],[f1286,f614])).
% 1.36/0.58  fof(f614,plain,(
% 1.36/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.36/0.58    inference(resolution,[],[f607,f104])).
% 1.36/0.58  fof(f104,plain,(
% 1.36/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.36/0.58    inference(equality_resolution,[],[f77])).
% 1.36/0.58  fof(f77,plain,(
% 1.36/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.36/0.58    inference(cnf_transformation,[],[f44])).
% 1.36/0.58  fof(f44,plain,(
% 1.36/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.58    inference(flattening,[],[f43])).
% 1.36/0.58  fof(f43,plain,(
% 1.36/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.58    inference(nnf_transformation,[],[f3])).
% 1.36/0.58  fof(f3,axiom,(
% 1.36/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.36/0.58  fof(f607,plain,(
% 1.36/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k1_xboole_0) | r1_tarski(X0,X1)) )),
% 1.36/0.58    inference(resolution,[],[f605,f104])).
% 1.36/0.58  fof(f605,plain,(
% 1.36/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,k1_xboole_0) | ~r1_tarski(X1,X0) | r1_tarski(X1,X2)) )),
% 1.36/0.58    inference(resolution,[],[f603,f80])).
% 1.36/0.58  fof(f80,plain,(
% 1.36/0.58    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f48])).
% 1.36/0.58  fof(f48,plain,(
% 1.36/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.36/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).
% 1.36/0.58  fof(f47,plain,(
% 1.36/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.36/0.58    introduced(choice_axiom,[])).
% 1.36/0.58  fof(f46,plain,(
% 1.36/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.36/0.58    inference(rectify,[],[f45])).
% 1.36/0.58  fof(f45,plain,(
% 1.36/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.36/0.58    inference(nnf_transformation,[],[f32])).
% 1.36/0.58  fof(f32,plain,(
% 1.36/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.36/0.58    inference(ennf_transformation,[],[f1])).
% 1.36/0.58  fof(f1,axiom,(
% 1.36/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.36/0.58  fof(f603,plain,(
% 1.36/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | ~r1_tarski(X0,k1_xboole_0) | ~r1_tarski(X2,X0)) )),
% 1.36/0.58    inference(resolution,[],[f184,f126])).
% 1.36/0.58  fof(f126,plain,(
% 1.36/0.58    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.36/0.58    inference(forward_demodulation,[],[f65,f64])).
% 1.36/0.58  fof(f64,plain,(
% 1.36/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.36/0.58    inference(cnf_transformation,[],[f5])).
% 1.36/0.58  fof(f5,axiom,(
% 1.36/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.36/0.58  fof(f65,plain,(
% 1.36/0.58    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.36/0.58    inference(cnf_transformation,[],[f6])).
% 1.36/0.58  fof(f6,axiom,(
% 1.36/0.58    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.36/0.58  fof(f184,plain,(
% 1.36/0.58    ( ! [X6,X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(X4,X3) | ~r2_hidden(X5,X6) | ~r1_tarski(X6,X4)) )),
% 1.36/0.58    inference(resolution,[],[f174,f79])).
% 1.36/0.58  fof(f79,plain,(
% 1.36/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f48])).
% 1.36/0.58  fof(f174,plain,(
% 1.36/0.58    ( ! [X4,X2,X3] : (~r2_hidden(X3,X4) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(X4,X2)) )),
% 1.36/0.58    inference(resolution,[],[f172,f79])).
% 1.36/0.58  fof(f172,plain,(
% 1.36/0.58    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) )),
% 1.36/0.58    inference(resolution,[],[f103,f63])).
% 1.36/0.58  fof(f63,plain,(
% 1.36/0.58    v1_xboole_0(k1_xboole_0)),
% 1.36/0.58    inference(cnf_transformation,[],[f2])).
% 1.36/0.58  fof(f2,axiom,(
% 1.36/0.58    v1_xboole_0(k1_xboole_0)),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.36/0.58  fof(f103,plain,(
% 1.36/0.58    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f38])).
% 1.36/0.58  fof(f38,plain,(
% 1.36/0.58    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.36/0.58    inference(ennf_transformation,[],[f8])).
% 1.36/0.58  fof(f8,axiom,(
% 1.36/0.58    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.36/0.58  fof(f1286,plain,(
% 1.36/0.58    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (spl6_3 | ~spl6_16 | ~spl6_45)),
% 1.36/0.58    inference(backward_demodulation,[],[f1133,f1283])).
% 1.36/0.58  fof(f1283,plain,(
% 1.36/0.58    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl6_16 | ~spl6_45)),
% 1.36/0.58    inference(forward_demodulation,[],[f268,f866])).
% 1.36/0.58  fof(f866,plain,(
% 1.36/0.58    k1_xboole_0 = sK3 | ~spl6_45),
% 1.36/0.58    inference(avatar_component_clause,[],[f864])).
% 1.36/0.58  fof(f864,plain,(
% 1.36/0.58    spl6_45 <=> k1_xboole_0 = sK3),
% 1.36/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 1.36/0.58  fof(f268,plain,(
% 1.36/0.58    k1_xboole_0 = k2_funct_1(sK3) | ~spl6_16),
% 1.36/0.58    inference(avatar_component_clause,[],[f266])).
% 1.36/0.58  fof(f266,plain,(
% 1.36/0.58    spl6_16 <=> k1_xboole_0 = k2_funct_1(sK3)),
% 1.36/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.36/0.58  fof(f1133,plain,(
% 1.36/0.58    ~r1_tarski(k2_funct_1(k1_xboole_0),k1_xboole_0) | (spl6_3 | ~spl6_45)),
% 1.36/0.58    inference(backward_demodulation,[],[f177,f866])).
% 1.36/0.58  fof(f177,plain,(
% 1.36/0.58    ~r1_tarski(k2_funct_1(sK3),k1_xboole_0) | spl6_3),
% 1.36/0.58    inference(resolution,[],[f175,f83])).
% 1.36/0.58  fof(f83,plain,(
% 1.36/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f49])).
% 1.36/0.58  fof(f49,plain,(
% 1.36/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.36/0.58    inference(nnf_transformation,[],[f7])).
% 1.36/0.58  fof(f7,axiom,(
% 1.36/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.36/0.58  fof(f175,plain,(
% 1.36/0.58    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) | spl6_3),
% 1.36/0.58    inference(resolution,[],[f173,f153])).
% 1.36/0.58  fof(f153,plain,(
% 1.36/0.58    ~r1_tarski(k2_funct_1(sK3),k2_zfmisc_1(sK2,sK1)) | spl6_3),
% 1.36/0.58    inference(resolution,[],[f83,f124])).
% 1.36/0.58  fof(f124,plain,(
% 1.36/0.58    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl6_3),
% 1.36/0.58    inference(avatar_component_clause,[],[f122])).
% 1.36/0.58  fof(f173,plain,(
% 1.36/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) )),
% 1.36/0.58    inference(resolution,[],[f172,f80])).
% 1.36/0.58  fof(f1314,plain,(
% 1.36/0.58    spl6_2 | ~spl6_12 | ~spl6_16 | ~spl6_25 | ~spl6_39),
% 1.36/0.58    inference(avatar_contradiction_clause,[],[f1311])).
% 1.36/0.58  fof(f1311,plain,(
% 1.36/0.58    $false | (spl6_2 | ~spl6_12 | ~spl6_16 | ~spl6_25 | ~spl6_39)),
% 1.36/0.58    inference(resolution,[],[f946,f544])).
% 1.36/0.58  fof(f544,plain,(
% 1.36/0.58    ( ! [X1] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)) )),
% 1.36/0.58    inference(superposition,[],[f92,f524])).
% 1.36/0.58  fof(f524,plain,(
% 1.36/0.58    ( ! [X2] : (k1_xboole_0 = sK5(k1_xboole_0,X2)) )),
% 1.36/0.58    inference(resolution,[],[f517,f158])).
% 1.36/0.58  fof(f158,plain,(
% 1.36/0.58    ( ! [X1] : (m1_subset_1(sK5(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))) )),
% 1.36/0.58    inference(superposition,[],[f87,f107])).
% 1.36/0.58  fof(f107,plain,(
% 1.36/0.58    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.36/0.58    inference(equality_resolution,[],[f85])).
% 1.36/0.58  fof(f85,plain,(
% 1.36/0.58    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.36/0.58    inference(cnf_transformation,[],[f51])).
% 1.36/0.58  fof(f51,plain,(
% 1.36/0.58    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.36/0.58    inference(flattening,[],[f50])).
% 1.36/0.58  fof(f50,plain,(
% 1.36/0.58    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.36/0.58    inference(nnf_transformation,[],[f4])).
% 1.36/0.58  fof(f4,axiom,(
% 1.36/0.58    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.36/0.58  fof(f87,plain,(
% 1.36/0.58    ( ! [X0,X1] : (m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.36/0.58    inference(cnf_transformation,[],[f53])).
% 1.36/0.58  fof(f53,plain,(
% 1.36/0.58    ! [X0,X1] : (v1_funct_2(sK5(X0,X1),X0,X1) & v1_funct_1(sK5(X0,X1)) & v5_relat_1(sK5(X0,X1),X1) & v4_relat_1(sK5(X0,X1),X0) & v1_relat_1(sK5(X0,X1)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f52])).
% 1.36/0.58  fof(f52,plain,(
% 1.36/0.58    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK5(X0,X1),X0,X1) & v1_funct_1(sK5(X0,X1)) & v5_relat_1(sK5(X0,X1),X1) & v4_relat_1(sK5(X0,X1),X0) & v1_relat_1(sK5(X0,X1)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.36/0.58    introduced(choice_axiom,[])).
% 1.36/0.58  fof(f17,axiom,(
% 1.36/0.58    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).
% 1.36/0.58  fof(f517,plain,(
% 1.36/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) )),
% 1.36/0.58    inference(resolution,[],[f181,f126])).
% 1.36/0.58  fof(f181,plain,(
% 1.36/0.58    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | X1 = X2) )),
% 1.36/0.58    inference(resolution,[],[f170,f173])).
% 1.36/0.58  fof(f170,plain,(
% 1.36/0.58    ( ! [X2,X1] : (~r1_tarski(X1,X2) | X1 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(X1))) )),
% 1.36/0.58    inference(resolution,[],[f78,f82])).
% 1.36/0.58  fof(f82,plain,(
% 1.36/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.36/0.58    inference(cnf_transformation,[],[f49])).
% 1.36/0.58  fof(f78,plain,(
% 1.36/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f44])).
% 1.36/0.58  fof(f92,plain,(
% 1.36/0.58    ( ! [X0,X1] : (v1_funct_2(sK5(X0,X1),X0,X1)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f53])).
% 1.36/0.58  fof(f946,plain,(
% 1.36/0.58    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | (spl6_2 | ~spl6_12 | ~spl6_16 | ~spl6_25 | ~spl6_39)),
% 1.36/0.58    inference(forward_demodulation,[],[f945,f268])).
% 1.36/0.58  fof(f945,plain,(
% 1.36/0.58    ~v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1) | (spl6_2 | ~spl6_12 | ~spl6_16 | ~spl6_25 | ~spl6_39)),
% 1.36/0.58    inference(forward_demodulation,[],[f120,f892])).
% 1.36/0.58  fof(f892,plain,(
% 1.36/0.58    k1_xboole_0 = sK2 | (~spl6_12 | ~spl6_16 | ~spl6_25 | ~spl6_39)),
% 1.36/0.58    inference(forward_demodulation,[],[f891,f585])).
% 1.36/0.58  fof(f585,plain,(
% 1.36/0.58    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl6_39),
% 1.36/0.58    inference(avatar_component_clause,[],[f583])).
% 1.36/0.58  fof(f583,plain,(
% 1.36/0.58    spl6_39 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.36/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 1.36/0.58  fof(f891,plain,(
% 1.36/0.58    sK2 = k1_relat_1(k1_xboole_0) | (~spl6_12 | ~spl6_16 | ~spl6_25)),
% 1.36/0.58    inference(forward_demodulation,[],[f384,f268])).
% 1.36/0.58  fof(f120,plain,(
% 1.36/0.58    ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | spl6_2),
% 1.36/0.58    inference(avatar_component_clause,[],[f118])).
% 1.36/0.58  fof(f118,plain,(
% 1.36/0.58    spl6_2 <=> v1_funct_2(k2_funct_1(sK3),sK2,sK1)),
% 1.36/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.36/0.58  fof(f1121,plain,(
% 1.36/0.58    ~spl6_13 | spl6_16 | ~spl6_42 | ~spl6_12 | ~spl6_25),
% 1.36/0.58    inference(avatar_split_clause,[],[f431,f355,f240,f736,f266,f252])).
% 1.36/0.58  fof(f736,plain,(
% 1.36/0.58    spl6_42 <=> k1_xboole_0 = sK2),
% 1.36/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 1.36/0.58  fof(f431,plain,(
% 1.36/0.58    k1_xboole_0 != sK2 | k1_xboole_0 = k2_funct_1(sK3) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl6_12 | ~spl6_25)),
% 1.36/0.58    inference(superposition,[],[f67,f384])).
% 1.36/0.58  fof(f67,plain,(
% 1.36/0.58    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f25])).
% 1.36/0.58  fof(f25,plain,(
% 1.36/0.58    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.36/0.58    inference(flattening,[],[f24])).
% 1.36/0.58  fof(f24,plain,(
% 1.36/0.58    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.36/0.58    inference(ennf_transformation,[],[f9])).
% 1.36/0.58  fof(f9,axiom,(
% 1.36/0.58    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.36/0.58  fof(f1120,plain,(
% 1.36/0.58    ~spl6_6 | spl6_45 | ~spl6_42 | ~spl6_25),
% 1.36/0.58    inference(avatar_split_clause,[],[f1067,f355,f736,f864,f142])).
% 1.36/0.58  fof(f142,plain,(
% 1.36/0.58    spl6_6 <=> v1_relat_1(sK3)),
% 1.36/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.36/0.58  fof(f1067,plain,(
% 1.36/0.58    k1_xboole_0 != sK2 | k1_xboole_0 = sK3 | ~v1_relat_1(sK3) | ~spl6_25),
% 1.36/0.58    inference(superposition,[],[f68,f357])).
% 1.36/0.58  fof(f68,plain,(
% 1.36/0.58    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f25])).
% 1.36/0.58  fof(f1106,plain,(
% 1.36/0.58    spl6_2 | ~spl6_15 | ~spl6_20 | ~spl6_25 | ~spl6_40),
% 1.36/0.58    inference(avatar_contradiction_clause,[],[f1105])).
% 1.36/0.58  fof(f1105,plain,(
% 1.36/0.58    $false | (spl6_2 | ~spl6_15 | ~spl6_20 | ~spl6_25 | ~spl6_40)),
% 1.36/0.58    inference(resolution,[],[f760,f120])).
% 1.36/0.58  fof(f760,plain,(
% 1.36/0.58    v1_funct_2(k2_funct_1(sK3),sK2,sK1) | (~spl6_15 | ~spl6_20 | ~spl6_25 | ~spl6_40)),
% 1.36/0.58    inference(backward_demodulation,[],[f388,f730])).
% 1.36/0.58  fof(f388,plain,(
% 1.36/0.58    v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) | (~spl6_15 | ~spl6_20 | ~spl6_25)),
% 1.36/0.58    inference(backward_demodulation,[],[f300,f357])).
% 1.36/0.58  fof(f300,plain,(
% 1.36/0.58    v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3)) | (~spl6_15 | ~spl6_20)),
% 1.36/0.58    inference(backward_demodulation,[],[f263,f297])).
% 1.36/0.58  fof(f263,plain,(
% 1.36/0.58    v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3))) | ~spl6_15),
% 1.36/0.58    inference(avatar_component_clause,[],[f261])).
% 1.36/0.58  fof(f261,plain,(
% 1.36/0.58    spl6_15 <=> v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3)))),
% 1.36/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.36/0.58  fof(f754,plain,(
% 1.36/0.58    spl6_41),
% 1.36/0.58    inference(avatar_contradiction_clause,[],[f752])).
% 1.36/0.58  fof(f752,plain,(
% 1.36/0.58    $false | spl6_41),
% 1.36/0.58    inference(resolution,[],[f734,f58])).
% 1.36/0.58  fof(f58,plain,(
% 1.36/0.58    v1_funct_2(sK3,sK1,sK2)),
% 1.36/0.58    inference(cnf_transformation,[],[f42])).
% 1.36/0.58  fof(f42,plain,(
% 1.36/0.58    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & sK2 = k2_relset_1(sK1,sK2,sK3) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 1.36/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f41])).
% 1.36/0.58  fof(f41,plain,(
% 1.36/0.58    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & sK2 = k2_relset_1(sK1,sK2,sK3) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 1.36/0.58    introduced(choice_axiom,[])).
% 1.36/0.58  fof(f22,plain,(
% 1.36/0.58    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.36/0.58    inference(flattening,[],[f21])).
% 1.36/0.58  fof(f21,plain,(
% 1.36/0.58    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.36/0.58    inference(ennf_transformation,[],[f20])).
% 1.36/0.58  fof(f20,negated_conjecture,(
% 1.36/0.58    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.36/0.58    inference(negated_conjecture,[],[f19])).
% 1.36/0.58  fof(f19,conjecture,(
% 1.36/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.36/0.58  fof(f734,plain,(
% 1.36/0.58    ~v1_funct_2(sK3,sK1,sK2) | spl6_41),
% 1.36/0.58    inference(avatar_component_clause,[],[f732])).
% 1.36/0.58  fof(f732,plain,(
% 1.36/0.58    spl6_41 <=> v1_funct_2(sK3,sK1,sK2)),
% 1.36/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 1.36/0.58  fof(f739,plain,(
% 1.36/0.58    spl6_40 | ~spl6_41 | spl6_42),
% 1.36/0.58    inference(avatar_split_clause,[],[f722,f736,f732,f728])).
% 1.36/0.58  fof(f722,plain,(
% 1.36/0.58    k1_xboole_0 = sK2 | ~v1_funct_2(sK3,sK1,sK2) | sK1 = k1_relat_1(sK3)),
% 1.36/0.58    inference(resolution,[],[f651,f59])).
% 1.36/0.58  fof(f59,plain,(
% 1.36/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.36/0.58    inference(cnf_transformation,[],[f42])).
% 1.36/0.58  fof(f651,plain,(
% 1.36/0.58    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_xboole_0 = X4 | ~v1_funct_2(X5,X3,X4) | k1_relat_1(X5) = X3) )),
% 1.36/0.58    inference(duplicate_literal_removal,[],[f648])).
% 1.36/0.58  fof(f648,plain,(
% 1.36/0.58    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | k1_xboole_0 = X4 | ~v1_funct_2(X5,X3,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 1.36/0.58    inference(superposition,[],[f476,f94])).
% 1.36/0.58  fof(f94,plain,(
% 1.36/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.36/0.58    inference(cnf_transformation,[],[f34])).
% 1.36/0.58  fof(f34,plain,(
% 1.36/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.58    inference(ennf_transformation,[],[f14])).
% 1.36/0.58  fof(f14,axiom,(
% 1.36/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.36/0.58  fof(f476,plain,(
% 1.36/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X1,X2,X0) = X1 | k1_xboole_0 = X2 | ~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.36/0.58    inference(resolution,[],[f96,f100])).
% 1.36/0.58  fof(f100,plain,(
% 1.36/0.58    ( ! [X2,X0,X1] : (sP0(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.36/0.58    inference(cnf_transformation,[],[f56])).
% 1.36/0.58  fof(f56,plain,(
% 1.36/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.58    inference(nnf_transformation,[],[f40])).
% 1.36/0.58  fof(f40,plain,(
% 1.36/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.58    inference(definition_folding,[],[f37,f39])).
% 1.36/0.58  fof(f39,plain,(
% 1.36/0.58    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.36/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.36/0.58  fof(f37,plain,(
% 1.36/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.58    inference(flattening,[],[f36])).
% 1.36/0.58  fof(f36,plain,(
% 1.36/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.58    inference(ennf_transformation,[],[f16])).
% 1.36/0.58  fof(f16,axiom,(
% 1.36/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.36/0.58  fof(f96,plain,(
% 1.36/0.58    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 1.36/0.58    inference(cnf_transformation,[],[f55])).
% 1.36/0.58  fof(f55,plain,(
% 1.36/0.58    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.36/0.58    inference(rectify,[],[f54])).
% 1.36/0.58  fof(f54,plain,(
% 1.36/0.58    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.36/0.58    inference(nnf_transformation,[],[f39])).
% 1.36/0.58  fof(f594,plain,(
% 1.36/0.58    ~spl6_38),
% 1.36/0.58    inference(avatar_contradiction_clause,[],[f589])).
% 1.36/0.58  fof(f589,plain,(
% 1.36/0.58    $false | ~spl6_38),
% 1.36/0.58    inference(resolution,[],[f581,f544])).
% 1.36/0.58  fof(f581,plain,(
% 1.36/0.58    ( ! [X1] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,X1)) ) | ~spl6_38),
% 1.36/0.58    inference(avatar_component_clause,[],[f580])).
% 1.36/0.58  fof(f580,plain,(
% 1.36/0.58    spl6_38 <=> ! [X1] : ~v1_funct_2(k1_xboole_0,k1_xboole_0,X1)),
% 1.36/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 1.36/0.58  fof(f588,plain,(
% 1.36/0.58    spl6_38 | spl6_39 | ~spl6_5),
% 1.36/0.58    inference(avatar_split_clause,[],[f587,f132,f583,f580])).
% 1.36/0.58  fof(f132,plain,(
% 1.36/0.58    spl6_5 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.36/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.36/0.58  fof(f587,plain,(
% 1.36/0.58    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.36/0.58    inference(forward_demodulation,[],[f577,f107])).
% 1.36/0.58  fof(f577,plain,(
% 1.36/0.58    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.36/0.58    inference(superposition,[],[f94,f574])).
% 1.36/0.58  fof(f574,plain,(
% 1.36/0.58    ( ! [X0] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.36/0.58    inference(resolution,[],[f427,f126])).
% 1.36/0.58  fof(f427,plain,(
% 1.36/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X0,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X0)) )),
% 1.36/0.58    inference(forward_demodulation,[],[f426,f107])).
% 1.36/0.58  fof(f426,plain,(
% 1.36/0.58    ( ! [X0,X1] : (~v1_funct_2(X0,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.36/0.58    inference(resolution,[],[f109,f100])).
% 1.36/0.58  fof(f109,plain,(
% 1.36/0.58    ( ! [X2,X1] : (~sP0(k1_xboole_0,X1,X2) | ~v1_funct_2(X1,k1_xboole_0,X2) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X1)) )),
% 1.36/0.58    inference(equality_resolution,[],[f97])).
% 1.36/0.58  fof(f97,plain,(
% 1.36/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 != X0 | ~sP0(X0,X1,X2)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f55])).
% 1.36/0.58  fof(f383,plain,(
% 1.36/0.58    spl6_24),
% 1.36/0.58    inference(avatar_contradiction_clause,[],[f381])).
% 1.36/0.58  fof(f381,plain,(
% 1.36/0.58    $false | spl6_24),
% 1.36/0.58    inference(resolution,[],[f353,f59])).
% 1.36/0.58  fof(f353,plain,(
% 1.36/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl6_24),
% 1.36/0.58    inference(avatar_component_clause,[],[f351])).
% 1.36/0.58  fof(f351,plain,(
% 1.36/0.58    spl6_24 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.36/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.36/0.58  fof(f359,plain,(
% 1.36/0.58    ~spl6_24 | spl6_25),
% 1.36/0.58    inference(avatar_split_clause,[],[f349,f355,f351])).
% 1.36/0.58  fof(f349,plain,(
% 1.36/0.58    sK2 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.36/0.58    inference(superposition,[],[f61,f95])).
% 1.36/0.58  fof(f95,plain,(
% 1.36/0.58    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.36/0.58    inference(cnf_transformation,[],[f35])).
% 1.36/0.58  fof(f35,plain,(
% 1.36/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.58    inference(ennf_transformation,[],[f15])).
% 1.36/0.58  fof(f15,axiom,(
% 1.36/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.36/0.58  fof(f61,plain,(
% 1.36/0.58    sK2 = k2_relset_1(sK1,sK2,sK3)),
% 1.36/0.58    inference(cnf_transformation,[],[f42])).
% 1.36/0.58  fof(f298,plain,(
% 1.36/0.58    ~spl6_6 | ~spl6_7 | spl6_20),
% 1.36/0.58    inference(avatar_split_clause,[],[f293,f295,f146,f142])).
% 1.36/0.58  fof(f146,plain,(
% 1.36/0.58    spl6_7 <=> v1_funct_1(sK3)),
% 1.36/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.36/0.58  fof(f293,plain,(
% 1.36/0.58    k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.36/0.58    inference(resolution,[],[f75,f60])).
% 1.36/0.58  fof(f60,plain,(
% 1.36/0.58    v2_funct_1(sK3)),
% 1.36/0.58    inference(cnf_transformation,[],[f42])).
% 1.36/0.58  fof(f75,plain,(
% 1.36/0.58    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f31])).
% 1.36/0.58  fof(f31,plain,(
% 1.36/0.58    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.58    inference(flattening,[],[f30])).
% 1.36/0.58  fof(f30,plain,(
% 1.36/0.58    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.58    inference(ennf_transformation,[],[f12])).
% 1.36/0.58  fof(f12,axiom,(
% 1.36/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.36/0.58  fof(f276,plain,(
% 1.36/0.58    ~spl6_6 | ~spl6_7 | spl6_13),
% 1.36/0.58    inference(avatar_split_clause,[],[f274,f252,f146,f142])).
% 1.36/0.58  fof(f274,plain,(
% 1.36/0.58    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl6_13),
% 1.36/0.58    inference(resolution,[],[f254,f72])).
% 1.36/0.58  fof(f72,plain,(
% 1.36/0.58    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f29])).
% 1.36/0.58  fof(f29,plain,(
% 1.36/0.58    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.58    inference(flattening,[],[f28])).
% 1.36/0.58  fof(f28,plain,(
% 1.36/0.58    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.58    inference(ennf_transformation,[],[f11])).
% 1.36/0.58  fof(f11,axiom,(
% 1.36/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.36/0.58  fof(f254,plain,(
% 1.36/0.58    ~v1_relat_1(k2_funct_1(sK3)) | spl6_13),
% 1.36/0.58    inference(avatar_component_clause,[],[f252])).
% 1.36/0.58  fof(f264,plain,(
% 1.36/0.58    ~spl6_13 | ~spl6_1 | spl6_15 | ~spl6_12),
% 1.36/0.58    inference(avatar_split_clause,[],[f249,f240,f261,f114,f252])).
% 1.36/0.58  fof(f249,plain,(
% 1.36/0.58    v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k2_relat_1(k2_funct_1(sK3))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~spl6_12),
% 1.36/0.58    inference(superposition,[],[f70,f242])).
% 1.36/0.58  fof(f70,plain,(
% 1.36/0.58    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f27])).
% 1.36/0.58  fof(f243,plain,(
% 1.36/0.58    ~spl6_6 | ~spl6_7 | spl6_12),
% 1.36/0.58    inference(avatar_split_clause,[],[f238,f240,f146,f142])).
% 1.36/0.58  fof(f238,plain,(
% 1.36/0.58    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.36/0.58    inference(resolution,[],[f74,f60])).
% 1.36/0.58  fof(f74,plain,(
% 1.36/0.58    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f31])).
% 1.36/0.58  fof(f164,plain,(
% 1.36/0.58    spl6_6),
% 1.36/0.58    inference(avatar_contradiction_clause,[],[f160])).
% 1.36/0.58  fof(f160,plain,(
% 1.36/0.58    $false | spl6_6),
% 1.36/0.58    inference(resolution,[],[f159,f59])).
% 1.36/0.58  fof(f159,plain,(
% 1.36/0.58    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_6),
% 1.36/0.58    inference(resolution,[],[f93,f144])).
% 1.36/0.58  fof(f144,plain,(
% 1.36/0.58    ~v1_relat_1(sK3) | spl6_6),
% 1.36/0.58    inference(avatar_component_clause,[],[f142])).
% 1.36/0.58  fof(f93,plain,(
% 1.36/0.58    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.36/0.58    inference(cnf_transformation,[],[f33])).
% 1.36/0.58  fof(f33,plain,(
% 1.36/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.58    inference(ennf_transformation,[],[f13])).
% 1.36/0.58  fof(f13,axiom,(
% 1.36/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.36/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.36/0.58  fof(f152,plain,(
% 1.36/0.58    spl6_7),
% 1.36/0.58    inference(avatar_contradiction_clause,[],[f150])).
% 1.36/0.58  fof(f150,plain,(
% 1.36/0.58    $false | spl6_7),
% 1.36/0.58    inference(resolution,[],[f148,f57])).
% 1.36/0.58  fof(f57,plain,(
% 1.36/0.58    v1_funct_1(sK3)),
% 1.36/0.58    inference(cnf_transformation,[],[f42])).
% 1.36/0.58  fof(f148,plain,(
% 1.36/0.58    ~v1_funct_1(sK3) | spl6_7),
% 1.36/0.58    inference(avatar_component_clause,[],[f146])).
% 1.36/0.58  fof(f149,plain,(
% 1.36/0.58    ~spl6_6 | ~spl6_7 | spl6_1),
% 1.36/0.58    inference(avatar_split_clause,[],[f140,f114,f146,f142])).
% 1.36/0.58  fof(f140,plain,(
% 1.36/0.58    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl6_1),
% 1.36/0.58    inference(resolution,[],[f73,f116])).
% 1.36/0.58  fof(f116,plain,(
% 1.36/0.58    ~v1_funct_1(k2_funct_1(sK3)) | spl6_1),
% 1.36/0.58    inference(avatar_component_clause,[],[f114])).
% 1.36/0.58  fof(f73,plain,(
% 1.36/0.58    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.58    inference(cnf_transformation,[],[f29])).
% 1.36/0.58  fof(f139,plain,(
% 1.36/0.58    spl6_5),
% 1.36/0.58    inference(avatar_contradiction_clause,[],[f138])).
% 1.36/0.58  fof(f138,plain,(
% 1.36/0.58    $false | spl6_5),
% 1.36/0.58    inference(resolution,[],[f134,f126])).
% 1.36/0.58  fof(f134,plain,(
% 1.36/0.58    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl6_5),
% 1.36/0.58    inference(avatar_component_clause,[],[f132])).
% 1.36/0.58  fof(f125,plain,(
% 1.36/0.58    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 1.36/0.58    inference(avatar_split_clause,[],[f62,f122,f118,f114])).
% 1.36/0.58  fof(f62,plain,(
% 1.36/0.58    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 1.36/0.58    inference(cnf_transformation,[],[f42])).
% 1.36/0.58  % SZS output end Proof for theBenchmark
% 1.36/0.58  % (20245)------------------------------
% 1.36/0.58  % (20245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.58  % (20245)Termination reason: Refutation
% 1.36/0.58  
% 1.36/0.58  % (20245)Memory used [KB]: 6780
% 1.36/0.58  % (20245)Time elapsed: 0.163 s
% 1.36/0.58  % (20245)------------------------------
% 1.36/0.58  % (20245)------------------------------
% 1.36/0.58  % (20232)Success in time 0.225 s
%------------------------------------------------------------------------------
