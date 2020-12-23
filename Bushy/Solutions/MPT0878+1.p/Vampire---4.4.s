%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t38_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:07 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  81 expanded)
%              Number of leaves         :    9 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  138 ( 246 expanded)
%              Number of equality atoms :   82 ( 166 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f41,f55,f64,f71,f79,f84,f88])).

fof(f88,plain,
    ( spl2_1
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f87])).

fof(f87,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f86,f33])).

fof(f33,plain,
    ( sK0 != sK1
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl2_1
  <=> sK0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f86,plain,
    ( sK0 = sK1
    | ~ spl2_6 ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,
    ( ! [X2,X0,X1] :
        ( k3_zfmisc_1(sK0,sK0,sK0) != k3_zfmisc_1(X0,X1,X2)
        | sK1 = X0 )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl2_6
  <=> ! [X1,X0,X2] :
        ( k3_zfmisc_1(sK0,sK0,sK0) != k3_zfmisc_1(X0,X1,X2)
        | sK1 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f84,plain,
    ( spl2_6
    | ~ spl2_2
    | spl2_5 ),
    inference(avatar_split_clause,[],[f83,f47,f39,f53])).

fof(f39,plain,
    ( spl2_2
  <=> k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f47,plain,
    ( spl2_5
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f83,plain,
    ( ! [X4,X5,X3] :
        ( k3_zfmisc_1(sK0,sK0,sK0) != k3_zfmisc_1(X3,X4,X5)
        | sK1 = X3 )
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f82,f48])).

fof(f48,plain,
    ( k1_xboole_0 != sK1
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f82,plain,
    ( ! [X4,X5,X3] :
        ( k3_zfmisc_1(sK0,sK0,sK0) != k3_zfmisc_1(X3,X4,X5)
        | k1_xboole_0 = sK1
        | sK1 = X3 )
    | ~ spl2_2 ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,
    ( ! [X4,X5,X3] :
        ( k3_zfmisc_1(sK0,sK0,sK0) != k3_zfmisc_1(X3,X4,X5)
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK1
        | sK1 = X3 )
    | ~ spl2_2 ),
    inference(superposition,[],[f24,f40])).

fof(f40,plain,
    ( k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t38_mcart_1.p',t36_mcart_1)).

fof(f79,plain,
    ( ~ spl2_8
    | spl2_11 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f77,f70])).

fof(f70,plain,
    ( k1_xboole_0 != sK0
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl2_11
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f77,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,
    ( ! [X4,X5,X3] :
        ( k3_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k3_zfmisc_1(X3,X4,X5)
        | sK0 = X3 )
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f74,f70])).

fof(f74,plain,
    ( ! [X4,X5,X3] :
        ( k3_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k3_zfmisc_1(X3,X4,X5)
        | k1_xboole_0 = sK0
        | sK0 = X3 )
    | ~ spl2_8 ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,
    ( ! [X4,X5,X3] :
        ( k3_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k3_zfmisc_1(X3,X4,X5)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = sK0
        | k1_xboole_0 = sK0
        | sK0 = X3 )
    | ~ spl2_8 ),
    inference(superposition,[],[f24,f63])).

fof(f63,plain,
    ( k3_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k3_zfmisc_1(sK0,sK0,sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl2_8
  <=> k3_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k3_zfmisc_1(sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f71,plain,
    ( ~ spl2_11
    | spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f57,f50,f32,f69])).

fof(f50,plain,
    ( spl2_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f57,plain,
    ( k1_xboole_0 != sK0
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f51,f33])).

fof(f51,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f64,plain,
    ( spl2_8
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f56,f50,f39,f62])).

fof(f56,plain,
    ( k3_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k3_zfmisc_1(sK0,sK0,sK0)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f51,f40])).

fof(f55,plain,
    ( spl2_4
    | spl2_6
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f45,f39,f53,f50])).

fof(f45,plain,
    ( ! [X2,X0,X1] :
        ( k3_zfmisc_1(sK0,sK0,sK0) != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = sK1
        | sK1 = X0 )
    | ~ spl2_2 ),
    inference(duplicate_literal_removal,[],[f42])).

fof(f42,plain,
    ( ! [X2,X0,X1] :
        ( k3_zfmisc_1(sK0,sK0,sK0) != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK1
        | sK1 = X0 )
    | ~ spl2_2 ),
    inference(superposition,[],[f24,f40])).

fof(f41,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f21,f39])).

fof(f21,plain,(
    k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t38_mcart_1.p',t38_mcart_1)).

fof(f34,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f22,f32])).

fof(f22,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
