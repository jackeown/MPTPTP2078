%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t58_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:11 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   46 (  81 expanded)
%              Number of leaves         :    9 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  148 ( 270 expanded)
%              Number of equality atoms :   92 ( 190 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f42,f56,f65,f72,f80,f85,f89])).

fof(f89,plain,
    ( spl2_1
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f87,f34])).

fof(f34,plain,
    ( sK0 != sK1
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl2_1
  <=> sK0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f87,plain,
    ( sK0 = sK1
    | ~ spl2_6 ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,
    ( ! [X2,X0,X3,X1] :
        ( k4_zfmisc_1(sK0,sK0,sK0,sK0) != k4_zfmisc_1(X0,X1,X2,X3)
        | sK1 = X0 )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl2_6
  <=> ! [X1,X3,X0,X2] :
        ( k4_zfmisc_1(sK0,sK0,sK0,sK0) != k4_zfmisc_1(X0,X1,X2,X3)
        | sK1 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f85,plain,
    ( spl2_6
    | ~ spl2_2
    | spl2_5 ),
    inference(avatar_split_clause,[],[f84,f48,f40,f54])).

fof(f40,plain,
    ( spl2_2
  <=> k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f48,plain,
    ( spl2_5
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f84,plain,
    ( ! [X6,X4,X7,X5] :
        ( k4_zfmisc_1(sK0,sK0,sK0,sK0) != k4_zfmisc_1(X4,X5,X6,X7)
        | sK1 = X4 )
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f83,f49])).

fof(f49,plain,
    ( k1_xboole_0 != sK1
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f83,plain,
    ( ! [X6,X4,X7,X5] :
        ( k4_zfmisc_1(sK0,sK0,sK0,sK0) != k4_zfmisc_1(X4,X5,X6,X7)
        | k1_xboole_0 = sK1
        | sK1 = X4 )
    | ~ spl2_2 ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,
    ( ! [X6,X4,X7,X5] :
        ( k4_zfmisc_1(sK0,sK0,sK0,sK0) != k4_zfmisc_1(X4,X5,X6,X7)
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK1
        | sK1 = X4 )
    | ~ spl2_2 ),
    inference(superposition,[],[f24,f41])).

fof(f41,plain,
    ( k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t58_mcart_1.p',t56_mcart_1)).

fof(f80,plain,
    ( ~ spl2_8
    | spl2_11 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f78,f71])).

fof(f71,plain,
    ( k1_xboole_0 != sK0
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl2_11
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f78,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,
    ( ! [X6,X4,X7,X5] :
        ( k4_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k4_zfmisc_1(X4,X5,X6,X7)
        | sK0 = X4 )
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f75,f71])).

fof(f75,plain,
    ( ! [X6,X4,X7,X5] :
        ( k4_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k4_zfmisc_1(X4,X5,X6,X7)
        | k1_xboole_0 = sK0
        | sK0 = X4 )
    | ~ spl2_8 ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,
    ( ! [X6,X4,X7,X5] :
        ( k4_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k4_zfmisc_1(X4,X5,X6,X7)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = sK0
        | k1_xboole_0 = sK0
        | k1_xboole_0 = sK0
        | sK0 = X4 )
    | ~ spl2_8 ),
    inference(superposition,[],[f24,f64])).

fof(f64,plain,
    ( k4_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k4_zfmisc_1(sK0,sK0,sK0,sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl2_8
  <=> k4_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k4_zfmisc_1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f72,plain,
    ( ~ spl2_11
    | spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f58,f51,f33,f70])).

fof(f51,plain,
    ( spl2_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f58,plain,
    ( k1_xboole_0 != sK0
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f52,f34])).

fof(f52,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f65,plain,
    ( spl2_8
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f57,f51,f40,f63])).

fof(f57,plain,
    ( k4_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k4_zfmisc_1(sK0,sK0,sK0,sK0)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f52,f41])).

fof(f56,plain,
    ( spl2_4
    | spl2_6
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f46,f40,f54,f51])).

fof(f46,plain,
    ( ! [X2,X0,X3,X1] :
        ( k4_zfmisc_1(sK0,sK0,sK0,sK0) != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = sK1
        | sK1 = X0 )
    | ~ spl2_2 ),
    inference(duplicate_literal_removal,[],[f43])).

fof(f43,plain,
    ( ! [X2,X0,X3,X1] :
        ( k4_zfmisc_1(sK0,sK0,sK0,sK0) != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK1
        | sK1 = X0 )
    | ~ spl2_2 ),
    inference(superposition,[],[f24,f41])).

fof(f42,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f21,f40])).

fof(f21,plain,(
    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t58_mcart_1.p',t58_mcart_1)).

fof(f35,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f22,f33])).

fof(f22,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
