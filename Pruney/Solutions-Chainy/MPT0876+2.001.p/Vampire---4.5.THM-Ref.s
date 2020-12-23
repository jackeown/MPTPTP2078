%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:51 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 876 expanded)
%              Number of leaves         :   33 ( 266 expanded)
%              Depth                    :   17
%              Number of atoms          :  623 (3464 expanded)
%              Number of equality atoms :  187 (1616 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1955,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f102,f164,f820,f923,f926,f960,f1242,f1302,f1519,f1701,f1706,f1797,f1832,f1886,f1946,f1952,f1954])).

fof(f1954,plain,
    ( spl13_3
    | spl13_6
    | spl13_8
    | spl13_15 ),
    inference(avatar_contradiction_clause,[],[f1953])).

fof(f1953,plain,
    ( $false
    | spl13_3
    | spl13_6
    | spl13_8
    | spl13_15 ),
    inference(subsumption_resolution,[],[f91,f1621])).

fof(f1621,plain,
    ( sK2 = sK5
    | spl13_6
    | spl13_8
    | spl13_15 ),
    inference(subsumption_resolution,[],[f1620,f771])).

fof(f771,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl13_15 ),
    inference(avatar_component_clause,[],[f770])).

fof(f770,plain,
    ( spl13_15
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).

fof(f1620,plain,
    ( sK2 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | spl13_6
    | spl13_8 ),
    inference(subsumption_resolution,[],[f1618,f44])).

fof(f44,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( sK2 != sK5
      | sK1 != sK4
      | sK0 != sK3 )
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f15,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( X2 != X5
          | X1 != X4
          | X0 != X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) )
   => ( ( sK2 != sK5
        | sK1 != sK4
        | sK0 != sK3 )
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
       => ( ( X2 = X5
            & X1 = X4
            & X0 = X3 )
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).

fof(f1618,plain,
    ( sK2 = sK5
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | spl13_6
    | spl13_8 ),
    inference(superposition,[],[f1617,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(f1617,plain,
    ( sK5 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | spl13_6
    | spl13_8 ),
    inference(subsumption_resolution,[],[f1616,f158])).

fof(f158,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK3,sK4)
    | spl13_6 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl13_6
  <=> k1_xboole_0 = k2_zfmisc_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f1616,plain,
    ( sK5 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | spl13_8 ),
    inference(subsumption_resolution,[],[f1615,f275])).

fof(f275,plain,
    ( k1_xboole_0 != sK5
    | spl13_8 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl13_8
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f1615,plain,
    ( sK5 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) ),
    inference(superposition,[],[f60,f72])).

fof(f72,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) ),
    inference(definition_unfolding,[],[f41,f61,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f41,plain,(
    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f91,plain,
    ( sK2 != sK5
    | spl13_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl13_3
  <=> sK2 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f1952,plain,
    ( spl13_2
    | ~ spl13_25 ),
    inference(avatar_contradiction_clause,[],[f1951])).

fof(f1951,plain,
    ( $false
    | spl13_2
    | ~ spl13_25 ),
    inference(subsumption_resolution,[],[f87,f1921])).

fof(f1921,plain,
    ( sK1 = sK4
    | ~ spl13_25 ),
    inference(subsumption_resolution,[],[f1920,f42])).

fof(f42,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f24])).

fof(f1920,plain,
    ( sK1 = sK4
    | k1_xboole_0 = sK0
    | ~ spl13_25 ),
    inference(subsumption_resolution,[],[f1918,f43])).

fof(f43,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f1918,plain,
    ( sK1 = sK4
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl13_25 ),
    inference(superposition,[],[f1700,f60])).

fof(f1700,plain,
    ( sK4 = k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl13_25 ),
    inference(avatar_component_clause,[],[f1698])).

fof(f1698,plain,
    ( spl13_25
  <=> sK4 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_25])])).

fof(f87,plain,
    ( sK1 != sK4
    | spl13_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl13_2
  <=> sK1 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f1946,plain,
    ( spl13_1
    | ~ spl13_26 ),
    inference(avatar_contradiction_clause,[],[f1945])).

fof(f1945,plain,
    ( $false
    | spl13_1
    | ~ spl13_26 ),
    inference(subsumption_resolution,[],[f1944,f42])).

fof(f1944,plain,
    ( k1_xboole_0 = sK0
    | spl13_1
    | ~ spl13_26 ),
    inference(subsumption_resolution,[],[f1943,f43])).

fof(f1943,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl13_1
    | ~ spl13_26 ),
    inference(subsumption_resolution,[],[f1938,f83])).

fof(f83,plain,
    ( sK0 != sK3
    | spl13_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl13_1
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f1938,plain,
    ( sK0 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl13_26 ),
    inference(superposition,[],[f59,f1705])).

fof(f1705,plain,
    ( sK3 = k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl13_26 ),
    inference(avatar_component_clause,[],[f1703])).

fof(f1703,plain,
    ( spl13_26
  <=> sK3 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1886,plain,
    ( spl13_6
    | spl13_24
    | spl13_6
    | spl13_8
    | spl13_15 ),
    inference(avatar_split_clause,[],[f1885,f770,f274,f157,f1424,f157])).

fof(f1424,plain,
    ( spl13_24
  <=> k2_zfmisc_1(sK3,sK4) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_24])])).

fof(f1885,plain,
    ( k2_zfmisc_1(sK3,sK4) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | spl13_6
    | spl13_8
    | spl13_15 ),
    inference(subsumption_resolution,[],[f1847,f44])).

fof(f1847,plain,
    ( k2_zfmisc_1(sK3,sK4) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | spl13_6
    | spl13_8
    | spl13_15 ),
    inference(superposition,[],[f59,f1624])).

fof(f1624,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK2)
    | spl13_6
    | spl13_8
    | spl13_15 ),
    inference(backward_demodulation,[],[f72,f1621])).

fof(f1832,plain,
    ( spl13_7
    | ~ spl13_13 ),
    inference(avatar_contradiction_clause,[],[f1831])).

fof(f1831,plain,
    ( $false
    | spl13_7
    | ~ spl13_13 ),
    inference(subsumption_resolution,[],[f1824,f1116])).

fof(f1116,plain,(
    ! [X7] : ~ r2_hidden(X7,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1114,f1065])).

fof(f1065,plain,(
    ! [X5] : k1_xboole_0 = k2_zfmisc_1(X5,k1_xboole_0) ),
    inference(resolution,[],[f683,f46])).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f683,plain,(
    ! [X6,X5] :
      ( ~ v1_xboole_0(X6)
      | k1_xboole_0 = k2_zfmisc_1(X5,X6) ) ),
    inference(resolution,[],[f400,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f400,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f399,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(f399,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f57,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f26,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f1114,plain,(
    ! [X8,X7] : ~ r2_hidden(X7,k2_zfmisc_1(X8,k1_xboole_0)) ),
    inference(resolution,[],[f1111,f46])).

fof(f1111,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(resolution,[],[f78,f47])).

fof(f78,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK12(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK12(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK8(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( ( sK8(X0,X1,X2) = k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2))
              & r2_hidden(sK10(X0,X1,X2),X1)
              & r2_hidden(sK9(X0,X1,X2),X0) )
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK11(X0,X1,X8),sK12(X0,X1,X8)) = X8
                & r2_hidden(sK12(X0,X1,X8),X1)
                & r2_hidden(sK11(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11,sK12])],[f36,f39,f38,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK8(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK8(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK8(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK8(X0,X1,X2) = k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2))
        & r2_hidden(sK10(X0,X1,X2),X1)
        & r2_hidden(sK9(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK11(X0,X1,X8),sK12(X0,X1,X8)) = X8
        & r2_hidden(sK12(X0,X1,X8),X1)
        & r2_hidden(sK11(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f1824,plain,
    ( r2_hidden(sK6(k1_xboole_0),k1_xboole_0)
    | spl13_7
    | ~ spl13_13 ),
    inference(backward_demodulation,[],[f413,f747])).

fof(f747,plain,
    ( k1_xboole_0 = sK4
    | ~ spl13_13 ),
    inference(avatar_component_clause,[],[f745])).

fof(f745,plain,
    ( spl13_13
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).

fof(f413,plain,
    ( r2_hidden(sK6(sK4),sK4)
    | spl13_7 ),
    inference(resolution,[],[f404,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK6(X0),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f404,plain,
    ( ~ v1_xboole_0(sK4)
    | spl13_7 ),
    inference(resolution,[],[f402,f49])).

fof(f402,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK3,sK4))
    | spl13_7 ),
    inference(resolution,[],[f399,f163])).

fof(f163,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | spl13_7 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl13_7
  <=> r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f1797,plain,
    ( ~ spl13_11
    | spl13_15
    | spl13_19
    | ~ spl13_24 ),
    inference(avatar_contradiction_clause,[],[f1796])).

fof(f1796,plain,
    ( $false
    | ~ spl13_11
    | spl13_15
    | spl13_19
    | ~ spl13_24 ),
    inference(subsumption_resolution,[],[f1785,f1197])).

fof(f1197,plain,(
    ! [X4,X3] : ~ r2_hidden(X3,k2_zfmisc_1(k1_xboole_0,X4)) ),
    inference(resolution,[],[f79,f1116])).

fof(f79,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK11(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK11(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1785,plain,
    ( r2_hidden(sK6(k2_zfmisc_1(k1_xboole_0,sK4)),k2_zfmisc_1(k1_xboole_0,sK4))
    | ~ spl13_11
    | spl13_15
    | spl13_19
    | ~ spl13_24 ),
    inference(backward_demodulation,[],[f1305,f1730])).

fof(f1730,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,sK4)
    | ~ spl13_11
    | spl13_15
    | ~ spl13_24 ),
    inference(backward_demodulation,[],[f1681,f738])).

fof(f738,plain,
    ( k1_xboole_0 = sK3
    | ~ spl13_11 ),
    inference(avatar_component_clause,[],[f736])).

fof(f736,plain,
    ( spl13_11
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_11])])).

fof(f1681,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4)
    | spl13_15
    | ~ spl13_24 ),
    inference(subsumption_resolution,[],[f1680,f771])).

fof(f1680,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl13_24 ),
    inference(subsumption_resolution,[],[f1678,f44])).

fof(f1678,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl13_24 ),
    inference(superposition,[],[f1426,f59])).

fof(f1426,plain,
    ( k2_zfmisc_1(sK3,sK4) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl13_24 ),
    inference(avatar_component_clause,[],[f1424])).

fof(f1305,plain,
    ( r2_hidden(sK6(k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | spl13_19 ),
    inference(resolution,[],[f818,f48])).

fof(f818,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl13_19 ),
    inference(avatar_component_clause,[],[f817])).

fof(f817,plain,
    ( spl13_19
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_19])])).

fof(f1706,plain,
    ( spl13_11
    | spl13_13
    | spl13_26
    | spl13_15
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f1692,f1424,f770,f1703,f745,f736])).

fof(f1692,plain,
    ( sK3 = k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | spl13_15
    | ~ spl13_24 ),
    inference(superposition,[],[f59,f1681])).

fof(f1701,plain,
    ( spl13_11
    | spl13_13
    | spl13_25
    | spl13_15
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f1691,f1424,f770,f1698,f745,f736])).

fof(f1691,plain,
    ( sK4 = k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | spl13_15
    | ~ spl13_24 ),
    inference(superposition,[],[f60,f1681])).

fof(f1519,plain,
    ( spl13_4
    | spl13_7
    | ~ spl13_8 ),
    inference(avatar_contradiction_clause,[],[f1518])).

fof(f1518,plain,
    ( $false
    | spl13_4
    | spl13_7
    | ~ spl13_8 ),
    inference(subsumption_resolution,[],[f1517,f46])).

fof(f1517,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl13_4
    | spl13_7
    | ~ spl13_8 ),
    inference(forward_demodulation,[],[f1447,f1065])).

fof(f1447,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | spl13_4
    | spl13_7
    | ~ spl13_8 ),
    inference(backward_demodulation,[],[f1400,f276])).

fof(f276,plain,
    ( k1_xboole_0 = sK5
    | ~ spl13_8 ),
    inference(avatar_component_clause,[],[f274])).

fof(f1400,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK5,sK5))
    | spl13_4
    | spl13_7 ),
    inference(resolution,[],[f410,f49])).

fof(f410,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK4,k2_zfmisc_1(sK5,sK5)))
    | spl13_4
    | spl13_7 ),
    inference(resolution,[],[f404,f110])).

fof(f110,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ v1_xboole_0(k2_zfmisc_1(X0,k2_zfmisc_1(sK5,sK5))) )
    | spl13_4 ),
    inference(resolution,[],[f107,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_subset_1)).

fof(f107,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK5,sK5))
    | spl13_4 ),
    inference(resolution,[],[f105,f97])).

fof(f97,plain,
    ( ~ v1_xboole_0(sK5)
    | spl13_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl13_4
  <=> v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f105,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ v1_xboole_0(k2_zfmisc_1(X0,sK5)) )
    | spl13_4 ),
    inference(resolution,[],[f50,f97])).

fof(f1302,plain,
    ( spl13_15
    | ~ spl13_19 ),
    inference(avatar_contradiction_clause,[],[f1301])).

fof(f1301,plain,
    ( $false
    | spl13_15
    | ~ spl13_19 ),
    inference(subsumption_resolution,[],[f1293,f771])).

fof(f1293,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl13_19 ),
    inference(resolution,[],[f819,f400])).

fof(f819,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl13_19 ),
    inference(avatar_component_clause,[],[f817])).

fof(f1242,plain,(
    spl13_18 ),
    inference(avatar_contradiction_clause,[],[f1199])).

fof(f1199,plain,
    ( $false
    | spl13_18 ),
    inference(resolution,[],[f1197,f932])).

fof(f932,plain,
    ( r2_hidden(sK6(k2_zfmisc_1(k1_xboole_0,sK5)),k2_zfmisc_1(k1_xboole_0,sK5))
    | spl13_18 ),
    inference(resolution,[],[f784,f48])).

fof(f784,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK5))
    | spl13_18 ),
    inference(avatar_component_clause,[],[f783])).

fof(f783,plain,
    ( spl13_18
  <=> v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f960,plain,(
    ~ spl13_15 ),
    inference(avatar_contradiction_clause,[],[f959])).

fof(f959,plain,
    ( $false
    | ~ spl13_15 ),
    inference(subsumption_resolution,[],[f958,f942])).

fof(f942,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl13_15 ),
    inference(resolution,[],[f938,f399])).

fof(f938,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | ~ spl13_15 ),
    inference(subsumption_resolution,[],[f935,f42])).

fof(f935,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | ~ spl13_15 ),
    inference(superposition,[],[f51,f772])).

fof(f772,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl13_15 ),
    inference(avatar_component_clause,[],[f770])).

fof(f958,plain,
    ( v1_xboole_0(sK0)
    | ~ spl13_15 ),
    inference(subsumption_resolution,[],[f957,f46])).

fof(f957,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK0)
    | ~ spl13_15 ),
    inference(superposition,[],[f940,f772])).

fof(f940,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k2_zfmisc_1(X0,sK1))
        | v1_xboole_0(X0) )
    | ~ spl13_15 ),
    inference(resolution,[],[f939,f50])).

fof(f939,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl13_15 ),
    inference(resolution,[],[f937,f399])).

fof(f937,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ spl13_15 ),
    inference(subsumption_resolution,[],[f934,f43])).

fof(f934,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1
    | ~ spl13_15 ),
    inference(superposition,[],[f52,f772])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f926,plain,(
    ~ spl13_17 ),
    inference(avatar_contradiction_clause,[],[f925])).

fof(f925,plain,
    ( $false
    | ~ spl13_17 ),
    inference(subsumption_resolution,[],[f924,f44])).

fof(f924,plain,
    ( k1_xboole_0 = sK2
    | ~ spl13_17 ),
    inference(resolution,[],[f780,f400])).

fof(f780,plain,
    ( v1_xboole_0(sK2)
    | ~ spl13_17 ),
    inference(avatar_component_clause,[],[f779])).

fof(f779,plain,
    ( spl13_17
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).

fof(f923,plain,
    ( ~ spl13_5
    | spl13_17 ),
    inference(avatar_contradiction_clause,[],[f922])).

fof(f922,plain,
    ( $false
    | ~ spl13_5
    | spl13_17 ),
    inference(subsumption_resolution,[],[f921,f882])).

fof(f882,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl13_5
    | spl13_17 ),
    inference(resolution,[],[f878,f399])).

fof(f878,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | ~ spl13_5
    | spl13_17 ),
    inference(subsumption_resolution,[],[f875,f42])).

fof(f875,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | ~ spl13_5
    | spl13_17 ),
    inference(superposition,[],[f51,f864])).

fof(f864,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl13_5
    | spl13_17 ),
    inference(resolution,[],[f861,f400])).

fof(f861,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl13_5
    | spl13_17 ),
    inference(resolution,[],[f101,f789])).

fof(f789,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k2_zfmisc_1(X0,sK2))
        | v1_xboole_0(X0) )
    | spl13_17 ),
    inference(resolution,[],[f781,f50])).

fof(f781,plain,
    ( ~ v1_xboole_0(sK2)
    | spl13_17 ),
    inference(avatar_component_clause,[],[f779])).

fof(f101,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl13_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl13_5
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f921,plain,
    ( v1_xboole_0(sK0)
    | ~ spl13_5
    | spl13_17 ),
    inference(subsumption_resolution,[],[f920,f46])).

fof(f920,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK0)
    | ~ spl13_5
    | spl13_17 ),
    inference(superposition,[],[f880,f864])).

fof(f880,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k2_zfmisc_1(X0,sK1))
        | v1_xboole_0(X0) )
    | ~ spl13_5
    | spl13_17 ),
    inference(resolution,[],[f879,f50])).

fof(f879,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl13_5
    | spl13_17 ),
    inference(resolution,[],[f877,f399])).

fof(f877,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ spl13_5
    | spl13_17 ),
    inference(subsumption_resolution,[],[f874,f43])).

fof(f874,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1
    | ~ spl13_5
    | spl13_17 ),
    inference(superposition,[],[f52,f864])).

fof(f820,plain,
    ( spl13_19
    | ~ spl13_18
    | ~ spl13_6
    | spl13_17 ),
    inference(avatar_split_clause,[],[f815,f779,f157,f783,f817])).

fof(f815,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK5))
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl13_6
    | spl13_17 ),
    inference(superposition,[],[f789,f714])).

fof(f714,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k1_xboole_0,sK5)
    | ~ spl13_6 ),
    inference(backward_demodulation,[],[f72,f159])).

fof(f159,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f157])).

fof(f164,plain,
    ( spl13_6
    | ~ spl13_7 ),
    inference(avatar_split_clause,[],[f155,f161,f157])).

fof(f155,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) ),
    inference(superposition,[],[f51,f72])).

fof(f102,plain,
    ( ~ spl13_4
    | spl13_5 ),
    inference(avatar_split_clause,[],[f93,f99,f95])).

fof(f93,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ v1_xboole_0(sK5) ),
    inference(superposition,[],[f49,f72])).

fof(f92,plain,
    ( ~ spl13_1
    | ~ spl13_2
    | ~ spl13_3 ),
    inference(avatar_split_clause,[],[f45,f89,f85,f81])).

fof(f45,plain,
    ( sK2 != sK5
    | sK1 != sK4
    | sK0 != sK3 ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:06:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (10430)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (10425)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (10446)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (10433)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (10437)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (10418)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (10421)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (10439)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (10431)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (10419)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (10417)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (10417)Refutation not found, incomplete strategy% (10417)------------------------------
% 0.21/0.53  % (10417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10417)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (10417)Memory used [KB]: 1663
% 0.21/0.53  % (10417)Time elapsed: 0.115 s
% 0.21/0.53  % (10417)------------------------------
% 0.21/0.53  % (10417)------------------------------
% 0.21/0.53  % (10444)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (10424)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (10438)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (10423)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (10434)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (10445)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (10435)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (10437)Refutation not found, incomplete strategy% (10437)------------------------------
% 0.21/0.54  % (10437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10422)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (10437)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10437)Memory used [KB]: 10746
% 0.21/0.54  % (10437)Time elapsed: 0.123 s
% 0.21/0.54  % (10437)------------------------------
% 0.21/0.54  % (10437)------------------------------
% 0.21/0.54  % (10441)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (10443)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (10428)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (10420)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (10436)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (10426)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (10440)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (10440)Refutation not found, incomplete strategy% (10440)------------------------------
% 0.21/0.55  % (10440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10440)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10440)Memory used [KB]: 1663
% 0.21/0.55  % (10440)Time elapsed: 0.137 s
% 0.21/0.55  % (10440)------------------------------
% 0.21/0.55  % (10440)------------------------------
% 0.21/0.55  % (10426)Refutation not found, incomplete strategy% (10426)------------------------------
% 0.21/0.55  % (10426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10426)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10426)Memory used [KB]: 10618
% 0.21/0.55  % (10426)Time elapsed: 0.139 s
% 0.21/0.55  % (10426)------------------------------
% 0.21/0.55  % (10426)------------------------------
% 0.21/0.56  % (10427)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (10429)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (10427)Refutation not found, incomplete strategy% (10427)------------------------------
% 0.21/0.56  % (10427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (10427)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (10427)Memory used [KB]: 10618
% 0.21/0.56  % (10427)Time elapsed: 0.148 s
% 0.21/0.56  % (10427)------------------------------
% 0.21/0.56  % (10427)------------------------------
% 0.21/0.56  % (10432)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (10434)Refutation not found, incomplete strategy% (10434)------------------------------
% 0.21/0.56  % (10434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (10434)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (10434)Memory used [KB]: 10618
% 0.21/0.56  % (10434)Time elapsed: 0.148 s
% 0.21/0.56  % (10434)------------------------------
% 0.21/0.56  % (10434)------------------------------
% 1.54/0.57  % (10442)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 2.13/0.66  % (10420)Refutation found. Thanks to Tanya!
% 2.13/0.66  % SZS status Theorem for theBenchmark
% 2.13/0.66  % SZS output start Proof for theBenchmark
% 2.13/0.66  fof(f1955,plain,(
% 2.13/0.66    $false),
% 2.13/0.66    inference(avatar_sat_refutation,[],[f92,f102,f164,f820,f923,f926,f960,f1242,f1302,f1519,f1701,f1706,f1797,f1832,f1886,f1946,f1952,f1954])).
% 2.13/0.66  fof(f1954,plain,(
% 2.13/0.66    spl13_3 | spl13_6 | spl13_8 | spl13_15),
% 2.13/0.66    inference(avatar_contradiction_clause,[],[f1953])).
% 2.13/0.66  fof(f1953,plain,(
% 2.13/0.66    $false | (spl13_3 | spl13_6 | spl13_8 | spl13_15)),
% 2.13/0.66    inference(subsumption_resolution,[],[f91,f1621])).
% 2.13/0.66  fof(f1621,plain,(
% 2.13/0.66    sK2 = sK5 | (spl13_6 | spl13_8 | spl13_15)),
% 2.13/0.66    inference(subsumption_resolution,[],[f1620,f771])).
% 2.13/0.66  fof(f771,plain,(
% 2.13/0.66    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | spl13_15),
% 2.13/0.66    inference(avatar_component_clause,[],[f770])).
% 2.13/0.66  fof(f770,plain,(
% 2.13/0.66    spl13_15 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).
% 2.13/0.66  fof(f1620,plain,(
% 2.13/0.66    sK2 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (spl13_6 | spl13_8)),
% 2.13/0.66    inference(subsumption_resolution,[],[f1618,f44])).
% 2.13/0.66  fof(f44,plain,(
% 2.13/0.66    k1_xboole_0 != sK2),
% 2.13/0.66    inference(cnf_transformation,[],[f24])).
% 2.13/0.66  fof(f24,plain,(
% 2.13/0.66    (sK2 != sK5 | sK1 != sK4 | sK0 != sK3) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5)),
% 2.13/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f15,f23])).
% 2.13/0.66  fof(f23,plain,(
% 2.13/0.66    ? [X0,X1,X2,X3,X4,X5] : ((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)) => ((sK2 != sK5 | sK1 != sK4 | sK0 != sK3) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5))),
% 2.13/0.66    introduced(choice_axiom,[])).
% 2.13/0.66  fof(f15,plain,(
% 2.13/0.66    ? [X0,X1,X2,X3,X4,X5] : ((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5))),
% 2.13/0.66    inference(flattening,[],[f14])).
% 2.13/0.66  fof(f14,plain,(
% 2.13/0.66    ? [X0,X1,X2,X3,X4,X5] : (((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5))),
% 2.13/0.66    inference(ennf_transformation,[],[f13])).
% 2.13/0.66  fof(f13,negated_conjecture,(
% 2.13/0.66    ~! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.13/0.66    inference(negated_conjecture,[],[f12])).
% 2.13/0.66  fof(f12,conjecture,(
% 2.13/0.66    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.13/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).
% 2.13/0.66  fof(f1618,plain,(
% 2.13/0.66    sK2 = sK5 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (spl13_6 | spl13_8)),
% 2.13/0.66    inference(superposition,[],[f1617,f60])).
% 2.13/0.66  fof(f60,plain,(
% 2.13/0.66    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.13/0.66    inference(cnf_transformation,[],[f21])).
% 2.13/0.66  fof(f21,plain,(
% 2.13/0.66    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.13/0.66    inference(ennf_transformation,[],[f10])).
% 2.13/0.66  fof(f10,axiom,(
% 2.13/0.66    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.13/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).
% 2.13/0.66  fof(f1617,plain,(
% 2.13/0.66    sK5 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | (spl13_6 | spl13_8)),
% 2.13/0.66    inference(subsumption_resolution,[],[f1616,f158])).
% 2.13/0.66  fof(f158,plain,(
% 2.13/0.66    k1_xboole_0 != k2_zfmisc_1(sK3,sK4) | spl13_6),
% 2.13/0.66    inference(avatar_component_clause,[],[f157])).
% 2.13/0.66  fof(f157,plain,(
% 2.13/0.66    spl13_6 <=> k1_xboole_0 = k2_zfmisc_1(sK3,sK4)),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).
% 2.13/0.66  fof(f1616,plain,(
% 2.13/0.66    sK5 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | spl13_8),
% 2.13/0.66    inference(subsumption_resolution,[],[f1615,f275])).
% 2.13/0.66  fof(f275,plain,(
% 2.13/0.66    k1_xboole_0 != sK5 | spl13_8),
% 2.13/0.66    inference(avatar_component_clause,[],[f274])).
% 2.13/0.66  fof(f274,plain,(
% 2.13/0.66    spl13_8 <=> k1_xboole_0 = sK5),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).
% 2.13/0.66  fof(f1615,plain,(
% 2.13/0.66    sK5 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK5 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)),
% 2.13/0.66    inference(superposition,[],[f60,f72])).
% 2.13/0.66  fof(f72,plain,(
% 2.13/0.66    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)),
% 2.13/0.66    inference(definition_unfolding,[],[f41,f61,f61])).
% 2.13/0.66  fof(f61,plain,(
% 2.13/0.66    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f11])).
% 2.13/0.66  fof(f11,axiom,(
% 2.13/0.66    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.13/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 2.13/0.66  fof(f41,plain,(
% 2.13/0.66    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5)),
% 2.13/0.66    inference(cnf_transformation,[],[f24])).
% 2.13/0.66  fof(f91,plain,(
% 2.13/0.66    sK2 != sK5 | spl13_3),
% 2.13/0.66    inference(avatar_component_clause,[],[f89])).
% 2.13/0.66  fof(f89,plain,(
% 2.13/0.66    spl13_3 <=> sK2 = sK5),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).
% 2.13/0.66  fof(f1952,plain,(
% 2.13/0.66    spl13_2 | ~spl13_25),
% 2.13/0.66    inference(avatar_contradiction_clause,[],[f1951])).
% 2.13/0.66  fof(f1951,plain,(
% 2.13/0.66    $false | (spl13_2 | ~spl13_25)),
% 2.13/0.66    inference(subsumption_resolution,[],[f87,f1921])).
% 2.13/0.66  fof(f1921,plain,(
% 2.13/0.66    sK1 = sK4 | ~spl13_25),
% 2.13/0.66    inference(subsumption_resolution,[],[f1920,f42])).
% 2.13/0.66  fof(f42,plain,(
% 2.13/0.66    k1_xboole_0 != sK0),
% 2.13/0.66    inference(cnf_transformation,[],[f24])).
% 2.13/0.66  fof(f1920,plain,(
% 2.13/0.66    sK1 = sK4 | k1_xboole_0 = sK0 | ~spl13_25),
% 2.13/0.66    inference(subsumption_resolution,[],[f1918,f43])).
% 2.13/0.66  fof(f43,plain,(
% 2.13/0.66    k1_xboole_0 != sK1),
% 2.13/0.66    inference(cnf_transformation,[],[f24])).
% 2.13/0.66  fof(f1918,plain,(
% 2.13/0.66    sK1 = sK4 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl13_25),
% 2.13/0.66    inference(superposition,[],[f1700,f60])).
% 2.13/0.66  fof(f1700,plain,(
% 2.13/0.66    sK4 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl13_25),
% 2.13/0.66    inference(avatar_component_clause,[],[f1698])).
% 2.13/0.66  fof(f1698,plain,(
% 2.13/0.66    spl13_25 <=> sK4 = k2_relat_1(k2_zfmisc_1(sK0,sK1))),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_25])])).
% 2.13/0.66  fof(f87,plain,(
% 2.13/0.66    sK1 != sK4 | spl13_2),
% 2.13/0.66    inference(avatar_component_clause,[],[f85])).
% 2.13/0.66  fof(f85,plain,(
% 2.13/0.66    spl13_2 <=> sK1 = sK4),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 2.13/0.66  fof(f1946,plain,(
% 2.13/0.66    spl13_1 | ~spl13_26),
% 2.13/0.66    inference(avatar_contradiction_clause,[],[f1945])).
% 2.13/0.66  fof(f1945,plain,(
% 2.13/0.66    $false | (spl13_1 | ~spl13_26)),
% 2.13/0.66    inference(subsumption_resolution,[],[f1944,f42])).
% 2.13/0.66  fof(f1944,plain,(
% 2.13/0.66    k1_xboole_0 = sK0 | (spl13_1 | ~spl13_26)),
% 2.13/0.66    inference(subsumption_resolution,[],[f1943,f43])).
% 2.13/0.66  fof(f1943,plain,(
% 2.13/0.66    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl13_1 | ~spl13_26)),
% 2.13/0.66    inference(subsumption_resolution,[],[f1938,f83])).
% 2.13/0.66  fof(f83,plain,(
% 2.13/0.66    sK0 != sK3 | spl13_1),
% 2.13/0.66    inference(avatar_component_clause,[],[f81])).
% 2.13/0.66  fof(f81,plain,(
% 2.13/0.66    spl13_1 <=> sK0 = sK3),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 2.13/0.66  fof(f1938,plain,(
% 2.13/0.66    sK0 = sK3 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl13_26),
% 2.13/0.66    inference(superposition,[],[f59,f1705])).
% 2.13/0.66  fof(f1705,plain,(
% 2.13/0.66    sK3 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl13_26),
% 2.13/0.66    inference(avatar_component_clause,[],[f1703])).
% 2.13/0.66  fof(f1703,plain,(
% 2.13/0.66    spl13_26 <=> sK3 = k1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).
% 2.13/0.66  fof(f59,plain,(
% 2.13/0.66    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.13/0.66    inference(cnf_transformation,[],[f21])).
% 2.13/0.66  fof(f1886,plain,(
% 2.13/0.66    spl13_6 | spl13_24 | spl13_6 | spl13_8 | spl13_15),
% 2.13/0.66    inference(avatar_split_clause,[],[f1885,f770,f274,f157,f1424,f157])).
% 2.13/0.66  fof(f1424,plain,(
% 2.13/0.66    spl13_24 <=> k2_zfmisc_1(sK3,sK4) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 2.13/0.66    introduced(avatar_definition,[new_symbols(naming,[spl13_24])])).
% 2.13/0.66  fof(f1885,plain,(
% 2.13/0.66    k2_zfmisc_1(sK3,sK4) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | (spl13_6 | spl13_8 | spl13_15)),
% 2.13/0.66    inference(subsumption_resolution,[],[f1847,f44])).
% 2.13/0.66  fof(f1847,plain,(
% 2.13/0.66    k2_zfmisc_1(sK3,sK4) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | (spl13_6 | spl13_8 | spl13_15)),
% 2.13/0.66    inference(superposition,[],[f59,f1624])).
% 2.13/0.66  fof(f1624,plain,(
% 2.13/0.66    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK2) | (spl13_6 | spl13_8 | spl13_15)),
% 2.13/0.66    inference(backward_demodulation,[],[f72,f1621])).
% 2.13/0.66  fof(f1832,plain,(
% 2.13/0.66    spl13_7 | ~spl13_13),
% 2.13/0.66    inference(avatar_contradiction_clause,[],[f1831])).
% 2.13/0.66  fof(f1831,plain,(
% 2.13/0.66    $false | (spl13_7 | ~spl13_13)),
% 2.13/0.66    inference(subsumption_resolution,[],[f1824,f1116])).
% 2.13/0.66  fof(f1116,plain,(
% 2.13/0.66    ( ! [X7] : (~r2_hidden(X7,k1_xboole_0)) )),
% 2.13/0.66    inference(forward_demodulation,[],[f1114,f1065])).
% 2.13/0.66  fof(f1065,plain,(
% 2.13/0.66    ( ! [X5] : (k1_xboole_0 = k2_zfmisc_1(X5,k1_xboole_0)) )),
% 2.13/0.66    inference(resolution,[],[f683,f46])).
% 2.13/0.66  fof(f46,plain,(
% 2.13/0.66    v1_xboole_0(k1_xboole_0)),
% 2.13/0.66    inference(cnf_transformation,[],[f3])).
% 2.13/0.66  fof(f3,axiom,(
% 2.13/0.66    v1_xboole_0(k1_xboole_0)),
% 2.13/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.13/0.66  fof(f683,plain,(
% 2.13/0.66    ( ! [X6,X5] : (~v1_xboole_0(X6) | k1_xboole_0 = k2_zfmisc_1(X5,X6)) )),
% 2.13/0.66    inference(resolution,[],[f400,f49])).
% 2.13/0.66  fof(f49,plain,(
% 2.13/0.66    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f16])).
% 2.13/0.66  fof(f16,plain,(
% 2.13/0.66    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 2.13/0.66    inference(ennf_transformation,[],[f6])).
% 2.13/0.66  fof(f6,axiom,(
% 2.13/0.66    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 2.13/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 2.13/0.66  fof(f400,plain,(
% 2.13/0.66    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 2.13/0.66    inference(resolution,[],[f399,f51])).
% 2.13/0.66  fof(f51,plain,(
% 2.13/0.66    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0) )),
% 2.13/0.66    inference(cnf_transformation,[],[f19])).
% 2.13/0.66  fof(f19,plain,(
% 2.13/0.66    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 2.13/0.66    inference(ennf_transformation,[],[f8])).
% 2.13/0.66  fof(f8,axiom,(
% 2.13/0.66    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 2.13/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).
% 2.13/0.66  fof(f399,plain,(
% 2.13/0.66    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 2.13/0.66    inference(resolution,[],[f57,f47])).
% 2.13/0.66  fof(f47,plain,(
% 2.13/0.66    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f28])).
% 2.13/0.66  fof(f28,plain,(
% 2.13/0.66    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.13/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f26,f27])).
% 2.13/0.66  fof(f27,plain,(
% 2.13/0.66    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 2.13/0.66    introduced(choice_axiom,[])).
% 2.13/0.66  fof(f26,plain,(
% 2.13/0.66    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.13/0.66    inference(rectify,[],[f25])).
% 2.13/0.66  fof(f25,plain,(
% 2.13/0.66    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.13/0.66    inference(nnf_transformation,[],[f1])).
% 2.13/0.66  fof(f1,axiom,(
% 2.13/0.66    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.13/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.13/0.66  fof(f57,plain,(
% 2.13/0.66    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f34])).
% 2.13/0.66  fof(f34,plain,(
% 2.13/0.66    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.13/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f33])).
% 2.13/0.66  fof(f33,plain,(
% 2.13/0.66    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 2.13/0.66    introduced(choice_axiom,[])).
% 2.13/0.68  fof(f32,plain,(
% 2.13/0.68    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.13/0.68    inference(rectify,[],[f31])).
% 2.13/0.68  fof(f31,plain,(
% 2.13/0.68    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.13/0.68    inference(nnf_transformation,[],[f20])).
% 2.13/0.68  fof(f20,plain,(
% 2.13/0.68    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.13/0.68    inference(ennf_transformation,[],[f2])).
% 2.13/0.68  fof(f2,axiom,(
% 2.13/0.68    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.13/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.13/0.68  fof(f1114,plain,(
% 2.13/0.68    ( ! [X8,X7] : (~r2_hidden(X7,k2_zfmisc_1(X8,k1_xboole_0))) )),
% 2.13/0.68    inference(resolution,[],[f1111,f46])).
% 2.13/0.68  fof(f1111,plain,(
% 2.13/0.68    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.13/0.68    inference(resolution,[],[f78,f47])).
% 2.13/0.68  fof(f78,plain,(
% 2.13/0.68    ( ! [X0,X8,X1] : (r2_hidden(sK12(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 2.13/0.68    inference(equality_resolution,[],[f63])).
% 2.13/0.68  fof(f63,plain,(
% 2.13/0.68    ( ! [X2,X0,X8,X1] : (r2_hidden(sK12(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.13/0.68    inference(cnf_transformation,[],[f40])).
% 2.13/0.68  fof(f40,plain,(
% 2.13/0.68    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK8(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((sK8(X0,X1,X2) = k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2)) & r2_hidden(sK10(X0,X1,X2),X1) & r2_hidden(sK9(X0,X1,X2),X0)) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK11(X0,X1,X8),sK12(X0,X1,X8)) = X8 & r2_hidden(sK12(X0,X1,X8),X1) & r2_hidden(sK11(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.13/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11,sK12])],[f36,f39,f38,f37])).
% 2.13/0.68  fof(f37,plain,(
% 2.13/0.68    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK8(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK8(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 2.13/0.68    introduced(choice_axiom,[])).
% 2.13/0.68  fof(f38,plain,(
% 2.13/0.68    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK8(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK8(X0,X1,X2) = k4_tarski(sK9(X0,X1,X2),sK10(X0,X1,X2)) & r2_hidden(sK10(X0,X1,X2),X1) & r2_hidden(sK9(X0,X1,X2),X0)))),
% 2.13/0.68    introduced(choice_axiom,[])).
% 2.13/0.68  fof(f39,plain,(
% 2.13/0.68    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK11(X0,X1,X8),sK12(X0,X1,X8)) = X8 & r2_hidden(sK12(X0,X1,X8),X1) & r2_hidden(sK11(X0,X1,X8),X0)))),
% 2.13/0.68    introduced(choice_axiom,[])).
% 2.13/0.68  fof(f36,plain,(
% 2.13/0.68    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.13/0.68    inference(rectify,[],[f35])).
% 2.13/0.68  fof(f35,plain,(
% 2.13/0.68    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.13/0.68    inference(nnf_transformation,[],[f5])).
% 2.13/0.68  fof(f5,axiom,(
% 2.13/0.68    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 2.13/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 2.13/0.68  fof(f1824,plain,(
% 2.13/0.68    r2_hidden(sK6(k1_xboole_0),k1_xboole_0) | (spl13_7 | ~spl13_13)),
% 2.13/0.68    inference(backward_demodulation,[],[f413,f747])).
% 2.13/0.68  fof(f747,plain,(
% 2.13/0.68    k1_xboole_0 = sK4 | ~spl13_13),
% 2.13/0.68    inference(avatar_component_clause,[],[f745])).
% 2.13/0.68  fof(f745,plain,(
% 2.13/0.68    spl13_13 <=> k1_xboole_0 = sK4),
% 2.13/0.68    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).
% 2.13/0.68  fof(f413,plain,(
% 2.13/0.68    r2_hidden(sK6(sK4),sK4) | spl13_7),
% 2.13/0.68    inference(resolution,[],[f404,f48])).
% 2.13/0.68  fof(f48,plain,(
% 2.13/0.68    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) )),
% 2.13/0.68    inference(cnf_transformation,[],[f28])).
% 2.13/0.68  fof(f404,plain,(
% 2.13/0.68    ~v1_xboole_0(sK4) | spl13_7),
% 2.13/0.68    inference(resolution,[],[f402,f49])).
% 2.13/0.68  fof(f402,plain,(
% 2.13/0.68    ~v1_xboole_0(k2_zfmisc_1(sK3,sK4)) | spl13_7),
% 2.13/0.68    inference(resolution,[],[f399,f163])).
% 2.13/0.68  fof(f163,plain,(
% 2.13/0.68    ~r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | spl13_7),
% 2.13/0.68    inference(avatar_component_clause,[],[f161])).
% 2.13/0.68  fof(f161,plain,(
% 2.13/0.68    spl13_7 <=> r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 2.13/0.68    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).
% 2.13/0.68  fof(f1797,plain,(
% 2.13/0.68    ~spl13_11 | spl13_15 | spl13_19 | ~spl13_24),
% 2.13/0.68    inference(avatar_contradiction_clause,[],[f1796])).
% 2.13/0.68  fof(f1796,plain,(
% 2.13/0.68    $false | (~spl13_11 | spl13_15 | spl13_19 | ~spl13_24)),
% 2.13/0.68    inference(subsumption_resolution,[],[f1785,f1197])).
% 2.13/0.68  fof(f1197,plain,(
% 2.13/0.68    ( ! [X4,X3] : (~r2_hidden(X3,k2_zfmisc_1(k1_xboole_0,X4))) )),
% 2.13/0.68    inference(resolution,[],[f79,f1116])).
% 2.13/0.68  fof(f79,plain,(
% 2.13/0.68    ( ! [X0,X8,X1] : (r2_hidden(sK11(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 2.13/0.68    inference(equality_resolution,[],[f62])).
% 2.13/0.68  fof(f62,plain,(
% 2.13/0.68    ( ! [X2,X0,X8,X1] : (r2_hidden(sK11(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.13/0.68    inference(cnf_transformation,[],[f40])).
% 2.13/0.68  fof(f1785,plain,(
% 2.13/0.68    r2_hidden(sK6(k2_zfmisc_1(k1_xboole_0,sK4)),k2_zfmisc_1(k1_xboole_0,sK4)) | (~spl13_11 | spl13_15 | spl13_19 | ~spl13_24)),
% 2.13/0.68    inference(backward_demodulation,[],[f1305,f1730])).
% 2.13/0.68  fof(f1730,plain,(
% 2.13/0.68    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,sK4) | (~spl13_11 | spl13_15 | ~spl13_24)),
% 2.13/0.68    inference(backward_demodulation,[],[f1681,f738])).
% 2.13/0.68  fof(f738,plain,(
% 2.13/0.68    k1_xboole_0 = sK3 | ~spl13_11),
% 2.13/0.68    inference(avatar_component_clause,[],[f736])).
% 2.13/0.68  fof(f736,plain,(
% 2.13/0.68    spl13_11 <=> k1_xboole_0 = sK3),
% 2.13/0.68    introduced(avatar_definition,[new_symbols(naming,[spl13_11])])).
% 2.13/0.68  fof(f1681,plain,(
% 2.13/0.68    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4) | (spl13_15 | ~spl13_24)),
% 2.13/0.68    inference(subsumption_resolution,[],[f1680,f771])).
% 2.13/0.68  fof(f1680,plain,(
% 2.13/0.68    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl13_24),
% 2.13/0.68    inference(subsumption_resolution,[],[f1678,f44])).
% 2.13/0.68  fof(f1678,plain,(
% 2.13/0.68    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl13_24),
% 2.13/0.68    inference(superposition,[],[f1426,f59])).
% 2.13/0.68  fof(f1426,plain,(
% 2.13/0.68    k2_zfmisc_1(sK3,sK4) = k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl13_24),
% 2.13/0.68    inference(avatar_component_clause,[],[f1424])).
% 2.13/0.68  fof(f1305,plain,(
% 2.13/0.68    r2_hidden(sK6(k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) | spl13_19),
% 2.13/0.68    inference(resolution,[],[f818,f48])).
% 2.13/0.68  fof(f818,plain,(
% 2.13/0.68    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl13_19),
% 2.13/0.68    inference(avatar_component_clause,[],[f817])).
% 2.13/0.68  fof(f817,plain,(
% 2.13/0.68    spl13_19 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 2.13/0.68    introduced(avatar_definition,[new_symbols(naming,[spl13_19])])).
% 2.13/0.68  fof(f1706,plain,(
% 2.13/0.68    spl13_11 | spl13_13 | spl13_26 | spl13_15 | ~spl13_24),
% 2.13/0.68    inference(avatar_split_clause,[],[f1692,f1424,f770,f1703,f745,f736])).
% 2.13/0.68  fof(f1692,plain,(
% 2.13/0.68    sK3 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | (spl13_15 | ~spl13_24)),
% 2.13/0.68    inference(superposition,[],[f59,f1681])).
% 2.13/0.68  fof(f1701,plain,(
% 2.13/0.68    spl13_11 | spl13_13 | spl13_25 | spl13_15 | ~spl13_24),
% 2.13/0.68    inference(avatar_split_clause,[],[f1691,f1424,f770,f1698,f745,f736])).
% 2.13/0.68  fof(f1691,plain,(
% 2.13/0.68    sK4 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | (spl13_15 | ~spl13_24)),
% 2.13/0.68    inference(superposition,[],[f60,f1681])).
% 2.13/0.68  fof(f1519,plain,(
% 2.13/0.68    spl13_4 | spl13_7 | ~spl13_8),
% 2.13/0.68    inference(avatar_contradiction_clause,[],[f1518])).
% 2.13/0.68  fof(f1518,plain,(
% 2.13/0.68    $false | (spl13_4 | spl13_7 | ~spl13_8)),
% 2.13/0.68    inference(subsumption_resolution,[],[f1517,f46])).
% 2.13/0.68  fof(f1517,plain,(
% 2.13/0.68    ~v1_xboole_0(k1_xboole_0) | (spl13_4 | spl13_7 | ~spl13_8)),
% 2.13/0.68    inference(forward_demodulation,[],[f1447,f1065])).
% 2.13/0.68  fof(f1447,plain,(
% 2.13/0.68    ~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) | (spl13_4 | spl13_7 | ~spl13_8)),
% 2.13/0.68    inference(backward_demodulation,[],[f1400,f276])).
% 2.13/0.68  fof(f276,plain,(
% 2.13/0.68    k1_xboole_0 = sK5 | ~spl13_8),
% 2.13/0.68    inference(avatar_component_clause,[],[f274])).
% 2.13/0.68  fof(f1400,plain,(
% 2.13/0.68    ~v1_xboole_0(k2_zfmisc_1(sK5,sK5)) | (spl13_4 | spl13_7)),
% 2.13/0.68    inference(resolution,[],[f410,f49])).
% 2.13/0.68  fof(f410,plain,(
% 2.13/0.68    ~v1_xboole_0(k2_zfmisc_1(sK4,k2_zfmisc_1(sK5,sK5))) | (spl13_4 | spl13_7)),
% 2.13/0.68    inference(resolution,[],[f404,f110])).
% 2.13/0.68  fof(f110,plain,(
% 2.13/0.68    ( ! [X0] : (v1_xboole_0(X0) | ~v1_xboole_0(k2_zfmisc_1(X0,k2_zfmisc_1(sK5,sK5)))) ) | spl13_4),
% 2.13/0.68    inference(resolution,[],[f107,f50])).
% 2.13/0.68  fof(f50,plain,(
% 2.13/0.68    ( ! [X0,X1] : (v1_xboole_0(X1) | ~v1_xboole_0(k2_zfmisc_1(X0,X1)) | v1_xboole_0(X0)) )),
% 2.13/0.68    inference(cnf_transformation,[],[f18])).
% 2.13/0.68  fof(f18,plain,(
% 2.13/0.68    ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.13/0.68    inference(flattening,[],[f17])).
% 2.13/0.68  fof(f17,plain,(
% 2.13/0.68    ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.13/0.68    inference(ennf_transformation,[],[f9])).
% 2.13/0.68  fof(f9,axiom,(
% 2.13/0.68    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 2.13/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_subset_1)).
% 2.13/0.68  fof(f107,plain,(
% 2.13/0.68    ~v1_xboole_0(k2_zfmisc_1(sK5,sK5)) | spl13_4),
% 2.13/0.68    inference(resolution,[],[f105,f97])).
% 2.13/0.68  fof(f97,plain,(
% 2.13/0.68    ~v1_xboole_0(sK5) | spl13_4),
% 2.13/0.68    inference(avatar_component_clause,[],[f95])).
% 2.13/0.68  fof(f95,plain,(
% 2.13/0.68    spl13_4 <=> v1_xboole_0(sK5)),
% 2.13/0.68    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).
% 2.13/0.68  fof(f105,plain,(
% 2.13/0.68    ( ! [X0] : (v1_xboole_0(X0) | ~v1_xboole_0(k2_zfmisc_1(X0,sK5))) ) | spl13_4),
% 2.13/0.68    inference(resolution,[],[f50,f97])).
% 2.13/0.68  fof(f1302,plain,(
% 2.13/0.68    spl13_15 | ~spl13_19),
% 2.13/0.68    inference(avatar_contradiction_clause,[],[f1301])).
% 2.13/0.68  fof(f1301,plain,(
% 2.13/0.68    $false | (spl13_15 | ~spl13_19)),
% 2.13/0.68    inference(subsumption_resolution,[],[f1293,f771])).
% 2.13/0.68  fof(f1293,plain,(
% 2.13/0.68    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl13_19),
% 2.13/0.68    inference(resolution,[],[f819,f400])).
% 2.13/0.68  fof(f819,plain,(
% 2.13/0.68    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl13_19),
% 2.13/0.68    inference(avatar_component_clause,[],[f817])).
% 2.13/0.68  fof(f1242,plain,(
% 2.13/0.68    spl13_18),
% 2.13/0.68    inference(avatar_contradiction_clause,[],[f1199])).
% 2.13/0.68  fof(f1199,plain,(
% 2.13/0.68    $false | spl13_18),
% 2.13/0.68    inference(resolution,[],[f1197,f932])).
% 2.13/0.68  fof(f932,plain,(
% 2.13/0.68    r2_hidden(sK6(k2_zfmisc_1(k1_xboole_0,sK5)),k2_zfmisc_1(k1_xboole_0,sK5)) | spl13_18),
% 2.13/0.68    inference(resolution,[],[f784,f48])).
% 2.13/0.68  fof(f784,plain,(
% 2.13/0.68    ~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK5)) | spl13_18),
% 2.13/0.68    inference(avatar_component_clause,[],[f783])).
% 2.13/0.68  fof(f783,plain,(
% 2.13/0.68    spl13_18 <=> v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK5))),
% 2.13/0.68    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).
% 2.13/0.68  fof(f960,plain,(
% 2.13/0.68    ~spl13_15),
% 2.13/0.68    inference(avatar_contradiction_clause,[],[f959])).
% 2.13/0.68  fof(f959,plain,(
% 2.13/0.68    $false | ~spl13_15),
% 2.13/0.68    inference(subsumption_resolution,[],[f958,f942])).
% 2.13/0.68  fof(f942,plain,(
% 2.13/0.68    ~v1_xboole_0(sK0) | ~spl13_15),
% 2.13/0.68    inference(resolution,[],[f938,f399])).
% 2.13/0.68  fof(f938,plain,(
% 2.13/0.68    ~r1_tarski(sK0,k1_xboole_0) | ~spl13_15),
% 2.13/0.68    inference(subsumption_resolution,[],[f935,f42])).
% 2.13/0.68  fof(f935,plain,(
% 2.13/0.68    ~r1_tarski(sK0,k1_xboole_0) | k1_xboole_0 = sK0 | ~spl13_15),
% 2.13/0.68    inference(superposition,[],[f51,f772])).
% 2.13/0.68  fof(f772,plain,(
% 2.13/0.68    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl13_15),
% 2.13/0.68    inference(avatar_component_clause,[],[f770])).
% 2.13/0.68  fof(f958,plain,(
% 2.13/0.68    v1_xboole_0(sK0) | ~spl13_15),
% 2.13/0.68    inference(subsumption_resolution,[],[f957,f46])).
% 2.13/0.68  fof(f957,plain,(
% 2.13/0.68    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK0) | ~spl13_15),
% 2.13/0.68    inference(superposition,[],[f940,f772])).
% 2.13/0.68  fof(f940,plain,(
% 2.13/0.68    ( ! [X0] : (~v1_xboole_0(k2_zfmisc_1(X0,sK1)) | v1_xboole_0(X0)) ) | ~spl13_15),
% 2.13/0.68    inference(resolution,[],[f939,f50])).
% 2.13/0.68  fof(f939,plain,(
% 2.13/0.68    ~v1_xboole_0(sK1) | ~spl13_15),
% 2.13/0.68    inference(resolution,[],[f937,f399])).
% 2.13/0.68  fof(f937,plain,(
% 2.13/0.68    ~r1_tarski(sK1,k1_xboole_0) | ~spl13_15),
% 2.13/0.68    inference(subsumption_resolution,[],[f934,f43])).
% 2.13/0.68  fof(f934,plain,(
% 2.13/0.68    ~r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 = sK1 | ~spl13_15),
% 2.13/0.68    inference(superposition,[],[f52,f772])).
% 2.13/0.68  fof(f52,plain,(
% 2.13/0.68    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0) )),
% 2.13/0.68    inference(cnf_transformation,[],[f19])).
% 2.13/0.68  fof(f926,plain,(
% 2.13/0.68    ~spl13_17),
% 2.13/0.68    inference(avatar_contradiction_clause,[],[f925])).
% 2.13/0.68  fof(f925,plain,(
% 2.13/0.68    $false | ~spl13_17),
% 2.13/0.68    inference(subsumption_resolution,[],[f924,f44])).
% 2.13/0.68  fof(f924,plain,(
% 2.13/0.68    k1_xboole_0 = sK2 | ~spl13_17),
% 2.13/0.68    inference(resolution,[],[f780,f400])).
% 2.13/0.68  fof(f780,plain,(
% 2.13/0.68    v1_xboole_0(sK2) | ~spl13_17),
% 2.13/0.68    inference(avatar_component_clause,[],[f779])).
% 2.13/0.68  fof(f779,plain,(
% 2.13/0.68    spl13_17 <=> v1_xboole_0(sK2)),
% 2.13/0.68    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).
% 2.13/0.68  fof(f923,plain,(
% 2.13/0.68    ~spl13_5 | spl13_17),
% 2.13/0.68    inference(avatar_contradiction_clause,[],[f922])).
% 2.13/0.68  fof(f922,plain,(
% 2.13/0.68    $false | (~spl13_5 | spl13_17)),
% 2.13/0.68    inference(subsumption_resolution,[],[f921,f882])).
% 2.13/0.68  fof(f882,plain,(
% 2.13/0.68    ~v1_xboole_0(sK0) | (~spl13_5 | spl13_17)),
% 2.13/0.68    inference(resolution,[],[f878,f399])).
% 2.13/0.68  fof(f878,plain,(
% 2.13/0.68    ~r1_tarski(sK0,k1_xboole_0) | (~spl13_5 | spl13_17)),
% 2.13/0.68    inference(subsumption_resolution,[],[f875,f42])).
% 2.13/0.68  fof(f875,plain,(
% 2.13/0.68    ~r1_tarski(sK0,k1_xboole_0) | k1_xboole_0 = sK0 | (~spl13_5 | spl13_17)),
% 2.13/0.68    inference(superposition,[],[f51,f864])).
% 2.13/0.68  fof(f864,plain,(
% 2.13/0.68    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (~spl13_5 | spl13_17)),
% 2.13/0.68    inference(resolution,[],[f861,f400])).
% 2.13/0.68  fof(f861,plain,(
% 2.13/0.68    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | (~spl13_5 | spl13_17)),
% 2.13/0.68    inference(resolution,[],[f101,f789])).
% 2.13/0.68  fof(f789,plain,(
% 2.13/0.68    ( ! [X0] : (~v1_xboole_0(k2_zfmisc_1(X0,sK2)) | v1_xboole_0(X0)) ) | spl13_17),
% 2.13/0.68    inference(resolution,[],[f781,f50])).
% 2.13/0.68  fof(f781,plain,(
% 2.13/0.68    ~v1_xboole_0(sK2) | spl13_17),
% 2.13/0.68    inference(avatar_component_clause,[],[f779])).
% 2.13/0.68  fof(f101,plain,(
% 2.13/0.68    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl13_5),
% 2.13/0.68    inference(avatar_component_clause,[],[f99])).
% 2.13/0.68  fof(f99,plain,(
% 2.13/0.68    spl13_5 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 2.13/0.68    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).
% 2.13/0.68  fof(f921,plain,(
% 2.13/0.68    v1_xboole_0(sK0) | (~spl13_5 | spl13_17)),
% 2.13/0.68    inference(subsumption_resolution,[],[f920,f46])).
% 2.13/0.68  fof(f920,plain,(
% 2.13/0.68    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK0) | (~spl13_5 | spl13_17)),
% 2.13/0.68    inference(superposition,[],[f880,f864])).
% 2.13/0.68  fof(f880,plain,(
% 2.13/0.68    ( ! [X0] : (~v1_xboole_0(k2_zfmisc_1(X0,sK1)) | v1_xboole_0(X0)) ) | (~spl13_5 | spl13_17)),
% 2.13/0.68    inference(resolution,[],[f879,f50])).
% 2.13/0.68  fof(f879,plain,(
% 2.13/0.68    ~v1_xboole_0(sK1) | (~spl13_5 | spl13_17)),
% 2.13/0.68    inference(resolution,[],[f877,f399])).
% 2.13/0.68  fof(f877,plain,(
% 2.13/0.68    ~r1_tarski(sK1,k1_xboole_0) | (~spl13_5 | spl13_17)),
% 2.13/0.68    inference(subsumption_resolution,[],[f874,f43])).
% 2.13/0.68  fof(f874,plain,(
% 2.13/0.68    ~r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 = sK1 | (~spl13_5 | spl13_17)),
% 2.13/0.68    inference(superposition,[],[f52,f864])).
% 2.13/0.68  fof(f820,plain,(
% 2.13/0.68    spl13_19 | ~spl13_18 | ~spl13_6 | spl13_17),
% 2.13/0.68    inference(avatar_split_clause,[],[f815,f779,f157,f783,f817])).
% 2.13/0.68  fof(f815,plain,(
% 2.13/0.68    ~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK5)) | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | (~spl13_6 | spl13_17)),
% 2.13/0.68    inference(superposition,[],[f789,f714])).
% 2.13/0.68  fof(f714,plain,(
% 2.13/0.68    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k1_xboole_0,sK5) | ~spl13_6),
% 2.13/0.68    inference(backward_demodulation,[],[f72,f159])).
% 2.13/0.68  fof(f159,plain,(
% 2.13/0.68    k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | ~spl13_6),
% 2.13/0.68    inference(avatar_component_clause,[],[f157])).
% 2.13/0.68  fof(f164,plain,(
% 2.13/0.68    spl13_6 | ~spl13_7),
% 2.13/0.68    inference(avatar_split_clause,[],[f155,f161,f157])).
% 2.13/0.68  fof(f155,plain,(
% 2.13/0.68    ~r1_tarski(k2_zfmisc_1(sK3,sK4),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = k2_zfmisc_1(sK3,sK4)),
% 2.13/0.68    inference(superposition,[],[f51,f72])).
% 2.13/0.68  fof(f102,plain,(
% 2.13/0.68    ~spl13_4 | spl13_5),
% 2.13/0.68    inference(avatar_split_clause,[],[f93,f99,f95])).
% 2.13/0.68  fof(f93,plain,(
% 2.13/0.68    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~v1_xboole_0(sK5)),
% 2.13/0.68    inference(superposition,[],[f49,f72])).
% 2.13/0.68  fof(f92,plain,(
% 2.13/0.68    ~spl13_1 | ~spl13_2 | ~spl13_3),
% 2.13/0.68    inference(avatar_split_clause,[],[f45,f89,f85,f81])).
% 2.13/0.68  fof(f45,plain,(
% 2.13/0.68    sK2 != sK5 | sK1 != sK4 | sK0 != sK3),
% 2.13/0.68    inference(cnf_transformation,[],[f24])).
% 2.13/0.68  % SZS output end Proof for theBenchmark
% 2.13/0.68  % (10420)------------------------------
% 2.13/0.68  % (10420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.68  % (10420)Termination reason: Refutation
% 2.13/0.68  
% 2.13/0.68  % (10420)Memory used [KB]: 11385
% 2.13/0.68  % (10420)Time elapsed: 0.244 s
% 2.13/0.68  % (10420)------------------------------
% 2.13/0.68  % (10420)------------------------------
% 2.13/0.68  % (10416)Success in time 0.312 s
%------------------------------------------------------------------------------
