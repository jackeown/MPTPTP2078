%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 152 expanded)
%              Number of leaves         :   26 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  301 ( 459 expanded)
%              Number of equality atoms :   67 ( 102 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f437,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f76,f80,f88,f265,f278,f306,f307,f310,f318,f322,f424,f431])).

fof(f431,plain,(
    ~ spl3_36 ),
    inference(avatar_contradiction_clause,[],[f428])).

fof(f428,plain,
    ( $false
    | ~ spl3_36 ),
    inference(resolution,[],[f423,f89])).

fof(f89,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f49,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f423,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_xboole_0)
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f422])).

fof(f422,plain,
    ( spl3_36
  <=> r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f424,plain,
    ( ~ spl3_28
    | spl3_36
    | ~ spl3_3
    | ~ spl3_23
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f419,f316,f276,f78,f422,f320])).

fof(f320,plain,
    ( spl3_28
  <=> r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f78,plain,
    ( spl3_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f276,plain,
    ( spl3_23
  <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f316,plain,
    ( spl3_27
  <=> r2_hidden(sK2(k1_relat_1(sK1),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f419,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_xboole_0)
    | ~ r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(sK1))
    | ~ spl3_3
    | ~ spl3_23
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f416,f277])).

fof(f277,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f276])).

fof(f416,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(sK1))
    | ~ spl3_3
    | ~ spl3_27 ),
    inference(resolution,[],[f360,f79])).

fof(f79,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f360,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(X0,sK0)))
        | ~ r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(X0)) )
    | ~ spl3_27 ),
    inference(resolution,[],[f317,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f317,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0),sK0)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f316])).

fof(f322,plain,
    ( spl3_28
    | spl3_2 ),
    inference(avatar_split_clause,[],[f313,f71,f320])).

fof(f71,plain,
    ( spl3_2
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f313,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(sK1))
    | spl3_2 ),
    inference(resolution,[],[f72,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f72,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f318,plain,
    ( spl3_27
    | spl3_2 ),
    inference(avatar_split_clause,[],[f312,f71,f316])).

fof(f312,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0),sK0)
    | spl3_2 ),
    inference(resolution,[],[f72,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f310,plain,
    ( ~ spl3_3
    | spl3_25 ),
    inference(avatar_split_clause,[],[f309,f300,f78])).

fof(f300,plain,
    ( spl3_25
  <=> v1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f309,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_25 ),
    inference(resolution,[],[f301,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f301,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl3_25 ),
    inference(avatar_component_clause,[],[f300])).

fof(f307,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f306,plain,
    ( ~ spl3_25
    | spl3_1
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f294,f276,f68,f300])).

fof(f68,plain,
    ( spl3_1
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f294,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl3_23 ),
    inference(trivial_inequality_removal,[],[f293])).

fof(f293,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl3_23 ),
    inference(superposition,[],[f47,f277])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f278,plain,
    ( spl3_23
    | ~ spl3_2
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f270,f263,f71,f276])).

fof(f263,plain,
    ( spl3_22
  <=> ! [X1] :
        ( ~ r1_xboole_0(k1_relat_1(sK1),X1)
        | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f270,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl3_2
    | ~ spl3_22 ),
    inference(resolution,[],[f264,f75])).

fof(f75,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f264,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(k1_relat_1(sK1),X1)
        | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X1)) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f263])).

fof(f265,plain,
    ( ~ spl3_3
    | spl3_22
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f255,f78,f263,f78])).

fof(f255,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(k1_relat_1(sK1),X1)
        | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X1))
        | ~ v1_relat_1(sK1) )
    | ~ spl3_3 ),
    inference(resolution,[],[f109,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

fof(f109,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X1)
        | ~ r1_xboole_0(X1,X0)
        | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X0)) )
    | ~ spl3_3 ),
    inference(resolution,[],[f107,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f107,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X0)
        | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X0)) )
    | ~ spl3_3 ),
    inference(resolution,[],[f105,f79])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X1)
      | k1_xboole_0 = k1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f91,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_relat_1(k7_relat_1(X0,X1)))
      | ~ r1_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f55,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f88,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f44,f86])).

fof(f86,plain,
    ( spl3_5
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f44,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f80,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f41,f78])).

fof(f41,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k7_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k7_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f33])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k7_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k7_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f76,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f42,f71,f68])).

fof(f42,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f73,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f43,f71,f68])).

fof(f43,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n019.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 19:47:37 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.47  % (29903)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (29912)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (29905)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (29897)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (29904)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (29898)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (29898)Refutation not found, incomplete strategy% (29898)------------------------------
% 0.21/0.48  % (29898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (29898)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.49  % (29898)Memory used [KB]: 10618
% 0.21/0.49  % (29898)Time elapsed: 0.069 s
% 0.21/0.49  % (29898)------------------------------
% 0.21/0.49  % (29898)------------------------------
% 0.21/0.49  % (29900)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (29901)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (29913)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (29899)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (29902)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (29911)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (29908)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (29903)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f437,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f73,f76,f80,f88,f265,f278,f306,f307,f310,f318,f322,f424,f431])).
% 0.21/0.50  fof(f431,plain,(
% 0.21/0.50    ~spl3_36),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f428])).
% 0.21/0.50  fof(f428,plain,(
% 0.21/0.50    $false | ~spl3_36),
% 0.21/0.50    inference(resolution,[],[f423,f89])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(superposition,[],[f49,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.50    inference(flattening,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.50  fof(f423,plain,(
% 0.21/0.50    r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_xboole_0) | ~spl3_36),
% 0.21/0.50    inference(avatar_component_clause,[],[f422])).
% 0.21/0.50  fof(f422,plain,(
% 0.21/0.50    spl3_36 <=> r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.50  fof(f424,plain,(
% 0.21/0.50    ~spl3_28 | spl3_36 | ~spl3_3 | ~spl3_23 | ~spl3_27),
% 0.21/0.50    inference(avatar_split_clause,[],[f419,f316,f276,f78,f422,f320])).
% 0.21/0.50  fof(f320,plain,(
% 0.21/0.50    spl3_28 <=> r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    spl3_3 <=> v1_relat_1(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    spl3_23 <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.50  fof(f316,plain,(
% 0.21/0.50    spl3_27 <=> r2_hidden(sK2(k1_relat_1(sK1),sK0),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.50  fof(f419,plain,(
% 0.21/0.50    r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_xboole_0) | ~r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(sK1)) | (~spl3_3 | ~spl3_23 | ~spl3_27)),
% 0.21/0.50    inference(forward_demodulation,[],[f416,f277])).
% 0.21/0.50  fof(f277,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~spl3_23),
% 0.21/0.50    inference(avatar_component_clause,[],[f276])).
% 0.21/0.50  fof(f416,plain,(
% 0.21/0.50    r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(sK1,sK0))) | ~r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(sK1)) | (~spl3_3 | ~spl3_27)),
% 0.21/0.50    inference(resolution,[],[f360,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    v1_relat_1(sK1) | ~spl3_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f78])).
% 0.21/0.50  fof(f360,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(X0) | r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(k7_relat_1(X0,sK0))) | ~r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(X0))) ) | ~spl3_27),
% 0.21/0.50    inference(resolution,[],[f317,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 0.21/0.50  fof(f317,plain,(
% 0.21/0.50    r2_hidden(sK2(k1_relat_1(sK1),sK0),sK0) | ~spl3_27),
% 0.21/0.50    inference(avatar_component_clause,[],[f316])).
% 0.21/0.50  fof(f322,plain,(
% 0.21/0.50    spl3_28 | spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f313,f71,f320])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    spl3_2 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.50  fof(f313,plain,(
% 0.21/0.50    r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(sK1)) | spl3_2),
% 0.21/0.50    inference(resolution,[],[f72,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(rectify,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl3_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f71])).
% 0.21/0.50  fof(f318,plain,(
% 0.21/0.50    spl3_27 | spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f312,f71,f316])).
% 0.21/0.50  fof(f312,plain,(
% 0.21/0.50    r2_hidden(sK2(k1_relat_1(sK1),sK0),sK0) | spl3_2),
% 0.21/0.50    inference(resolution,[],[f72,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f310,plain,(
% 0.21/0.50    ~spl3_3 | spl3_25),
% 0.21/0.50    inference(avatar_split_clause,[],[f309,f300,f78])).
% 0.21/0.50  fof(f300,plain,(
% 0.21/0.50    spl3_25 <=> v1_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.50  fof(f309,plain,(
% 0.21/0.50    ~v1_relat_1(sK1) | spl3_25),
% 0.21/0.50    inference(resolution,[],[f301,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.50  fof(f301,plain,(
% 0.21/0.50    ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl3_25),
% 0.21/0.50    inference(avatar_component_clause,[],[f300])).
% 0.21/0.50  fof(f307,plain,(
% 0.21/0.50    k1_xboole_0 != k7_relat_1(sK1,sK0) | k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f306,plain,(
% 0.21/0.50    ~spl3_25 | spl3_1 | ~spl3_23),
% 0.21/0.50    inference(avatar_split_clause,[],[f294,f276,f68,f300])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    spl3_1 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.50  fof(f294,plain,(
% 0.21/0.50    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~spl3_23),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f293])).
% 0.21/0.50  fof(f293,plain,(
% 0.21/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k7_relat_1(sK1,sK0) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~spl3_23),
% 0.21/0.50    inference(superposition,[],[f47,f277])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.50  fof(f278,plain,(
% 0.21/0.50    spl3_23 | ~spl3_2 | ~spl3_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f270,f263,f71,f276])).
% 0.21/0.50  fof(f263,plain,(
% 0.21/0.50    spl3_22 <=> ! [X1] : (~r1_xboole_0(k1_relat_1(sK1),X1) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.50  fof(f270,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | (~spl3_2 | ~spl3_22)),
% 0.21/0.50    inference(resolution,[],[f264,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl3_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f71])).
% 0.21/0.50  fof(f264,plain,(
% 0.21/0.50    ( ! [X1] : (~r1_xboole_0(k1_relat_1(sK1),X1) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X1))) ) | ~spl3_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f263])).
% 0.21/0.50  fof(f265,plain,(
% 0.21/0.50    ~spl3_3 | spl3_22 | ~spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f255,f78,f263,f78])).
% 0.21/0.50  fof(f255,plain,(
% 0.21/0.50    ( ! [X1] : (~r1_xboole_0(k1_relat_1(sK1),X1) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) ) | ~spl3_3),
% 0.21/0.50    inference(resolution,[],[f109,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X1) | ~r1_xboole_0(X1,X0) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X0))) ) | ~spl3_3),
% 0.21/0.50    inference(resolution,[],[f107,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X0) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X0))) ) | ~spl3_3),
% 0.21/0.50    inference(resolution,[],[f105,f79])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X1) | k1_xboole_0 = k1_relat_1(k7_relat_1(X0,X1))) )),
% 0.21/0.50    inference(resolution,[],[f91,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_xboole_0(k1_relat_1(k7_relat_1(X0,X1))) | ~r1_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(resolution,[],[f55,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0) | v1_xboole_0(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f44,f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    spl3_5 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f41,f78])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    v1_relat_1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.50    inference(negated_conjecture,[],[f14])).
% 0.21/0.50  fof(f14,conjecture,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl3_1 | spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f42,f71,f68])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ~spl3_1 | ~spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f43,f71,f68])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (29903)------------------------------
% 0.21/0.50  % (29903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (29903)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (29903)Memory used [KB]: 10874
% 0.21/0.50  % (29903)Time elapsed: 0.079 s
% 0.21/0.50  % (29903)------------------------------
% 0.21/0.50  % (29903)------------------------------
% 0.21/0.50  % (29915)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (29917)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (29896)Success in time 0.15 s
%------------------------------------------------------------------------------
