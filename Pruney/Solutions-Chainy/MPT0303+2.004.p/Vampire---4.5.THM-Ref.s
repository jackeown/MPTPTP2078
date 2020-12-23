%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 212 expanded)
%              Number of leaves         :   12 (  61 expanded)
%              Depth                    :   17
%              Number of atoms          :  293 ( 933 expanded)
%              Number of equality atoms :   52 ( 170 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f248,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f67,f195,f219,f227,f247])).

fof(f247,plain,
    ( ~ spl4_1
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f245,f23])).

fof(f23,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( sK0 != sK1
    & k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) )
   => ( sK0 != sK1
      & k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_zfmisc_1)).

fof(f245,plain,
    ( sK0 = sK1
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(resolution,[],[f235,f228])).

fof(f228,plain,
    ( ! [X5] : ~ r2_hidden(X5,sK1)
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f62,f45])).

fof(f45,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl4_1
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f62,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,sK1)
        | r2_hidden(X5,sK0) )
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl4_3
  <=> ! [X5] :
        ( ~ r2_hidden(X5,sK1)
        | r2_hidden(X5,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f235,plain,
    ( ! [X8,X7] :
        ( r2_hidden(sK3(sK0,X7,X8),X8)
        | sK0 = X8 )
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f224,f234])).

fof(f234,plain,
    ( ! [X0] : sK0 = k3_xboole_0(sK0,X0)
    | ~ spl4_1 ),
    inference(resolution,[],[f220,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f220,plain,
    ( ! [X0] : r1_tarski(sK0,X0)
    | ~ spl4_1 ),
    inference(resolution,[],[f45,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f224,plain,
    ( ! [X8,X7] :
        ( r2_hidden(sK3(sK0,X7,X8),X8)
        | k3_xboole_0(sK0,X7) = X8 )
    | ~ spl4_1 ),
    inference(resolution,[],[f45,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f227,plain,
    ( ~ spl4_1
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f225,f23])).

fof(f225,plain,
    ( sK0 = sK1
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(resolution,[],[f45,f208])).

fof(f208,plain,
    ( ! [X8,X9] :
        ( r2_hidden(sK3(sK1,X8,X9),X9)
        | sK1 = X9 )
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f201,f207])).

fof(f207,plain,
    ( ! [X0] : sK1 = k3_xboole_0(sK1,X0)
    | ~ spl4_4 ),
    inference(resolution,[],[f197,f24])).

fof(f197,plain,
    ( ! [X1] : r1_tarski(sK1,X1)
    | ~ spl4_4 ),
    inference(resolution,[],[f65,f25])).

fof(f65,plain,
    ( ! [X4] : ~ r2_hidden(X4,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl4_4
  <=> ! [X4] : ~ r2_hidden(X4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f201,plain,
    ( ! [X8,X9] :
        ( r2_hidden(sK3(sK1,X8,X9),X9)
        | k3_xboole_0(sK1,X8) = X9 )
    | ~ spl4_4 ),
    inference(resolution,[],[f65,f30])).

fof(f219,plain,
    ( spl4_1
    | spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f218,f64,f44,f44])).

fof(f218,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f52,f65])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f40,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f20])).

% (16316)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f40,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK0))
      | r2_hidden(X3,sK1) ) ),
    inference(superposition,[],[f34,f22])).

fof(f22,plain,(
    k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f195,plain,
    ( ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f193,f23])).

fof(f193,plain,
    ( sK0 = sK1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f170,f55])).

fof(f55,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f54,f24])).

fof(f54,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_2 ),
    inference(duplicate_literal_removal,[],[f53])).

fof(f53,plain,
    ( r1_tarski(sK0,sK1)
    | r1_tarski(sK0,sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f50,f25])).

fof(f50,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(X0,sK1),sK0)
        | r1_tarski(X0,sK1) )
    | ~ spl4_2 ),
    inference(resolution,[],[f48,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl4_2
  <=> ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f170,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f150,f87])).

fof(f87,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,X0,sK1),sK0)
        | sK1 = k3_xboole_0(sK0,X0) )
    | ~ spl4_3 ),
    inference(factoring,[],[f73])).

fof(f73,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK3(X2,X3,sK1),sK0)
        | r2_hidden(sK3(X2,X3,sK1),X2)
        | sK1 = k3_xboole_0(X2,X3) )
    | ~ spl4_3 ),
    inference(resolution,[],[f62,f30])).

fof(f150,plain,
    ( ! [X8] :
        ( ~ r2_hidden(sK3(X8,sK1,sK1),X8)
        | sK1 = k3_xboole_0(X8,sK1) )
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f143,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f143,plain,
    ( ! [X8] :
        ( ~ r2_hidden(sK3(X8,sK1,sK1),sK1)
        | ~ r2_hidden(sK3(X8,sK1,sK1),X8)
        | sK1 = k3_xboole_0(X8,sK1) )
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,
    ( ! [X8] :
        ( ~ r2_hidden(sK3(X8,sK1,sK1),sK1)
        | ~ r2_hidden(sK3(X8,sK1,sK1),X8)
        | sK1 = k3_xboole_0(X8,sK1)
        | sK1 = k3_xboole_0(X8,sK1) )
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f51,f102])).

fof(f102,plain,
    ( ! [X7] :
        ( r2_hidden(sK3(X7,sK1,sK1),sK0)
        | sK1 = k3_xboole_0(X7,sK1) )
    | ~ spl4_3 ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,
    ( ! [X7] :
        ( r2_hidden(sK3(X7,sK1,sK1),sK0)
        | sK1 = k3_xboole_0(X7,sK1)
        | r2_hidden(sK3(X7,sK1,sK1),sK0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f74,f62])).

fof(f74,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK3(X4,X5,sK1),sK0)
        | r2_hidden(sK3(X4,X5,sK1),X5)
        | sK1 = k3_xboole_0(X4,X5) )
    | ~ spl4_3 ),
    inference(resolution,[],[f62,f31])).

fof(f51,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(sK3(X1,X2,sK1),sK0)
        | ~ r2_hidden(sK3(X1,X2,sK1),X2)
        | ~ r2_hidden(sK3(X1,X2,sK1),X1)
        | sK1 = k3_xboole_0(X1,X2) )
    | ~ spl4_2 ),
    inference(resolution,[],[f48,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f67,plain,
    ( spl4_4
    | spl4_3 ),
    inference(avatar_split_clause,[],[f59,f61,f64])).

fof(f59,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,sK1)
      | ~ r2_hidden(X7,sK1)
      | r2_hidden(X6,sK0) ) ),
    inference(resolution,[],[f41,f34])).

fof(f41,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK0))
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(superposition,[],[f35,f22])).

fof(f49,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f42,f47,f44])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f39,f35])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK0))
      | r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f33,f22])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:57:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.49  % (16305)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.49  % (16297)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.49  % (16298)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.49  % (16321)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.49  % (16295)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.49  % (16313)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.50  % (16318)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.50  % (16292)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.50  % (16292)Refutation not found, incomplete strategy% (16292)------------------------------
% 0.22/0.50  % (16292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (16292)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (16292)Memory used [KB]: 1663
% 0.22/0.50  % (16292)Time elapsed: 0.076 s
% 0.22/0.50  % (16292)------------------------------
% 0.22/0.50  % (16292)------------------------------
% 0.22/0.50  % (16318)Refutation not found, incomplete strategy% (16318)------------------------------
% 0.22/0.50  % (16318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (16293)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.50  % (16318)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (16318)Memory used [KB]: 10618
% 0.22/0.50  % (16318)Time elapsed: 0.105 s
% 0.22/0.50  % (16318)------------------------------
% 0.22/0.50  % (16318)------------------------------
% 0.22/0.50  % (16313)Refutation not found, incomplete strategy% (16313)------------------------------
% 0.22/0.50  % (16313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (16310)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.51  % (16313)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (16313)Memory used [KB]: 1663
% 0.22/0.51  % (16313)Time elapsed: 0.104 s
% 0.22/0.51  % (16313)------------------------------
% 0.22/0.51  % (16313)------------------------------
% 0.22/0.51  % (16306)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (16301)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (16301)Refutation not found, incomplete strategy% (16301)------------------------------
% 0.22/0.51  % (16301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (16301)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (16301)Memory used [KB]: 10618
% 0.22/0.51  % (16301)Time elapsed: 0.098 s
% 0.22/0.51  % (16301)------------------------------
% 0.22/0.51  % (16301)------------------------------
% 0.22/0.51  % (16299)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (16308)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.51  % (16296)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (16296)Refutation not found, incomplete strategy% (16296)------------------------------
% 0.22/0.51  % (16296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (16296)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (16296)Memory used [KB]: 6140
% 0.22/0.51  % (16296)Time elapsed: 0.112 s
% 0.22/0.51  % (16296)------------------------------
% 0.22/0.51  % (16296)------------------------------
% 0.22/0.51  % (16312)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.51  % (16319)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.51  % (16311)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.51  % (16312)Refutation not found, incomplete strategy% (16312)------------------------------
% 0.22/0.51  % (16312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (16312)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (16312)Memory used [KB]: 10618
% 0.22/0.51  % (16312)Time elapsed: 0.118 s
% 0.22/0.51  % (16312)------------------------------
% 0.22/0.51  % (16312)------------------------------
% 0.22/0.51  % (16294)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (16320)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.52  % (16309)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.52  % (16294)Refutation not found, incomplete strategy% (16294)------------------------------
% 0.22/0.52  % (16294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (16294)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (16294)Memory used [KB]: 10746
% 0.22/0.52  % (16294)Time elapsed: 0.090 s
% 0.22/0.52  % (16294)------------------------------
% 0.22/0.52  % (16294)------------------------------
% 0.22/0.52  % (16314)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (16309)Refutation not found, incomplete strategy% (16309)------------------------------
% 0.22/0.52  % (16309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (16309)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (16309)Memory used [KB]: 10618
% 0.22/0.52  % (16309)Time elapsed: 0.114 s
% 0.22/0.52  % (16309)------------------------------
% 0.22/0.52  % (16309)------------------------------
% 0.22/0.52  % (16315)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (16317)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.52  % (16302)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (16302)Refutation not found, incomplete strategy% (16302)------------------------------
% 0.22/0.52  % (16302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (16302)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (16302)Memory used [KB]: 10618
% 0.22/0.52  % (16302)Time elapsed: 0.100 s
% 0.22/0.52  % (16302)------------------------------
% 0.22/0.52  % (16302)------------------------------
% 0.22/0.52  % (16304)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (16307)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (16307)Refutation not found, incomplete strategy% (16307)------------------------------
% 0.22/0.52  % (16307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (16307)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (16307)Memory used [KB]: 6140
% 0.22/0.52  % (16307)Time elapsed: 0.003 s
% 0.22/0.52  % (16307)------------------------------
% 0.22/0.52  % (16307)------------------------------
% 0.22/0.52  % (16300)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (16300)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f248,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f49,f67,f195,f219,f227,f247])).
% 0.22/0.53  fof(f247,plain,(
% 0.22/0.53    ~spl4_1 | ~spl4_3),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f246])).
% 0.22/0.53  fof(f246,plain,(
% 0.22/0.53    $false | (~spl4_1 | ~spl4_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f245,f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    sK0 != sK1),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    sK0 != sK1 & k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ? [X0,X1] : (X0 != X1 & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1)) => (sK0 != sK1 & k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f8,plain,(
% 0.22/0.53    ? [X0,X1] : (X0 != X1 & k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : (k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) => X0 = X1)),
% 0.22/0.53    inference(negated_conjecture,[],[f5])).
% 0.22/0.53  fof(f5,conjecture,(
% 0.22/0.53    ! [X0,X1] : (k2_zfmisc_1(X0,X0) = k2_zfmisc_1(X1,X1) => X0 = X1)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_zfmisc_1)).
% 0.22/0.53  fof(f245,plain,(
% 0.22/0.53    sK0 = sK1 | (~spl4_1 | ~spl4_3)),
% 0.22/0.53    inference(resolution,[],[f235,f228])).
% 0.22/0.53  fof(f228,plain,(
% 0.22/0.53    ( ! [X5] : (~r2_hidden(X5,sK1)) ) | (~spl4_1 | ~spl4_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f62,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl4_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    spl4_1 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X5] : (~r2_hidden(X5,sK1) | r2_hidden(X5,sK0)) ) | ~spl4_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    spl4_3 <=> ! [X5] : (~r2_hidden(X5,sK1) | r2_hidden(X5,sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.53  fof(f235,plain,(
% 0.22/0.53    ( ! [X8,X7] : (r2_hidden(sK3(sK0,X7,X8),X8) | sK0 = X8) ) | ~spl4_1),
% 0.22/0.53    inference(backward_demodulation,[],[f224,f234])).
% 0.22/0.53  fof(f234,plain,(
% 0.22/0.53    ( ! [X0] : (sK0 = k3_xboole_0(sK0,X0)) ) | ~spl4_1),
% 0.22/0.53    inference(resolution,[],[f220,f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.53  fof(f220,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(sK0,X0)) ) | ~spl4_1),
% 0.22/0.53    inference(resolution,[],[f45,f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.22/0.53    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.53  fof(f224,plain,(
% 0.22/0.53    ( ! [X8,X7] : (r2_hidden(sK3(sK0,X7,X8),X8) | k3_xboole_0(sK0,X7) = X8) ) | ~spl4_1),
% 0.22/0.53    inference(resolution,[],[f45,f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k3_xboole_0(X0,X1) = X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.53    inference(rectify,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.53    inference(flattening,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.53    inference(nnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.22/0.53  fof(f227,plain,(
% 0.22/0.53    ~spl4_1 | ~spl4_4),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f226])).
% 0.22/0.53  fof(f226,plain,(
% 0.22/0.53    $false | (~spl4_1 | ~spl4_4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f225,f23])).
% 0.22/0.53  fof(f225,plain,(
% 0.22/0.53    sK0 = sK1 | (~spl4_1 | ~spl4_4)),
% 0.22/0.53    inference(resolution,[],[f45,f208])).
% 0.22/0.53  fof(f208,plain,(
% 0.22/0.53    ( ! [X8,X9] : (r2_hidden(sK3(sK1,X8,X9),X9) | sK1 = X9) ) | ~spl4_4),
% 0.22/0.53    inference(backward_demodulation,[],[f201,f207])).
% 0.22/0.53  fof(f207,plain,(
% 0.22/0.53    ( ! [X0] : (sK1 = k3_xboole_0(sK1,X0)) ) | ~spl4_4),
% 0.22/0.53    inference(resolution,[],[f197,f24])).
% 0.22/0.53  fof(f197,plain,(
% 0.22/0.53    ( ! [X1] : (r1_tarski(sK1,X1)) ) | ~spl4_4),
% 0.22/0.53    inference(resolution,[],[f65,f25])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X4] : (~r2_hidden(X4,sK1)) ) | ~spl4_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    spl4_4 <=> ! [X4] : ~r2_hidden(X4,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.53  fof(f201,plain,(
% 0.22/0.53    ( ! [X8,X9] : (r2_hidden(sK3(sK1,X8,X9),X9) | k3_xboole_0(sK1,X8) = X9) ) | ~spl4_4),
% 0.22/0.53    inference(resolution,[],[f65,f30])).
% 0.22/0.53  fof(f219,plain,(
% 0.22/0.53    spl4_1 | spl4_1 | ~spl4_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f218,f64,f44,f44])).
% 0.22/0.53  fof(f218,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r2_hidden(X1,sK0)) ) | ~spl4_4),
% 0.22/0.53    inference(subsumption_resolution,[],[f52,f65])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0) | ~r2_hidden(X1,sK0)) )),
% 0.22/0.53    inference(resolution,[],[f40,f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.53    inference(flattening,[],[f20])).
% 0.22/0.53  % (16316)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.53    inference(nnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(sK0,sK0)) | r2_hidden(X3,sK1)) )),
% 0.22/0.53    inference(superposition,[],[f34,f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK1,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f195,plain,(
% 0.22/0.53    ~spl4_2 | ~spl4_3),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f194])).
% 0.22/0.53  fof(f194,plain,(
% 0.22/0.53    $false | (~spl4_2 | ~spl4_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f193,f23])).
% 0.22/0.53  fof(f193,plain,(
% 0.22/0.53    sK0 = sK1 | (~spl4_2 | ~spl4_3)),
% 0.22/0.53    inference(forward_demodulation,[],[f170,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    sK0 = k3_xboole_0(sK0,sK1) | ~spl4_2),
% 0.22/0.53    inference(resolution,[],[f54,f24])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    r1_tarski(sK0,sK1) | ~spl4_2),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    r1_tarski(sK0,sK1) | r1_tarski(sK0,sK1) | ~spl4_2),
% 0.22/0.53    inference(resolution,[],[f50,f25])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(sK2(X0,sK1),sK0) | r1_tarski(X0,sK1)) ) | ~spl4_2),
% 0.22/0.53    inference(resolution,[],[f48,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl4_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    spl4_2 <=> ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    sK1 = k3_xboole_0(sK0,sK1) | (~spl4_2 | ~spl4_3)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f165])).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    sK1 = k3_xboole_0(sK0,sK1) | sK1 = k3_xboole_0(sK0,sK1) | (~spl4_2 | ~spl4_3)),
% 0.22/0.53    inference(resolution,[],[f150,f87])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK3(sK0,X0,sK1),sK0) | sK1 = k3_xboole_0(sK0,X0)) ) | ~spl4_3),
% 0.22/0.53    inference(factoring,[],[f73])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ( ! [X2,X3] : (r2_hidden(sK3(X2,X3,sK1),sK0) | r2_hidden(sK3(X2,X3,sK1),X2) | sK1 = k3_xboole_0(X2,X3)) ) | ~spl4_3),
% 0.22/0.53    inference(resolution,[],[f62,f30])).
% 0.22/0.53  fof(f150,plain,(
% 0.22/0.53    ( ! [X8] : (~r2_hidden(sK3(X8,sK1,sK1),X8) | sK1 = k3_xboole_0(X8,sK1)) ) | (~spl4_2 | ~spl4_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f143,f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | k3_xboole_0(X0,X1) = X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f143,plain,(
% 0.22/0.53    ( ! [X8] : (~r2_hidden(sK3(X8,sK1,sK1),sK1) | ~r2_hidden(sK3(X8,sK1,sK1),X8) | sK1 = k3_xboole_0(X8,sK1)) ) | (~spl4_2 | ~spl4_3)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f132])).
% 0.22/0.53  fof(f132,plain,(
% 0.22/0.53    ( ! [X8] : (~r2_hidden(sK3(X8,sK1,sK1),sK1) | ~r2_hidden(sK3(X8,sK1,sK1),X8) | sK1 = k3_xboole_0(X8,sK1) | sK1 = k3_xboole_0(X8,sK1)) ) | (~spl4_2 | ~spl4_3)),
% 0.22/0.53    inference(resolution,[],[f51,f102])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    ( ! [X7] : (r2_hidden(sK3(X7,sK1,sK1),sK0) | sK1 = k3_xboole_0(X7,sK1)) ) | ~spl4_3),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f100])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    ( ! [X7] : (r2_hidden(sK3(X7,sK1,sK1),sK0) | sK1 = k3_xboole_0(X7,sK1) | r2_hidden(sK3(X7,sK1,sK1),sK0)) ) | ~spl4_3),
% 0.22/0.53    inference(resolution,[],[f74,f62])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ( ! [X4,X5] : (r2_hidden(sK3(X4,X5,sK1),sK0) | r2_hidden(sK3(X4,X5,sK1),X5) | sK1 = k3_xboole_0(X4,X5)) ) | ~spl4_3),
% 0.22/0.53    inference(resolution,[],[f62,f31])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X2,X1] : (~r2_hidden(sK3(X1,X2,sK1),sK0) | ~r2_hidden(sK3(X1,X2,sK1),X2) | ~r2_hidden(sK3(X1,X2,sK1),X1) | sK1 = k3_xboole_0(X1,X2)) ) | ~spl4_2),
% 0.22/0.53    inference(resolution,[],[f48,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | k3_xboole_0(X0,X1) = X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    spl4_4 | spl4_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f59,f61,f64])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X6,X7] : (~r2_hidden(X6,sK1) | ~r2_hidden(X7,sK1) | r2_hidden(X6,sK0)) )),
% 0.22/0.53    inference(resolution,[],[f41,f34])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK0)) | ~r2_hidden(X5,sK1) | ~r2_hidden(X4,sK1)) )),
% 0.22/0.53    inference(superposition,[],[f35,f22])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    spl4_1 | spl4_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f42,f47,f44])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(X0,sK1) | ~r2_hidden(X1,sK0) | ~r2_hidden(X0,sK0)) )),
% 0.22/0.53    inference(resolution,[],[f39,f35])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK0)) | r2_hidden(X0,sK1)) )),
% 0.22/0.53    inference(superposition,[],[f33,f22])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (16300)------------------------------
% 0.22/0.53  % (16300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (16300)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (16300)Memory used [KB]: 10746
% 0.22/0.53  % (16300)Time elapsed: 0.129 s
% 0.22/0.53  % (16300)------------------------------
% 0.22/0.53  % (16300)------------------------------
% 0.22/0.53  % (16291)Success in time 0.161 s
%------------------------------------------------------------------------------
