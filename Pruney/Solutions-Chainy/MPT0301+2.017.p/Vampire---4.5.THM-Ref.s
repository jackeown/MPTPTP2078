%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 179 expanded)
%              Number of leaves         :   18 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  337 ( 825 expanded)
%              Number of equality atoms :  118 ( 313 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f487,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f97,f98,f164,f204,f464,f475,f486])).

fof(f486,plain,
    ( spl10_3
    | ~ spl10_4 ),
    inference(avatar_contradiction_clause,[],[f485])).

fof(f485,plain,
    ( $false
    | spl10_3
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f482,f96])).

fof(f96,plain,
    ( k1_xboole_0 != sK0
    | spl10_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl10_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f482,plain,
    ( k1_xboole_0 = sK0
    | ~ spl10_4 ),
    inference(resolution,[],[f460,f45])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

% (19469)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f21,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f460,plain,
    ( ! [X6] : ~ r2_hidden(X6,sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f459])).

fof(f459,plain,
    ( spl10_4
  <=> ! [X6] : ~ r2_hidden(X6,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

% (19469)Refutation not found, incomplete strategy% (19469)------------------------------
% (19469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19469)Termination reason: Refutation not found, incomplete strategy

% (19469)Memory used [KB]: 10618
% (19469)Time elapsed: 0.138 s
% (19469)------------------------------
% (19469)------------------------------
fof(f475,plain,
    ( spl10_2
    | ~ spl10_5 ),
    inference(avatar_contradiction_clause,[],[f474])).

fof(f474,plain,
    ( $false
    | spl10_2
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f471,f91])).

fof(f91,plain,
    ( k1_xboole_0 != sK1
    | spl10_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl10_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f471,plain,
    ( k1_xboole_0 = sK1
    | ~ spl10_5 ),
    inference(resolution,[],[f463,f45])).

fof(f463,plain,
    ( ! [X7] : ~ r2_hidden(X7,sK1)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f462])).

fof(f462,plain,
    ( spl10_5
  <=> ! [X7] : ~ r2_hidden(X7,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f464,plain,
    ( spl10_4
    | spl10_5
    | ~ spl10_1 ),
    inference(avatar_split_clause,[],[f457,f85,f462,f459])).

fof(f85,plain,
    ( spl10_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f457,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X7,sK1)
        | ~ r2_hidden(X6,sK0) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f456,f106])).

fof(f106,plain,(
    ! [X3] : ~ r2_hidden(X3,k1_xboole_0) ),
    inference(condensation,[],[f105])).

fof(f105,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | ~ r2_hidden(X3,X2) ) ),
    inference(superposition,[],[f82,f100])).

fof(f100,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f72,f44])).

fof(f44,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f43,f47])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK9(X0,X1,X2),X1)
            | ~ r2_hidden(sK9(X0,X1,X2),X0)
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK9(X0,X1,X2),X1)
              & r2_hidden(sK9(X0,X1,X2),X0) )
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK9(X0,X1,X2),X1)
          | ~ r2_hidden(sK9(X0,X1,X2),X0)
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK9(X0,X1,X2),X1)
            & r2_hidden(sK9(X0,X1,X2),X0) )
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f456,plain,
    ( ! [X6,X7] :
        ( r2_hidden(k4_tarski(X6,X7),k1_xboole_0)
        | ~ r2_hidden(X7,sK1)
        | ~ r2_hidden(X6,sK0) )
    | ~ spl10_1 ),
    inference(superposition,[],[f77,f86])).

fof(f86,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f77,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK4(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( sK4(X0,X1,X2) = k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2))
              & r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
                & r2_hidden(sK8(X0,X1,X8),X1)
                & r2_hidden(sK7(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f30,f33,f32,f31])).

fof(f31,plain,(
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
              ( k4_tarski(X4,X5) != sK4(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK4(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK4(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK4(X0,X1,X2) = k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(sK5(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
        & r2_hidden(sK8(X0,X1,X8),X1)
        & r2_hidden(sK7(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

% (19474)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f204,plain,
    ( spl10_1
    | ~ spl10_3 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl10_1
    | ~ spl10_3 ),
    inference(trivial_inequality_removal,[],[f202])).

fof(f202,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl10_1
    | ~ spl10_3 ),
    inference(superposition,[],[f165,f197])).

fof(f197,plain,(
    ! [X12] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X12) ),
    inference(resolution,[],[f191,f45])).

fof(f191,plain,(
    ! [X17,X16] : ~ r2_hidden(X16,k2_zfmisc_1(k1_xboole_0,X17)) ),
    inference(resolution,[],[f80,f106])).

fof(f80,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f165,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl10_1
    | ~ spl10_3 ),
    inference(forward_demodulation,[],[f87,f95])).

fof(f95,plain,
    ( k1_xboole_0 = sK0
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f87,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f164,plain,
    ( spl10_1
    | ~ spl10_2 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl10_1
    | ~ spl10_2 ),
    inference(trivial_inequality_removal,[],[f162])).

fof(f162,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl10_1
    | ~ spl10_2 ),
    inference(superposition,[],[f99,f155])).

fof(f155,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f152,f45])).

fof(f152,plain,(
    ! [X4,X5] : ~ r2_hidden(X4,k2_zfmisc_1(X5,k1_xboole_0)) ),
    inference(resolution,[],[f79,f106])).

fof(f79,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK8(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK8(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f99,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl10_1
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f87,f90])).

fof(f90,plain,
    ( k1_xboole_0 = sK1
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f98,plain,
    ( spl10_1
    | spl10_3
    | spl10_2 ),
    inference(avatar_split_clause,[],[f40,f89,f94,f85])).

fof(f40,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ( k1_xboole_0 != sK1
        & k1_xboole_0 != sK0 )
      | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )
   => ( ( ( k1_xboole_0 != sK1
          & k1_xboole_0 != sK0 )
        | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f97,plain,
    ( ~ spl10_1
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f41,f94,f85])).

fof(f41,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f92,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f42,f89,f85])).

fof(f42,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:25:41 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (19468)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (19462)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (19467)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (19485)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (19470)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (19478)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (19461)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (19461)Refutation not found, incomplete strategy% (19461)------------------------------
% 0.22/0.55  % (19461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (19461)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (19461)Memory used [KB]: 10746
% 0.22/0.55  % (19461)Time elapsed: 0.135 s
% 0.22/0.55  % (19461)------------------------------
% 0.22/0.55  % (19461)------------------------------
% 0.22/0.55  % (19476)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (19470)Refutation not found, incomplete strategy% (19470)------------------------------
% 0.22/0.55  % (19470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (19460)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (19470)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (19470)Memory used [KB]: 10618
% 0.22/0.55  % (19470)Time elapsed: 0.130 s
% 0.22/0.55  % (19470)------------------------------
% 0.22/0.55  % (19470)------------------------------
% 0.22/0.55  % (19467)Refutation not found, incomplete strategy% (19467)------------------------------
% 0.22/0.55  % (19467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (19467)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (19467)Memory used [KB]: 10746
% 0.22/0.55  % (19467)Time elapsed: 0.131 s
% 0.22/0.55  % (19467)------------------------------
% 0.22/0.55  % (19467)------------------------------
% 0.22/0.56  % (19471)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (19463)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.56  % (19479)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (19462)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.57  % (19479)Refutation not found, incomplete strategy% (19479)------------------------------
% 0.22/0.57  % (19479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (19479)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (19479)Memory used [KB]: 10746
% 0.22/0.57  % (19479)Time elapsed: 0.160 s
% 0.22/0.57  % (19479)------------------------------
% 0.22/0.57  % (19479)------------------------------
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f487,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(avatar_sat_refutation,[],[f92,f97,f98,f164,f204,f464,f475,f486])).
% 0.22/0.57  fof(f486,plain,(
% 0.22/0.57    spl10_3 | ~spl10_4),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f485])).
% 0.22/0.57  fof(f485,plain,(
% 0.22/0.57    $false | (spl10_3 | ~spl10_4)),
% 0.22/0.57    inference(subsumption_resolution,[],[f482,f96])).
% 0.22/0.57  fof(f96,plain,(
% 0.22/0.57    k1_xboole_0 != sK0 | spl10_3),
% 0.22/0.57    inference(avatar_component_clause,[],[f94])).
% 0.22/0.57  fof(f94,plain,(
% 0.22/0.57    spl10_3 <=> k1_xboole_0 = sK0),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.22/0.57  fof(f482,plain,(
% 0.22/0.57    k1_xboole_0 = sK0 | ~spl10_4),
% 0.22/0.57    inference(resolution,[],[f460,f45])).
% 0.22/0.57  fof(f45,plain,(
% 0.22/0.57    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f21])).
% 0.22/0.57  % (19469)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f20])).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.57    inference(ennf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.57  fof(f460,plain,(
% 0.22/0.57    ( ! [X6] : (~r2_hidden(X6,sK0)) ) | ~spl10_4),
% 0.22/0.57    inference(avatar_component_clause,[],[f459])).
% 0.22/0.57  fof(f459,plain,(
% 0.22/0.57    spl10_4 <=> ! [X6] : ~r2_hidden(X6,sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.22/0.57  % (19469)Refutation not found, incomplete strategy% (19469)------------------------------
% 0.22/0.57  % (19469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (19469)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (19469)Memory used [KB]: 10618
% 0.22/0.57  % (19469)Time elapsed: 0.138 s
% 0.22/0.57  % (19469)------------------------------
% 0.22/0.57  % (19469)------------------------------
% 0.22/0.57  fof(f475,plain,(
% 0.22/0.57    spl10_2 | ~spl10_5),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f474])).
% 0.22/0.57  fof(f474,plain,(
% 0.22/0.57    $false | (spl10_2 | ~spl10_5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f471,f91])).
% 0.22/0.57  fof(f91,plain,(
% 0.22/0.57    k1_xboole_0 != sK1 | spl10_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f89])).
% 0.22/0.57  fof(f89,plain,(
% 0.22/0.57    spl10_2 <=> k1_xboole_0 = sK1),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.22/0.57  fof(f471,plain,(
% 0.22/0.57    k1_xboole_0 = sK1 | ~spl10_5),
% 0.22/0.57    inference(resolution,[],[f463,f45])).
% 0.22/0.57  fof(f463,plain,(
% 0.22/0.57    ( ! [X7] : (~r2_hidden(X7,sK1)) ) | ~spl10_5),
% 0.22/0.57    inference(avatar_component_clause,[],[f462])).
% 0.22/0.57  fof(f462,plain,(
% 0.22/0.57    spl10_5 <=> ! [X7] : ~r2_hidden(X7,sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.22/0.57  fof(f464,plain,(
% 0.22/0.57    spl10_4 | spl10_5 | ~spl10_1),
% 0.22/0.57    inference(avatar_split_clause,[],[f457,f85,f462,f459])).
% 0.22/0.57  fof(f85,plain,(
% 0.22/0.57    spl10_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.22/0.57  fof(f457,plain,(
% 0.22/0.57    ( ! [X6,X7] : (~r2_hidden(X7,sK1) | ~r2_hidden(X6,sK0)) ) | ~spl10_1),
% 0.22/0.57    inference(subsumption_resolution,[],[f456,f106])).
% 0.22/0.57  fof(f106,plain,(
% 0.22/0.57    ( ! [X3] : (~r2_hidden(X3,k1_xboole_0)) )),
% 0.22/0.57    inference(condensation,[],[f105])).
% 0.22/0.57  fof(f105,plain,(
% 0.22/0.57    ( ! [X2,X3] : (~r2_hidden(X3,k1_xboole_0) | ~r2_hidden(X3,X2)) )),
% 0.22/0.57    inference(superposition,[],[f82,f100])).
% 0.22/0.57  fof(f100,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.57    inference(forward_demodulation,[],[f72,f44])).
% 0.22/0.57  fof(f44,plain,(
% 0.22/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.57  fof(f72,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.57    inference(definition_unfolding,[],[f43,f47])).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.57  fof(f82,plain,(
% 0.22/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.22/0.57    inference(equality_resolution,[],[f67])).
% 0.22/0.57  fof(f67,plain,(
% 0.22/0.57    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f39])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK9(X0,X1,X2),X1) | ~r2_hidden(sK9(X0,X1,X2),X0) | ~r2_hidden(sK9(X0,X1,X2),X2)) & ((~r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(sK9(X0,X1,X2),X0)) | r2_hidden(sK9(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f37,f38])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK9(X0,X1,X2),X1) | ~r2_hidden(sK9(X0,X1,X2),X0) | ~r2_hidden(sK9(X0,X1,X2),X2)) & ((~r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(sK9(X0,X1,X2),X0)) | r2_hidden(sK9(X0,X1,X2),X2))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f37,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.57    inference(rectify,[],[f36])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.57    inference(flattening,[],[f35])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.57    inference(nnf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.57  fof(f456,plain,(
% 0.22/0.57    ( ! [X6,X7] : (r2_hidden(k4_tarski(X6,X7),k1_xboole_0) | ~r2_hidden(X7,sK1) | ~r2_hidden(X6,sK0)) ) | ~spl10_1),
% 0.22/0.57    inference(superposition,[],[f77,f86])).
% 0.22/0.57  fof(f86,plain,(
% 0.22/0.57    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl10_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f85])).
% 0.22/0.57  fof(f77,plain,(
% 0.22/0.57    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 0.22/0.57    inference(equality_resolution,[],[f76])).
% 0.22/0.57  fof(f76,plain,(
% 0.22/0.57    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.57    inference(equality_resolution,[],[f61])).
% 0.22/0.57  fof(f61,plain,(
% 0.22/0.57    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f34])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK4(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((sK4(X0,X1,X2) = k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8 & r2_hidden(sK8(X0,X1,X8),X1) & r2_hidden(sK7(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f30,f33,f32,f31])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK4(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK4(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK4(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK4(X0,X1,X2) = k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8 & r2_hidden(sK8(X0,X1,X8),X1) & r2_hidden(sK7(X0,X1,X8),X0)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  % (19474)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.22/0.57    inference(rectify,[],[f29])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.22/0.57    inference(nnf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.22/0.57  fof(f204,plain,(
% 0.22/0.57    spl10_1 | ~spl10_3),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f203])).
% 0.22/0.57  fof(f203,plain,(
% 0.22/0.57    $false | (spl10_1 | ~spl10_3)),
% 0.22/0.57    inference(trivial_inequality_removal,[],[f202])).
% 0.22/0.57  fof(f202,plain,(
% 0.22/0.57    k1_xboole_0 != k1_xboole_0 | (spl10_1 | ~spl10_3)),
% 0.22/0.57    inference(superposition,[],[f165,f197])).
% 0.22/0.57  fof(f197,plain,(
% 0.22/0.57    ( ! [X12] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X12)) )),
% 0.22/0.57    inference(resolution,[],[f191,f45])).
% 0.22/0.57  fof(f191,plain,(
% 0.22/0.57    ( ! [X17,X16] : (~r2_hidden(X16,k2_zfmisc_1(k1_xboole_0,X17))) )),
% 0.22/0.57    inference(resolution,[],[f80,f106])).
% 0.22/0.57  fof(f80,plain,(
% 0.22/0.57    ( ! [X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.57    inference(equality_resolution,[],[f58])).
% 0.22/0.57  fof(f58,plain,(
% 0.22/0.57    ( ! [X2,X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f34])).
% 0.22/0.57  fof(f165,plain,(
% 0.22/0.57    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | (spl10_1 | ~spl10_3)),
% 0.22/0.57    inference(forward_demodulation,[],[f87,f95])).
% 0.22/0.57  fof(f95,plain,(
% 0.22/0.57    k1_xboole_0 = sK0 | ~spl10_3),
% 0.22/0.57    inference(avatar_component_clause,[],[f94])).
% 0.22/0.57  fof(f87,plain,(
% 0.22/0.57    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | spl10_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f85])).
% 0.22/0.57  fof(f164,plain,(
% 0.22/0.57    spl10_1 | ~spl10_2),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f163])).
% 0.22/0.57  fof(f163,plain,(
% 0.22/0.57    $false | (spl10_1 | ~spl10_2)),
% 0.22/0.57    inference(trivial_inequality_removal,[],[f162])).
% 0.22/0.57  fof(f162,plain,(
% 0.22/0.57    k1_xboole_0 != k1_xboole_0 | (spl10_1 | ~spl10_2)),
% 0.22/0.57    inference(superposition,[],[f99,f155])).
% 0.22/0.57  fof(f155,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.57    inference(resolution,[],[f152,f45])).
% 0.22/0.57  fof(f152,plain,(
% 0.22/0.57    ( ! [X4,X5] : (~r2_hidden(X4,k2_zfmisc_1(X5,k1_xboole_0))) )),
% 0.22/0.57    inference(resolution,[],[f79,f106])).
% 0.22/0.57  fof(f79,plain,(
% 0.22/0.57    ( ! [X0,X8,X1] : (r2_hidden(sK8(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.57    inference(equality_resolution,[],[f59])).
% 0.22/0.57  fof(f59,plain,(
% 0.22/0.57    ( ! [X2,X0,X8,X1] : (r2_hidden(sK8(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f34])).
% 0.22/0.57  fof(f99,plain,(
% 0.22/0.57    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | (spl10_1 | ~spl10_2)),
% 0.22/0.57    inference(forward_demodulation,[],[f87,f90])).
% 0.22/0.57  fof(f90,plain,(
% 0.22/0.57    k1_xboole_0 = sK1 | ~spl10_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f89])).
% 0.22/0.57  fof(f98,plain,(
% 0.22/0.57    spl10_1 | spl10_3 | spl10_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f40,f89,f94,f85])).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f17,plain,(
% 0.22/0.57    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.22/0.57    inference(flattening,[],[f16])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.22/0.57    inference(nnf_transformation,[],[f14])).
% 0.22/0.57  fof(f14,plain,(
% 0.22/0.57    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f12])).
% 0.22/0.57  fof(f12,negated_conjecture,(
% 0.22/0.57    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.57    inference(negated_conjecture,[],[f11])).
% 0.22/0.57  fof(f11,conjecture,(
% 0.22/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.57  fof(f97,plain,(
% 0.22/0.57    ~spl10_1 | ~spl10_3),
% 0.22/0.57    inference(avatar_split_clause,[],[f41,f94,f85])).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f92,plain,(
% 0.22/0.57    ~spl10_1 | ~spl10_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f42,f89,f85])).
% 0.22/0.57  fof(f42,plain,(
% 0.22/0.57    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (19462)------------------------------
% 0.22/0.57  % (19462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (19462)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (19462)Memory used [KB]: 11129
% 0.22/0.57  % (19462)Time elapsed: 0.119 s
% 0.22/0.57  % (19462)------------------------------
% 0.22/0.57  % (19462)------------------------------
% 0.22/0.57  % (19458)Success in time 0.208 s
%------------------------------------------------------------------------------
