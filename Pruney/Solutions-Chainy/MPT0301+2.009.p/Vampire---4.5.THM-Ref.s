%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:53 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 258 expanded)
%              Number of leaves         :   10 (  76 expanded)
%              Depth                    :   30
%              Number of atoms          :  241 (1279 expanded)
%              Number of equality atoms :  129 ( 691 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f449,plain,(
    $false ),
    inference(subsumption_resolution,[],[f439,f58])).

fof(f58,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

% (10312)Refutation not found, incomplete strategy% (10312)------------------------------
% (10312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f439,plain,(
    k1_tarski(sK6(k1_xboole_0,sK1,k1_xboole_0)) != k4_xboole_0(k1_tarski(sK6(k1_xboole_0,sK1,k1_xboole_0)),k1_xboole_0) ),
    inference(resolution,[],[f436,f75])).

% (10312)Termination reason: Refutation not found, incomplete strategy

% (10312)Memory used [KB]: 1791
% (10312)Time elapsed: 0.125 s
% (10312)------------------------------
% (10312)------------------------------
fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f436,plain,(
    r2_hidden(sK6(k1_xboole_0,sK1,k1_xboole_0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f427,f58])).

fof(f427,plain,
    ( r2_hidden(sK6(k1_xboole_0,sK1,k1_xboole_0),k1_xboole_0)
    | k1_tarski(sK7(k1_xboole_0,sK1,k1_xboole_0)) != k4_xboole_0(k1_tarski(sK7(k1_xboole_0,sK1,k1_xboole_0)),k1_xboole_0) ),
    inference(resolution,[],[f425,f75])).

fof(f425,plain,
    ( r2_hidden(sK7(k1_xboole_0,sK1,k1_xboole_0),k1_xboole_0)
    | r2_hidden(sK6(k1_xboole_0,sK1,k1_xboole_0),k1_xboole_0) ),
    inference(equality_resolution,[],[f399])).

fof(f399,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r2_hidden(sK7(k1_xboole_0,sK1,X0),k1_xboole_0)
      | r2_hidden(sK6(k1_xboole_0,sK1,X0),X0) ) ),
    inference(forward_demodulation,[],[f398,f371])).

fof(f371,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f359,f58])).

fof(f359,plain,
    ( k1_xboole_0 = sK0
    | k1_tarski(sK6(sK0,k1_xboole_0,k1_xboole_0)) != k4_xboole_0(k1_tarski(sK6(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(resolution,[],[f354,f75])).

fof(f354,plain,
    ( r2_hidden(sK6(sK0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f343,f58])).

fof(f343,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK6(sK0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k1_tarski(sK8(sK0,k1_xboole_0,k1_xboole_0)) != k4_xboole_0(k1_tarski(sK8(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(resolution,[],[f339,f75])).

fof(f339,plain,
    ( r2_hidden(sK8(sK0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = sK0
    | r2_hidden(sK6(sK0,k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(equality_resolution,[],[f195])).

fof(f195,plain,(
    ! [X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = sK0
      | r2_hidden(sK8(sK0,k1_xboole_0,X1),k1_xboole_0)
      | r2_hidden(sK6(sK0,k1_xboole_0,X1),X1) ) ),
    inference(superposition,[],[f192,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK8(X0,X1,X2),X1)
      | r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK6(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( sK6(X0,X1,X2) = k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2))
              & r2_hidden(sK8(X0,X1,X2),X1)
              & r2_hidden(sK7(X0,X1,X2),X0) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK9(X0,X1,X8),sK10(X0,X1,X8)) = X8
                & r2_hidden(sK10(X0,X1,X8),X1)
                & r2_hidden(sK9(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f46,f49,f48,f47])).

fof(f47,plain,(
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
              ( k4_tarski(X4,X5) != sK6(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK6(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK6(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK6(X0,X1,X2) = k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2))
        & r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(sK7(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK9(X0,X1,X8),sK10(X0,X1,X8)) = X8
        & r2_hidden(sK10(X0,X1,X8),X1)
        & r2_hidden(sK9(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f192,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f188])).

fof(f188,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f55,f185])).

fof(f185,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f173])).

fof(f173,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f167,f60])).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

% (10294)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f167,plain,(
    ! [X13] :
      ( ~ r2_hidden(X13,sK1)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1 ) ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,(
    ! [X13] :
      ( ~ r2_hidden(X13,sK1)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f149,f60])).

fof(f149,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,sK0)
      | ~ r2_hidden(X3,sK1)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f138,f58])).

fof(f138,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(X4,sK0)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_tarski(k4_tarski(X4,X3)) != k4_xboole_0(k1_tarski(k4_tarski(X4,X3)),k1_xboole_0) ) ),
    inference(resolution,[],[f117,f75])).

fof(f117,plain,(
    ! [X6,X7] :
      ( r2_hidden(k4_tarski(X6,X7),k1_xboole_0)
      | ~ r2_hidden(X7,sK1)
      | ~ r2_hidden(X6,sK0)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f95,f53])).

fof(f53,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ( k1_xboole_0 != sK1
        & k1_xboole_0 != sK0 )
      | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).

fof(f29,plain,
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

fof(f28,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f95,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f55,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f398,plain,(
    ! [X0] :
      ( r2_hidden(sK7(k1_xboole_0,sK1,X0),k1_xboole_0)
      | k1_xboole_0 != X0
      | r2_hidden(sK6(sK0,sK1,X0),X0) ) ),
    inference(forward_demodulation,[],[f395,f371])).

fof(f395,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r2_hidden(sK7(sK0,sK1,X0),sK0)
      | r2_hidden(sK6(sK0,sK1,X0),X0) ) ),
    inference(trivial_inequality_removal,[],[f374])).

fof(f374,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 != X0
      | r2_hidden(sK7(sK0,sK1,X0),sK0)
      | r2_hidden(sK6(sK0,sK1,X0),X0) ) ),
    inference(backward_demodulation,[],[f99,f371])).

fof(f99,plain,(
    ! [X0] :
      ( k1_xboole_0 != sK0
      | k1_xboole_0 != X0
      | r2_hidden(sK7(sK0,sK1,X0),sK0)
      | r2_hidden(sK6(sK0,sK1,X0),X0) ) ),
    inference(superposition,[],[f54,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X2
      | r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f54,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:06:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.50  % (10291)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.52  % (10303)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.52  % (10297)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.52  % (10299)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.52  % (10311)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.52  % (10291)Refutation not found, incomplete strategy% (10291)------------------------------
% 0.19/0.52  % (10291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (10291)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (10291)Memory used [KB]: 1663
% 0.19/0.52  % (10291)Time elapsed: 0.111 s
% 0.19/0.52  % (10291)------------------------------
% 0.19/0.52  % (10291)------------------------------
% 0.19/0.52  % (10304)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.52  % (10311)Refutation not found, incomplete strategy% (10311)------------------------------
% 0.19/0.52  % (10311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (10321)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.52  % (10305)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.52  % (10314)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.52  % (10299)Refutation not found, incomplete strategy% (10299)------------------------------
% 0.19/0.52  % (10299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (10301)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.52  % (10299)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (10299)Memory used [KB]: 10746
% 0.19/0.52  % (10299)Time elapsed: 0.124 s
% 0.19/0.52  % (10299)------------------------------
% 0.19/0.52  % (10299)------------------------------
% 0.19/0.52  % (10296)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.53  % (10307)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.53  % (10314)Refutation found. Thanks to Tanya!
% 0.19/0.53  % SZS status Theorem for theBenchmark
% 0.19/0.53  % (10311)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (10311)Memory used [KB]: 10746
% 0.19/0.53  % (10311)Time elapsed: 0.109 s
% 0.19/0.53  % (10311)------------------------------
% 0.19/0.53  % (10311)------------------------------
% 0.19/0.53  % (10298)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.53  % (10300)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.53  % (10313)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.53  % (10320)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.54  % (10295)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.54  % (10306)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.54  % (10292)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.54  % (10302)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.54  % (10301)Refutation not found, incomplete strategy% (10301)------------------------------
% 0.19/0.54  % (10301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (10301)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (10301)Memory used [KB]: 10618
% 0.19/0.54  % (10301)Time elapsed: 0.145 s
% 0.19/0.54  % (10301)------------------------------
% 0.19/0.54  % (10301)------------------------------
% 0.19/0.54  % (10293)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.55  % (10302)Refutation not found, incomplete strategy% (10302)------------------------------
% 0.19/0.55  % (10302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (10302)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (10302)Memory used [KB]: 10618
% 0.19/0.55  % (10302)Time elapsed: 0.144 s
% 0.19/0.55  % (10302)------------------------------
% 0.19/0.55  % (10302)------------------------------
% 0.19/0.55  % (10312)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.55  % (10293)Refutation not found, incomplete strategy% (10293)------------------------------
% 0.19/0.55  % (10293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (10293)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (10293)Memory used [KB]: 10746
% 0.19/0.55  % (10293)Time elapsed: 0.146 s
% 0.19/0.55  % (10293)------------------------------
% 0.19/0.55  % (10293)------------------------------
% 0.19/0.55  % SZS output start Proof for theBenchmark
% 0.19/0.55  fof(f449,plain,(
% 0.19/0.55    $false),
% 0.19/0.55    inference(subsumption_resolution,[],[f439,f58])).
% 0.19/0.55  fof(f58,plain,(
% 0.19/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.55    inference(cnf_transformation,[],[f5])).
% 0.19/0.55  fof(f5,axiom,(
% 0.19/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.19/0.55  % (10312)Refutation not found, incomplete strategy% (10312)------------------------------
% 0.19/0.55  % (10312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  fof(f439,plain,(
% 0.19/0.55    k1_tarski(sK6(k1_xboole_0,sK1,k1_xboole_0)) != k4_xboole_0(k1_tarski(sK6(k1_xboole_0,sK1,k1_xboole_0)),k1_xboole_0)),
% 0.19/0.55    inference(resolution,[],[f436,f75])).
% 0.19/0.55  % (10312)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (10312)Memory used [KB]: 1791
% 0.19/0.55  % (10312)Time elapsed: 0.125 s
% 0.19/0.55  % (10312)------------------------------
% 0.19/0.55  % (10312)------------------------------
% 0.19/0.55  fof(f75,plain,(
% 0.19/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f43])).
% 0.19/0.55  fof(f43,plain,(
% 0.19/0.55    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 0.19/0.55    inference(nnf_transformation,[],[f16])).
% 0.19/0.55  fof(f16,axiom,(
% 0.19/0.55    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 0.19/0.55  fof(f436,plain,(
% 0.19/0.55    r2_hidden(sK6(k1_xboole_0,sK1,k1_xboole_0),k1_xboole_0)),
% 0.19/0.55    inference(subsumption_resolution,[],[f427,f58])).
% 0.19/0.55  fof(f427,plain,(
% 0.19/0.55    r2_hidden(sK6(k1_xboole_0,sK1,k1_xboole_0),k1_xboole_0) | k1_tarski(sK7(k1_xboole_0,sK1,k1_xboole_0)) != k4_xboole_0(k1_tarski(sK7(k1_xboole_0,sK1,k1_xboole_0)),k1_xboole_0)),
% 0.19/0.55    inference(resolution,[],[f425,f75])).
% 0.19/0.55  fof(f425,plain,(
% 0.19/0.55    r2_hidden(sK7(k1_xboole_0,sK1,k1_xboole_0),k1_xboole_0) | r2_hidden(sK6(k1_xboole_0,sK1,k1_xboole_0),k1_xboole_0)),
% 0.19/0.55    inference(equality_resolution,[],[f399])).
% 0.19/0.55  fof(f399,plain,(
% 0.19/0.55    ( ! [X0] : (k1_xboole_0 != X0 | r2_hidden(sK7(k1_xboole_0,sK1,X0),k1_xboole_0) | r2_hidden(sK6(k1_xboole_0,sK1,X0),X0)) )),
% 0.19/0.55    inference(forward_demodulation,[],[f398,f371])).
% 0.19/0.55  fof(f371,plain,(
% 0.19/0.55    k1_xboole_0 = sK0),
% 0.19/0.55    inference(subsumption_resolution,[],[f359,f58])).
% 0.19/0.55  fof(f359,plain,(
% 0.19/0.55    k1_xboole_0 = sK0 | k1_tarski(sK6(sK0,k1_xboole_0,k1_xboole_0)) != k4_xboole_0(k1_tarski(sK6(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 0.19/0.55    inference(resolution,[],[f354,f75])).
% 0.19/0.55  fof(f354,plain,(
% 0.19/0.55    r2_hidden(sK6(sK0,k1_xboole_0,k1_xboole_0),k1_xboole_0) | k1_xboole_0 = sK0),
% 0.19/0.55    inference(subsumption_resolution,[],[f343,f58])).
% 0.19/0.55  fof(f343,plain,(
% 0.19/0.55    k1_xboole_0 = sK0 | r2_hidden(sK6(sK0,k1_xboole_0,k1_xboole_0),k1_xboole_0) | k1_tarski(sK8(sK0,k1_xboole_0,k1_xboole_0)) != k4_xboole_0(k1_tarski(sK8(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 0.19/0.55    inference(resolution,[],[f339,f75])).
% 0.19/0.55  fof(f339,plain,(
% 0.19/0.55    r2_hidden(sK8(sK0,k1_xboole_0,k1_xboole_0),k1_xboole_0) | k1_xboole_0 = sK0 | r2_hidden(sK6(sK0,k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 0.19/0.55    inference(equality_resolution,[],[f195])).
% 0.19/0.55  fof(f195,plain,(
% 0.19/0.55    ( ! [X1] : (k1_xboole_0 != X1 | k1_xboole_0 = sK0 | r2_hidden(sK8(sK0,k1_xboole_0,X1),k1_xboole_0) | r2_hidden(sK6(sK0,k1_xboole_0,X1),X1)) )),
% 0.19/0.55    inference(superposition,[],[f192,f84])).
% 0.19/0.55  fof(f84,plain,(
% 0.19/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK8(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f50])).
% 0.19/0.55  fof(f50,plain,(
% 0.19/0.55    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK6(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((sK6(X0,X1,X2) = k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK9(X0,X1,X8),sK10(X0,X1,X8)) = X8 & r2_hidden(sK10(X0,X1,X8),X1) & r2_hidden(sK9(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.19/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f46,f49,f48,f47])).
% 0.19/0.55  fof(f47,plain,(
% 0.19/0.55    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK6(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK6(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.19/0.55    introduced(choice_axiom,[])).
% 0.19/0.55  fof(f48,plain,(
% 0.19/0.55    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK6(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK6(X0,X1,X2) = k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X0)))),
% 0.19/0.55    introduced(choice_axiom,[])).
% 0.19/0.55  fof(f49,plain,(
% 0.19/0.55    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK9(X0,X1,X8),sK10(X0,X1,X8)) = X8 & r2_hidden(sK10(X0,X1,X8),X1) & r2_hidden(sK9(X0,X1,X8),X0)))),
% 0.19/0.55    introduced(choice_axiom,[])).
% 0.19/0.55  fof(f46,plain,(
% 0.19/0.55    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.19/0.55    inference(rectify,[],[f45])).
% 0.19/0.55  fof(f45,plain,(
% 0.19/0.55    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.19/0.55    inference(nnf_transformation,[],[f12])).
% 0.19/0.55  fof(f12,axiom,(
% 0.19/0.55    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.19/0.55  fof(f192,plain,(
% 0.19/0.55    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 0.19/0.55    inference(trivial_inequality_removal,[],[f188])).
% 0.19/0.55  fof(f188,plain,(
% 0.19/0.55    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 0.19/0.55    inference(superposition,[],[f55,f185])).
% 0.19/0.55  fof(f185,plain,(
% 0.19/0.55    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.19/0.55    inference(duplicate_literal_removal,[],[f173])).
% 0.19/0.55  fof(f173,plain,(
% 0.19/0.55    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.19/0.55    inference(resolution,[],[f167,f60])).
% 0.19/0.55  fof(f60,plain,(
% 0.19/0.55    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.19/0.55    inference(cnf_transformation,[],[f32])).
% 0.19/0.55  % (10294)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.55  fof(f32,plain,(
% 0.19/0.55    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.19/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f31])).
% 0.19/0.55  fof(f31,plain,(
% 0.19/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.19/0.55    introduced(choice_axiom,[])).
% 0.19/0.55  fof(f22,plain,(
% 0.19/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.19/0.55    inference(ennf_transformation,[],[f3])).
% 0.19/0.55  fof(f3,axiom,(
% 0.19/0.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.19/0.55  fof(f167,plain,(
% 0.19/0.55    ( ! [X13] : (~r2_hidden(X13,sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1) )),
% 0.19/0.55    inference(duplicate_literal_removal,[],[f155])).
% 0.19/0.55  fof(f155,plain,(
% 0.19/0.55    ( ! [X13] : (~r2_hidden(X13,sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 0.19/0.55    inference(resolution,[],[f149,f60])).
% 0.19/0.55  fof(f149,plain,(
% 0.19/0.55    ( ! [X4,X3] : (~r2_hidden(X4,sK0) | ~r2_hidden(X3,sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1) )),
% 0.19/0.55    inference(subsumption_resolution,[],[f138,f58])).
% 0.19/0.55  fof(f138,plain,(
% 0.19/0.55    ( ! [X4,X3] : (~r2_hidden(X3,sK1) | ~r2_hidden(X4,sK0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_tarski(k4_tarski(X4,X3)) != k4_xboole_0(k1_tarski(k4_tarski(X4,X3)),k1_xboole_0)) )),
% 0.19/0.55    inference(resolution,[],[f117,f75])).
% 0.19/0.55  fof(f117,plain,(
% 0.19/0.55    ( ! [X6,X7] : (r2_hidden(k4_tarski(X6,X7),k1_xboole_0) | ~r2_hidden(X7,sK1) | ~r2_hidden(X6,sK0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1) )),
% 0.19/0.55    inference(superposition,[],[f95,f53])).
% 0.19/0.55  fof(f53,plain,(
% 0.19/0.55    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1),
% 0.19/0.55    inference(cnf_transformation,[],[f30])).
% 0.19/0.55  fof(f30,plain,(
% 0.19/0.55    ((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1))),
% 0.19/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f29])).
% 0.19/0.55  fof(f29,plain,(
% 0.19/0.55    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK1 & k1_xboole_0 != sK0) | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)) & (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.55    introduced(choice_axiom,[])).
% 0.19/0.55  fof(f28,plain,(
% 0.19/0.55    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.19/0.55    inference(flattening,[],[f27])).
% 0.19/0.55  fof(f27,plain,(
% 0.19/0.55    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.19/0.55    inference(nnf_transformation,[],[f21])).
% 0.19/0.55  fof(f21,plain,(
% 0.19/0.55    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.55    inference(ennf_transformation,[],[f19])).
% 0.19/0.55  fof(f19,negated_conjecture,(
% 0.19/0.55    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.55    inference(negated_conjecture,[],[f18])).
% 0.19/0.55  fof(f18,conjecture,(
% 0.19/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.55  fof(f95,plain,(
% 0.19/0.55    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 0.19/0.55    inference(equality_resolution,[],[f94])).
% 0.19/0.55  fof(f94,plain,(
% 0.19/0.55    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.19/0.55    inference(equality_resolution,[],[f82])).
% 0.19/0.55  fof(f82,plain,(
% 0.19/0.55    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.19/0.55    inference(cnf_transformation,[],[f50])).
% 0.19/0.55  fof(f55,plain,(
% 0.19/0.55    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 != sK1),
% 0.19/0.55    inference(cnf_transformation,[],[f30])).
% 0.19/0.55  fof(f398,plain,(
% 0.19/0.55    ( ! [X0] : (r2_hidden(sK7(k1_xboole_0,sK1,X0),k1_xboole_0) | k1_xboole_0 != X0 | r2_hidden(sK6(sK0,sK1,X0),X0)) )),
% 0.19/0.55    inference(forward_demodulation,[],[f395,f371])).
% 0.19/0.55  fof(f395,plain,(
% 0.19/0.55    ( ! [X0] : (k1_xboole_0 != X0 | r2_hidden(sK7(sK0,sK1,X0),sK0) | r2_hidden(sK6(sK0,sK1,X0),X0)) )),
% 0.19/0.55    inference(trivial_inequality_removal,[],[f374])).
% 0.19/0.55  fof(f374,plain,(
% 0.19/0.55    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != X0 | r2_hidden(sK7(sK0,sK1,X0),sK0) | r2_hidden(sK6(sK0,sK1,X0),X0)) )),
% 0.19/0.55    inference(backward_demodulation,[],[f99,f371])).
% 0.19/0.55  fof(f99,plain,(
% 0.19/0.55    ( ! [X0] : (k1_xboole_0 != sK0 | k1_xboole_0 != X0 | r2_hidden(sK7(sK0,sK1,X0),sK0) | r2_hidden(sK6(sK0,sK1,X0),X0)) )),
% 0.19/0.55    inference(superposition,[],[f54,f83])).
% 0.19/0.55  fof(f83,plain,(
% 0.19/0.55    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,X1) = X2 | r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f50])).
% 0.19/0.55  fof(f54,plain,(
% 0.19/0.55    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 != sK0),
% 0.19/0.55    inference(cnf_transformation,[],[f30])).
% 0.19/0.55  % SZS output end Proof for theBenchmark
% 0.19/0.55  % (10314)------------------------------
% 0.19/0.55  % (10314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (10314)Termination reason: Refutation
% 0.19/0.55  
% 0.19/0.55  % (10314)Memory used [KB]: 1918
% 0.19/0.55  % (10314)Time elapsed: 0.135 s
% 0.19/0.55  % (10314)------------------------------
% 0.19/0.55  % (10314)------------------------------
% 0.19/0.55  % (10316)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.55  % (10290)Success in time 0.197 s
%------------------------------------------------------------------------------
