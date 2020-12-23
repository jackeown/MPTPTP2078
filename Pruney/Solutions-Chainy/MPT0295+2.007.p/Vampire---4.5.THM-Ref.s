%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 116 expanded)
%              Number of leaves         :    9 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  228 ( 758 expanded)
%              Number of equality atoms :   56 ( 176 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f181,plain,(
    $false ),
    inference(subsumption_resolution,[],[f159,f105])).

fof(f105,plain,(
    sK3 = k4_tarski(sK8(sK1,sK2,sK3),sK9(sK1,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f99,f44])).

fof(f44,plain,(
    ! [X0,X8,X1] :
      ( ~ r2_hidden(X8,k2_zfmisc_1(X0,X1))
      | k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK5(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2))
              & r2_hidden(sK7(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8
                & r2_hidden(sK9(X0,X1,X8),X1)
                & r2_hidden(sK8(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f16,f19,f18,f17])).

fof(f17,plain,(
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
              ( k4_tarski(X4,X5) != sK5(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK5(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK5(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2))
        & r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(sK6(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8
        & r2_hidden(sK9(X0,X1,X8),X1)
        & r2_hidden(sK8(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f99,plain,(
    r2_hidden(sK3,k2_zfmisc_1(sK1,sK2)) ),
    inference(superposition,[],[f49,f51])).

fof(f51,plain,(
    k2_zfmisc_1(sK1,sK2) = k2_xboole_0(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f21,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f21,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ! [X4,X5] :
        ( k4_tarski(X4,X5) != sK3
        | ~ r2_hidden(X5,sK2)
        | ~ r2_hidden(X4,sK1) )
    & r2_hidden(sK3,sK0)
    & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4,X5] :
            ( k4_tarski(X4,X5) != X3
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) )
   => ( ! [X5,X4] :
          ( k4_tarski(X4,X5) != sK3
          | ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X4,sK1) )
      & r2_hidden(sK3,sK0)
      & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( k4_tarski(X4,X5) != X3
          | ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X3,X0)
      & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4,X5] :
              ~ ( k4_tarski(X4,X5) = X3
                & r2_hidden(X5,X2)
                & r2_hidden(X4,X1) )
          & r2_hidden(X3,X0)
          & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(f49,plain,(
    ! [X0] : r2_hidden(sK3,k2_xboole_0(sK0,X0)) ),
    inference(unit_resulting_resolution,[],[f22,f40])).

fof(f40,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & ~ r2_hidden(sK4(X0,X1,X2),X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f13])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & ~ r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f22,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f159,plain,(
    sK3 != k4_tarski(sK8(sK1,sK2,sK3),sK9(sK1,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f103,f104,f23])).

fof(f23,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK3
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f104,plain,(
    r2_hidden(sK9(sK1,sK2,sK3),sK2) ),
    inference(unit_resulting_resolution,[],[f99,f45])).

fof(f45,plain,(
    ! [X0,X8,X1] :
      ( ~ r2_hidden(X8,k2_zfmisc_1(X0,X1))
      | r2_hidden(sK9(X0,X1,X8),X1) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK9(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f103,plain,(
    r2_hidden(sK8(sK1,sK2,sK3),sK1) ),
    inference(unit_resulting_resolution,[],[f99,f46])).

fof(f46,plain,(
    ! [X0,X8,X1] :
      ( ~ r2_hidden(X8,k2_zfmisc_1(X0,X1))
      | r2_hidden(sK8(X0,X1,X8),X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK8(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:44:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (14753)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (14747)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (14753)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (14750)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (14756)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.49  % (14739)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f181,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f159,f105])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    sK3 = k4_tarski(sK8(sK1,sK2,sK3),sK9(sK1,sK2,sK3))),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f99,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0,X8,X1] : (~r2_hidden(X8,k2_zfmisc_1(X0,X1)) | k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8) )),
% 0.22/0.50    inference(equality_resolution,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X2,X0,X8,X1] : (k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8 | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK5(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8 & r2_hidden(sK9(X0,X1,X8),X1) & r2_hidden(sK8(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f16,f19,f18,f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK5(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK5(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK5(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8 & r2_hidden(sK9(X0,X1,X8),X1) & r2_hidden(sK8(X0,X1,X8),X0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.22/0.50    inference(rectify,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.22/0.50    inference(nnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    r2_hidden(sK3,k2_zfmisc_1(sK1,sK2))),
% 0.22/0.50    inference(superposition,[],[f49,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    k2_zfmisc_1(sK1,sK2) = k2_xboole_0(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f21,f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,plain,(
% 0.22/0.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ! [X4,X5] : (k4_tarski(X4,X5) != sK3 | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) & r2_hidden(sK3,sK0) & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f8])).
% 0.22/0.50  fof(f8,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X2) | ~r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2))) => (! [X5,X4] : (k4_tarski(X4,X5) != sK3 | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) & r2_hidden(sK3,sK0) & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f6,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X2) | ~r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.50    inference(negated_conjecture,[],[f4])).
% 0.22/0.50  fof(f4,conjecture,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(sK3,k2_xboole_0(sK0,X0))) )),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f22,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.50    inference(rectify,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.50    inference(flattening,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.50    inference(nnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    r2_hidden(sK3,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    sK3 != k4_tarski(sK8(sK1,sK2,sK3),sK9(sK1,sK2,sK3))),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f103,f104,f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ( ! [X4,X5] : (k4_tarski(X4,X5) != sK3 | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    r2_hidden(sK9(sK1,sK2,sK3),sK2)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f99,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0,X8,X1] : (~r2_hidden(X8,k2_zfmisc_1(X0,X1)) | r2_hidden(sK9(X0,X1,X8),X1)) )),
% 0.22/0.50    inference(equality_resolution,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X2,X0,X8,X1] : (r2_hidden(sK9(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    r2_hidden(sK8(sK1,sK2,sK3),sK1)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f99,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0,X8,X1] : (~r2_hidden(X8,k2_zfmisc_1(X0,X1)) | r2_hidden(sK8(X0,X1,X8),X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X2,X0,X8,X1] : (r2_hidden(sK8(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (14753)------------------------------
% 0.22/0.50  % (14753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (14753)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (14753)Memory used [KB]: 6268
% 0.22/0.50  % (14753)Time elapsed: 0.075 s
% 0.22/0.50  % (14753)------------------------------
% 0.22/0.50  % (14753)------------------------------
% 0.22/0.50  % (14736)Success in time 0.134 s
%------------------------------------------------------------------------------
