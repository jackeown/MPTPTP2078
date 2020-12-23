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
% DateTime   : Thu Dec  3 12:41:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 127 expanded)
%              Number of leaves         :   11 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  187 ( 623 expanded)
%              Number of equality atoms :   41 ( 134 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f104,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f102,f103])).

fof(f103,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f86,f94])).

fof(f94,plain,
    ( spl10_1
  <=> r2_hidden(sK8(sK1,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f86,plain,(
    r2_hidden(sK8(sK1,sK2,sK3),sK2) ),
    inference(resolution,[],[f70,f35])).

fof(f35,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK8(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK8(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f13,f16,f15,f14])).

fof(f14,plain,(
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

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK4(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK4(X0,X1,X2) = k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(sK5(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
        & r2_hidden(sK8(X0,X1,X8),X1)
        & r2_hidden(sK7(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f70,plain,(
    r2_hidden(sK3,k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f56,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f56,plain,(
    r1_tarski(k1_tarski(sK3),k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f49,f18])).

fof(f18,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ! [X4,X5] :
        ( k4_tarski(X4,X5) != sK3
        | ~ r2_hidden(X5,sK2)
        | ~ r2_hidden(X4,sK1) )
    & r2_hidden(sK3,sK0)
    & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f9])).

fof(f9,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(f49,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | r1_tarski(k1_tarski(sK3),X0) ) ),
    inference(resolution,[],[f47,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f47,plain,(
    r1_tarski(k1_tarski(sK3),sK0) ),
    inference(resolution,[],[f19,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f19,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f102,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f85,f98])).

fof(f98,plain,
    ( spl10_2
  <=> r2_hidden(sK7(sK1,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f85,plain,(
    r2_hidden(sK7(sK1,sK2,sK3),sK1) ),
    inference(resolution,[],[f70,f36])).

fof(f36,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK7(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f101,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f84,f98,f94])).

fof(f84,plain,
    ( ~ r2_hidden(sK7(sK1,sK2,sK3),sK1)
    | ~ r2_hidden(sK8(sK1,sK2,sK3),sK2) ),
    inference(resolution,[],[f70,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK7(X0,X1,sK3),sK1)
      | ~ r2_hidden(sK8(X0,X1,sK3),sK2) ) ),
    inference(resolution,[],[f38,f43])).

fof(f43,plain,(
    ! [X0,X8,X1] :
      ( sQ9_eqProxy(k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)),X8)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_proxy_replacement,[],[f34,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( sQ9_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ9_eqProxy])])).

fof(f34,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X4,X5] :
      ( ~ sQ9_eqProxy(k4_tarski(X4,X5),sK3)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(equality_proxy_replacement,[],[f20,f37])).

fof(f20,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK3
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:26:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (25153)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (25163)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (25163)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f101,f102,f103])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    spl10_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f86,f94])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    spl10_1 <=> r2_hidden(sK8(sK1,sK2,sK3),sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    r2_hidden(sK8(sK1,sK2,sK3),sK2)),
% 0.21/0.47    inference(resolution,[],[f70,f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0,X8,X1] : (r2_hidden(sK8(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.47    inference(equality_resolution,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X2,X0,X8,X1] : (r2_hidden(sK8(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK4(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((sK4(X0,X1,X2) = k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8 & r2_hidden(sK8(X0,X1,X8),X1) & r2_hidden(sK7(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f13,f16,f15,f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK4(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK4(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK4(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK4(X0,X1,X2) = k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8 & r2_hidden(sK8(X0,X1,X8),X1) & r2_hidden(sK7(X0,X1,X8),X0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.21/0.47    inference(rectify,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.21/0.47    inference(nnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    r2_hidden(sK3,k2_zfmisc_1(sK1,sK2))),
% 0.21/0.47    inference(resolution,[],[f56,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.47    inference(nnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    r1_tarski(k1_tarski(sK3),k2_zfmisc_1(sK1,sK2))),
% 0.21/0.47    inference(resolution,[],[f49,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X4,X5] : (k4_tarski(X4,X5) != sK3 | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) & r2_hidden(sK3,sK0) & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3] : (! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X2) | ~r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2))) => (! [X5,X4] : (k4_tarski(X4,X5) != sK3 | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) & r2_hidden(sK3,sK0) & r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3] : (! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X2) | ~r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.47    inference(negated_conjecture,[],[f4])).
% 0.21/0.47  fof(f4,conjecture,(
% 0.21/0.47    ! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_tarski(sK0,X0) | r1_tarski(k1_tarski(sK3),X0)) )),
% 0.21/0.47    inference(resolution,[],[f47,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    r1_tarski(k1_tarski(sK3),sK0)),
% 0.21/0.47    inference(resolution,[],[f19,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    r2_hidden(sK3,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    spl10_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f85,f98])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    spl10_2 <=> r2_hidden(sK7(sK1,sK2,sK3),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    r2_hidden(sK7(sK1,sK2,sK3),sK1)),
% 0.21/0.47    inference(resolution,[],[f70,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.47    inference(equality_resolution,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X2,X0,X8,X1] : (r2_hidden(sK7(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    ~spl10_1 | ~spl10_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f84,f98,f94])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    ~r2_hidden(sK7(sK1,sK2,sK3),sK1) | ~r2_hidden(sK8(sK1,sK2,sK3),sK2)),
% 0.21/0.47    inference(resolution,[],[f70,f53])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(sK3,k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK7(X0,X1,sK3),sK1) | ~r2_hidden(sK8(X0,X1,sK3),sK2)) )),
% 0.21/0.47    inference(resolution,[],[f38,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0,X8,X1] : (sQ9_eqProxy(k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)),X8) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.47    inference(equality_proxy_replacement,[],[f34,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ! [X1,X0] : (sQ9_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.47    introduced(equality_proxy_definition,[new_symbols(naming,[sQ9_eqProxy])])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0,X8,X1] : (k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8 | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.47    inference(equality_resolution,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X2,X0,X8,X1] : (k4_tarski(sK7(X0,X1,X8),sK8(X0,X1,X8)) = X8 | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X4,X5] : (~sQ9_eqProxy(k4_tarski(X4,X5),sK3) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) )),
% 0.21/0.47    inference(equality_proxy_replacement,[],[f20,f37])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X4,X5] : (k4_tarski(X4,X5) != sK3 | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (25163)------------------------------
% 0.21/0.47  % (25163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (25163)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (25163)Memory used [KB]: 6140
% 0.21/0.47  % (25163)Time elapsed: 0.052 s
% 0.21/0.47  % (25163)------------------------------
% 0.21/0.47  % (25163)------------------------------
% 0.21/0.47  % (25149)Success in time 0.112 s
%------------------------------------------------------------------------------
