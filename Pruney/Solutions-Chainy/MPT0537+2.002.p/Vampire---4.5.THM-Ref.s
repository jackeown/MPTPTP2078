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
% DateTime   : Thu Dec  3 12:49:06 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   46 (  71 expanded)
%              Number of leaves         :   12 (  22 expanded)
%              Depth                    :   12
%              Number of atoms          :  196 ( 258 expanded)
%              Number of equality atoms :   53 (  96 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f246,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f51,f233,f237])).

fof(f237,plain,(
    ~ spl6_28 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | ~ spl6_28 ),
    inference(resolution,[],[f231,f52])).

fof(f52,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f29,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f29,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f231,plain,
    ( r2_hidden(k4_tarski(sK4(k1_xboole_0,sK0,k1_xboole_0),sK5(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl6_28
  <=> r2_hidden(k4_tarski(sK4(k1_xboole_0,sK0,k1_xboole_0),sK5(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f233,plain,
    ( spl6_28
    | spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f227,f49,f45,f230])).

fof(f45,plain,
    ( spl6_1
  <=> k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f49,plain,
    ( spl6_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f227,plain,
    ( k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0)
    | r2_hidden(k4_tarski(sK4(k1_xboole_0,sK0,k1_xboole_0),sK5(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl6_2 ),
    inference(resolution,[],[f225,f52])).

fof(f225,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(X0,sK0,k1_xboole_0),X0)
        | k1_xboole_0 = k8_relat_1(X0,sK0)
        | r2_hidden(k4_tarski(sK4(X0,sK0,k1_xboole_0),sK5(X0,sK0,k1_xboole_0)),k1_xboole_0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f201,f52])).

fof(f201,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK1(X1),X1)
        | k8_relat_1(X0,sK0) = X1
        | r2_hidden(sK5(X0,sK0,X1),X0)
        | r2_hidden(k4_tarski(sK4(X0,sK0,X1),sK5(X0,sK0,X1)),X1) )
    | ~ spl6_2 ),
    inference(resolution,[],[f57,f50])).

fof(f50,plain,
    ( v1_relat_1(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f57,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X3)
      | r2_hidden(k4_tarski(sK4(X2,X3,X4),sK5(X2,X3,X4)),X4)
      | k8_relat_1(X2,X3) = X4
      | r2_hidden(sK5(X2,X3,X4),X2)
      | r2_hidden(sK1(X4),X4) ) ),
    inference(resolution,[],[f33,f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK2(X4),sK3(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f15,f14])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK2(X4),sK3(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)
      | k8_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK5(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X1)
                    & r2_hidden(sK5(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

fof(f51,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f24,f49])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k8_relat_1(k1_xboole_0,X0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( k1_xboole_0 != k8_relat_1(k1_xboole_0,X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

fof(f47,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f25,f45])).

fof(f25,plain,(
    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 19:39:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.44  % (20784)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.23/0.45  % (20776)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.23/0.46  % (20776)Refutation found. Thanks to Tanya!
% 0.23/0.46  % SZS status Theorem for theBenchmark
% 0.23/0.46  % SZS output start Proof for theBenchmark
% 0.23/0.46  fof(f246,plain,(
% 0.23/0.46    $false),
% 0.23/0.46    inference(avatar_sat_refutation,[],[f47,f51,f233,f237])).
% 0.23/0.46  fof(f237,plain,(
% 0.23/0.46    ~spl6_28),
% 0.23/0.46    inference(avatar_contradiction_clause,[],[f235])).
% 0.23/0.46  fof(f235,plain,(
% 0.23/0.46    $false | ~spl6_28),
% 0.23/0.46    inference(resolution,[],[f231,f52])).
% 0.23/0.46  fof(f52,plain,(
% 0.23/0.46    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.23/0.46    inference(superposition,[],[f29,f42])).
% 0.23/0.46  fof(f42,plain,(
% 0.23/0.46    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.23/0.46    inference(equality_resolution,[],[f38])).
% 0.23/0.46  fof(f38,plain,(
% 0.23/0.46    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.23/0.46    inference(cnf_transformation,[],[f23])).
% 0.23/0.46  fof(f23,plain,(
% 0.23/0.46    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.23/0.46    inference(flattening,[],[f22])).
% 0.23/0.46  fof(f22,plain,(
% 0.23/0.46    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.23/0.46    inference(nnf_transformation,[],[f1])).
% 0.23/0.46  fof(f1,axiom,(
% 0.23/0.46    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.23/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.23/0.46  fof(f29,plain,(
% 0.23/0.46    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.23/0.46    inference(cnf_transformation,[],[f2])).
% 0.23/0.46  fof(f2,axiom,(
% 0.23/0.46    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.23/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.23/0.46  fof(f231,plain,(
% 0.23/0.46    r2_hidden(k4_tarski(sK4(k1_xboole_0,sK0,k1_xboole_0),sK5(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0) | ~spl6_28),
% 0.23/0.46    inference(avatar_component_clause,[],[f230])).
% 0.23/0.46  fof(f230,plain,(
% 0.23/0.46    spl6_28 <=> r2_hidden(k4_tarski(sK4(k1_xboole_0,sK0,k1_xboole_0),sK5(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0)),
% 0.23/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.23/0.46  fof(f233,plain,(
% 0.23/0.46    spl6_28 | spl6_1 | ~spl6_2),
% 0.23/0.46    inference(avatar_split_clause,[],[f227,f49,f45,f230])).
% 0.23/0.46  fof(f45,plain,(
% 0.23/0.46    spl6_1 <=> k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0)),
% 0.23/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.23/0.46  fof(f49,plain,(
% 0.23/0.46    spl6_2 <=> v1_relat_1(sK0)),
% 0.23/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.23/0.46  fof(f227,plain,(
% 0.23/0.46    k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0) | r2_hidden(k4_tarski(sK4(k1_xboole_0,sK0,k1_xboole_0),sK5(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0) | ~spl6_2),
% 0.23/0.46    inference(resolution,[],[f225,f52])).
% 0.23/0.46  fof(f225,plain,(
% 0.23/0.46    ( ! [X0] : (r2_hidden(sK5(X0,sK0,k1_xboole_0),X0) | k1_xboole_0 = k8_relat_1(X0,sK0) | r2_hidden(k4_tarski(sK4(X0,sK0,k1_xboole_0),sK5(X0,sK0,k1_xboole_0)),k1_xboole_0)) ) | ~spl6_2),
% 0.23/0.46    inference(resolution,[],[f201,f52])).
% 0.23/0.46  fof(f201,plain,(
% 0.23/0.46    ( ! [X0,X1] : (r2_hidden(sK1(X1),X1) | k8_relat_1(X0,sK0) = X1 | r2_hidden(sK5(X0,sK0,X1),X0) | r2_hidden(k4_tarski(sK4(X0,sK0,X1),sK5(X0,sK0,X1)),X1)) ) | ~spl6_2),
% 0.23/0.46    inference(resolution,[],[f57,f50])).
% 0.23/0.46  fof(f50,plain,(
% 0.23/0.46    v1_relat_1(sK0) | ~spl6_2),
% 0.23/0.46    inference(avatar_component_clause,[],[f49])).
% 0.23/0.46  fof(f57,plain,(
% 0.23/0.46    ( ! [X4,X2,X3] : (~v1_relat_1(X3) | r2_hidden(k4_tarski(sK4(X2,X3,X4),sK5(X2,X3,X4)),X4) | k8_relat_1(X2,X3) = X4 | r2_hidden(sK5(X2,X3,X4),X2) | r2_hidden(sK1(X4),X4)) )),
% 0.23/0.46    inference(resolution,[],[f33,f27])).
% 0.23/0.46  fof(f27,plain,(
% 0.23/0.46    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK1(X0),X0)) )),
% 0.23/0.46    inference(cnf_transformation,[],[f16])).
% 0.23/0.46  fof(f16,plain,(
% 0.23/0.46    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0))) & (! [X4] : (k4_tarski(sK2(X4),sK3(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.23/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f15,f14])).
% 0.23/0.46  fof(f14,plain,(
% 0.23/0.46    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 0.23/0.46    introduced(choice_axiom,[])).
% 0.23/0.47  fof(f15,plain,(
% 0.23/0.47    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK2(X4),sK3(X4)) = X4)),
% 0.23/0.47    introduced(choice_axiom,[])).
% 0.23/0.47  fof(f13,plain,(
% 0.23/0.47    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.23/0.47    inference(rectify,[],[f12])).
% 0.23/0.47  fof(f12,plain,(
% 0.23/0.47    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 0.23/0.47    inference(nnf_transformation,[],[f8])).
% 0.23/0.47  fof(f8,plain,(
% 0.23/0.47    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.23/0.47    inference(ennf_transformation,[],[f4])).
% 0.23/0.47  fof(f4,axiom,(
% 0.23/0.47    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.23/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.23/0.47  fof(f33,plain,(
% 0.23/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) | k8_relat_1(X0,X1) = X2 | ~v1_relat_1(X1)) )),
% 0.23/0.47    inference(cnf_transformation,[],[f21])).
% 0.23/0.47  fof(f21,plain,(
% 0.23/0.47    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0)) & ((r2_hidden(k4_tarski(X5,X6),X1) & r2_hidden(X6,X0)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.23/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f19,f20])).
% 0.23/0.47  fof(f20,plain,(
% 0.23/0.47    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2))))),
% 0.23/0.47    introduced(choice_axiom,[])).
% 0.23/0.47  fof(f19,plain,(
% 0.23/0.47    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0)) & ((r2_hidden(k4_tarski(X5,X6),X1) & r2_hidden(X6,X0)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.23/0.47    inference(rectify,[],[f18])).
% 0.23/0.47  fof(f18,plain,(
% 0.23/0.47    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.23/0.47    inference(flattening,[],[f17])).
% 0.23/0.47  fof(f17,plain,(
% 0.23/0.47    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0))) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.23/0.47    inference(nnf_transformation,[],[f9])).
% 0.23/0.47  fof(f9,plain,(
% 0.23/0.47    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.23/0.47    inference(ennf_transformation,[],[f3])).
% 0.23/0.47  fof(f3,axiom,(
% 0.23/0.47    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0))))))),
% 0.23/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).
% 0.23/0.47  fof(f51,plain,(
% 0.23/0.47    spl6_2),
% 0.23/0.47    inference(avatar_split_clause,[],[f24,f49])).
% 0.23/0.47  fof(f24,plain,(
% 0.23/0.47    v1_relat_1(sK0)),
% 0.23/0.47    inference(cnf_transformation,[],[f11])).
% 0.23/0.47  fof(f11,plain,(
% 0.23/0.47    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) & v1_relat_1(sK0)),
% 0.23/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).
% 0.23/0.47  fof(f10,plain,(
% 0.23/0.47    ? [X0] : (k1_xboole_0 != k8_relat_1(k1_xboole_0,X0) & v1_relat_1(X0)) => (k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) & v1_relat_1(sK0))),
% 0.23/0.47    introduced(choice_axiom,[])).
% 0.23/0.47  fof(f7,plain,(
% 0.23/0.47    ? [X0] : (k1_xboole_0 != k8_relat_1(k1_xboole_0,X0) & v1_relat_1(X0))),
% 0.23/0.47    inference(ennf_transformation,[],[f6])).
% 0.23/0.47  fof(f6,negated_conjecture,(
% 0.23/0.47    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.23/0.47    inference(negated_conjecture,[],[f5])).
% 0.23/0.47  fof(f5,conjecture,(
% 0.23/0.47    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.23/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).
% 0.23/0.47  fof(f47,plain,(
% 0.23/0.47    ~spl6_1),
% 0.23/0.47    inference(avatar_split_clause,[],[f25,f45])).
% 0.23/0.47  fof(f25,plain,(
% 0.23/0.47    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)),
% 0.23/0.47    inference(cnf_transformation,[],[f11])).
% 0.23/0.47  % SZS output end Proof for theBenchmark
% 0.23/0.47  % (20776)------------------------------
% 0.23/0.47  % (20776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.47  % (20776)Termination reason: Refutation
% 0.23/0.47  
% 0.23/0.47  % (20776)Memory used [KB]: 10874
% 0.23/0.47  % (20776)Time elapsed: 0.022 s
% 0.23/0.47  % (20776)------------------------------
% 0.23/0.47  % (20776)------------------------------
% 0.23/0.47  % (20766)Success in time 0.096 s
%------------------------------------------------------------------------------
