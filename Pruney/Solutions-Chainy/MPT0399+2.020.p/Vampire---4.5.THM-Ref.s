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
% DateTime   : Thu Dec  3 12:46:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 175 expanded)
%              Number of leaves         :    9 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  202 ( 935 expanded)
%              Number of equality atoms :   38 ( 154 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f327,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f142,f145,f326])).

fof(f326,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f318,f20])).

fof(f20,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k1_xboole_0 != sK0
    & r1_setfam_1(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & r1_setfam_1(X0,k1_xboole_0) )
   => ( k1_xboole_0 != sK0
      & r1_setfam_1(sK0,k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( r1_setfam_1(X0,k1_xboole_0)
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

fof(f318,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_1 ),
    inference(superposition,[],[f21,f205])).

fof(f205,plain,
    ( ! [X23] : sK0 = k4_xboole_0(X23,X23)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f197,f182])).

fof(f182,plain,
    ( ! [X10] : sK0 = k4_xboole_0(sK0,X10)
    | ~ spl3_1 ),
    inference(resolution,[],[f152,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f152,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f150,f19])).

fof(f19,plain,(
    r1_setfam_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( ~ r1_setfam_1(X1,k1_xboole_0)
        | ~ r2_hidden(X0,X1) )
    | ~ spl3_1 ),
    inference(resolution,[],[f39,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X1),X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(sK1(X1),X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f12])).

fof(f12,plain,(
    ! [X1] :
      ( ? [X3] : r2_hidden(X3,X1)
     => r2_hidden(sK1(X1),X1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] : r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] : ~ r2_hidden(X3,X1)
            & r2_hidden(X2,X0) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f39,plain,
    ( ! [X10] : ~ r2_hidden(sK1(k1_xboole_0),X10)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl3_1
  <=> ! [X10] : ~ r2_hidden(sK1(k1_xboole_0),X10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f197,plain,
    ( ! [X23,X22] : k4_xboole_0(sK0,X22) = k4_xboole_0(X23,X23)
    | ~ spl3_1 ),
    inference(resolution,[],[f114,f152])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X1,X2,k4_xboole_0(X0,X0)),X1)
      | k4_xboole_0(X1,X2) = k4_xboole_0(X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k4_xboole_0(X0,X0)
      | r2_hidden(sK2(X1,X2,k4_xboole_0(X0,X0)),X1)
      | k4_xboole_0(X1,X2) = k4_xboole_0(X0,X0)
      | r2_hidden(sK2(X1,X2,k4_xboole_0(X0,X0)),X1) ) ),
    inference(resolution,[],[f49,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK2(X0,X1,k4_xboole_0(X2,X3)),X2)
      | k4_xboole_0(X0,X1) = k4_xboole_0(X2,X3)
      | r2_hidden(sK2(X0,X1,k4_xboole_0(X2,X3)),X0) ) ),
    inference(resolution,[],[f26,f31])).

fof(f31,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(sK2(X4,X5,k4_xboole_0(X6,X7)),X7)
      | k4_xboole_0(X6,X7) = k4_xboole_0(X4,X5)
      | r2_hidden(sK2(X4,X5,k4_xboole_0(X6,X7)),X4) ) ),
    inference(resolution,[],[f26,f30])).

fof(f30,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f145,plain,
    ( spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f144,f38,f41])).

fof(f41,plain,
    ( spl3_2
  <=> ! [X9,X8] :
        ( ~ r2_hidden(X8,X9)
        | ~ r1_setfam_1(X9,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f144,plain,(
    ! [X12,X10,X13] :
      ( ~ r2_hidden(sK1(k1_xboole_0),X13)
      | ~ r1_setfam_1(X10,k1_xboole_0)
      | ~ r2_hidden(X12,X10) ) ),
    inference(forward_demodulation,[],[f74,f21])).

fof(f74,plain,(
    ! [X12,X10,X13,X11] :
      ( ~ r1_setfam_1(X10,k1_xboole_0)
      | ~ r2_hidden(X12,X10)
      | ~ r2_hidden(sK1(k4_xboole_0(k1_xboole_0,X11)),X13) ) ),
    inference(forward_demodulation,[],[f71,f21])).

fof(f71,plain,(
    ! [X12,X10,X13,X11] :
      ( ~ r1_setfam_1(X10,k4_xboole_0(k1_xboole_0,X11))
      | ~ r2_hidden(X12,X10)
      | ~ r2_hidden(sK1(k4_xboole_0(k1_xboole_0,X11)),X13) ) ),
    inference(resolution,[],[f34,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f30,f21])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK1(k4_xboole_0(X2,X3)),X2)
      | ~ r1_setfam_1(X1,k4_xboole_0(X2,X3))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f22,f31])).

fof(f142,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f130,f20])).

fof(f130,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_2 ),
    inference(superposition,[],[f21,f106])).

fof(f106,plain,
    ( ! [X0] : sK0 = k4_xboole_0(X0,X0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f105,f44])).

fof(f44,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f42,f19])).

fof(f42,plain,
    ( ! [X8,X9] :
        ( ~ r1_setfam_1(X9,k1_xboole_0)
        | ~ r2_hidden(X8,X9) )
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f105,plain,
    ( ! [X0] :
        ( sK0 = k4_xboole_0(X0,X0)
        | r2_hidden(sK2(X0,X0,sK0),sK0) )
    | ~ spl3_2 ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,
    ( ! [X0] :
        ( sK0 = k4_xboole_0(X0,X0)
        | sK0 = k4_xboole_0(X0,X0)
        | r2_hidden(sK2(X0,X0,sK0),sK0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f53,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK2(X2,X3,sK0),X2)
        | sK0 = k4_xboole_0(X2,X3) )
    | ~ spl3_2 ),
    inference(resolution,[],[f44,f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:35:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.43  % (32058)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.44  % (32058)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f327,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f142,f145,f326])).
% 0.22/0.44  fof(f326,plain,(
% 0.22/0.44    ~spl3_1),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f325])).
% 0.22/0.44  fof(f325,plain,(
% 0.22/0.44    $false | ~spl3_1),
% 0.22/0.44    inference(subsumption_resolution,[],[f318,f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    k1_xboole_0 != sK0),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    k1_xboole_0 != sK0 & r1_setfam_1(sK0,k1_xboole_0)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0)) => (k1_xboole_0 != sK0 & r1_setfam_1(sK0,k1_xboole_0))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0))),
% 0.22/0.44    inference(ennf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,negated_conjecture,(
% 0.22/0.44    ~! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.44    inference(negated_conjecture,[],[f4])).
% 0.22/0.44  fof(f4,conjecture,(
% 0.22/0.44    ! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).
% 0.22/0.44  fof(f318,plain,(
% 0.22/0.44    k1_xboole_0 = sK0 | ~spl3_1),
% 0.22/0.44    inference(superposition,[],[f21,f205])).
% 0.22/0.44  fof(f205,plain,(
% 0.22/0.44    ( ! [X23] : (sK0 = k4_xboole_0(X23,X23)) ) | ~spl3_1),
% 0.22/0.44    inference(forward_demodulation,[],[f197,f182])).
% 0.22/0.44  fof(f182,plain,(
% 0.22/0.44    ( ! [X10] : (sK0 = k4_xboole_0(sK0,X10)) ) | ~spl3_1),
% 0.22/0.44    inference(resolution,[],[f152,f51])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 0.22/0.44    inference(factoring,[],[f26])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.44    inference(rectify,[],[f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.44    inference(flattening,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.44    inference(nnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.44  fof(f152,plain,(
% 0.22/0.44    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl3_1),
% 0.22/0.44    inference(resolution,[],[f150,f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    r1_setfam_1(sK0,k1_xboole_0)),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f150,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_setfam_1(X1,k1_xboole_0) | ~r2_hidden(X0,X1)) ) | ~spl3_1),
% 0.22/0.44    inference(resolution,[],[f39,f22])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r2_hidden(sK1(X1),X1) | ~r2_hidden(X2,X0) | ~r1_setfam_1(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ! [X0,X1] : (! [X2] : (r2_hidden(sK1(X1),X1) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ! [X1] : (? [X3] : r2_hidden(X3,X1) => r2_hidden(sK1(X1),X1))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ! [X0,X1] : (! [X2] : (? [X3] : r2_hidden(X3,X1) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,plain,(
% 0.22/0.44    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~r2_hidden(X3,X1) & r2_hidden(X2,X0)))),
% 0.22/0.44    inference(pure_predicate_removal,[],[f6])).
% 0.22/0.44  fof(f6,plain,(
% 0.22/0.44    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.22/0.44    inference(unused_predicate_definition_removal,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    ( ! [X10] : (~r2_hidden(sK1(k1_xboole_0),X10)) ) | ~spl3_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f38])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    spl3_1 <=> ! [X10] : ~r2_hidden(sK1(k1_xboole_0),X10)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.44  fof(f197,plain,(
% 0.22/0.44    ( ! [X23,X22] : (k4_xboole_0(sK0,X22) = k4_xboole_0(X23,X23)) ) | ~spl3_1),
% 0.22/0.44    inference(resolution,[],[f114,f152])).
% 0.22/0.44  fof(f114,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r2_hidden(sK2(X1,X2,k4_xboole_0(X0,X0)),X1) | k4_xboole_0(X1,X2) = k4_xboole_0(X0,X0)) )),
% 0.22/0.44    inference(duplicate_literal_removal,[],[f110])).
% 0.22/0.44  fof(f110,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X0,X0) | r2_hidden(sK2(X1,X2,k4_xboole_0(X0,X0)),X1) | k4_xboole_0(X1,X2) = k4_xboole_0(X0,X0) | r2_hidden(sK2(X1,X2,k4_xboole_0(X0,X0)),X1)) )),
% 0.22/0.44    inference(resolution,[],[f49,f48])).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (r2_hidden(sK2(X0,X1,k4_xboole_0(X2,X3)),X2) | k4_xboole_0(X0,X1) = k4_xboole_0(X2,X3) | r2_hidden(sK2(X0,X1,k4_xboole_0(X2,X3)),X0)) )),
% 0.22/0.44    inference(resolution,[],[f26,f31])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 0.22/0.44    inference(equality_resolution,[],[f23])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    ( ! [X6,X4,X7,X5] : (~r2_hidden(sK2(X4,X5,k4_xboole_0(X6,X7)),X7) | k4_xboole_0(X6,X7) = k4_xboole_0(X4,X5) | r2_hidden(sK2(X4,X5,k4_xboole_0(X6,X7)),X4)) )),
% 0.22/0.44    inference(resolution,[],[f26,f30])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.22/0.44    inference(equality_resolution,[],[f24])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.44  fof(f145,plain,(
% 0.22/0.44    spl3_2 | spl3_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f144,f38,f41])).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    spl3_2 <=> ! [X9,X8] : (~r2_hidden(X8,X9) | ~r1_setfam_1(X9,k1_xboole_0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.44  fof(f144,plain,(
% 0.22/0.44    ( ! [X12,X10,X13] : (~r2_hidden(sK1(k1_xboole_0),X13) | ~r1_setfam_1(X10,k1_xboole_0) | ~r2_hidden(X12,X10)) )),
% 0.22/0.44    inference(forward_demodulation,[],[f74,f21])).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    ( ! [X12,X10,X13,X11] : (~r1_setfam_1(X10,k1_xboole_0) | ~r2_hidden(X12,X10) | ~r2_hidden(sK1(k4_xboole_0(k1_xboole_0,X11)),X13)) )),
% 0.22/0.44    inference(forward_demodulation,[],[f71,f21])).
% 0.22/0.44  fof(f71,plain,(
% 0.22/0.44    ( ! [X12,X10,X13,X11] : (~r1_setfam_1(X10,k4_xboole_0(k1_xboole_0,X11)) | ~r2_hidden(X12,X10) | ~r2_hidden(sK1(k4_xboole_0(k1_xboole_0,X11)),X13)) )),
% 0.22/0.44    inference(resolution,[],[f34,f32])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 0.22/0.44    inference(superposition,[],[f30,f21])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (r2_hidden(sK1(k4_xboole_0(X2,X3)),X2) | ~r1_setfam_1(X1,k4_xboole_0(X2,X3)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.44    inference(resolution,[],[f22,f31])).
% 0.22/0.44  fof(f142,plain,(
% 0.22/0.44    ~spl3_2),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f141])).
% 0.22/0.44  fof(f141,plain,(
% 0.22/0.44    $false | ~spl3_2),
% 0.22/0.44    inference(subsumption_resolution,[],[f130,f20])).
% 0.22/0.44  fof(f130,plain,(
% 0.22/0.44    k1_xboole_0 = sK0 | ~spl3_2),
% 0.22/0.44    inference(superposition,[],[f21,f106])).
% 0.22/0.44  fof(f106,plain,(
% 0.22/0.44    ( ! [X0] : (sK0 = k4_xboole_0(X0,X0)) ) | ~spl3_2),
% 0.22/0.44    inference(subsumption_resolution,[],[f105,f44])).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl3_2),
% 0.22/0.44    inference(resolution,[],[f42,f19])).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    ( ! [X8,X9] : (~r1_setfam_1(X9,k1_xboole_0) | ~r2_hidden(X8,X9)) ) | ~spl3_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f41])).
% 0.22/0.44  fof(f105,plain,(
% 0.22/0.44    ( ! [X0] : (sK0 = k4_xboole_0(X0,X0) | r2_hidden(sK2(X0,X0,sK0),sK0)) ) | ~spl3_2),
% 0.22/0.44    inference(duplicate_literal_removal,[],[f98])).
% 0.22/0.44  fof(f98,plain,(
% 0.22/0.44    ( ! [X0] : (sK0 = k4_xboole_0(X0,X0) | sK0 = k4_xboole_0(X0,X0) | r2_hidden(sK2(X0,X0,sK0),sK0)) ) | ~spl3_2),
% 0.22/0.44    inference(resolution,[],[f53,f27])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    ( ! [X2,X3] : (r2_hidden(sK2(X2,X3,sK0),X2) | sK0 = k4_xboole_0(X2,X3)) ) | ~spl3_2),
% 0.22/0.44    inference(resolution,[],[f44,f26])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (32058)------------------------------
% 0.22/0.44  % (32058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (32058)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (32058)Memory used [KB]: 10746
% 0.22/0.44  % (32058)Time elapsed: 0.042 s
% 0.22/0.44  % (32058)------------------------------
% 0.22/0.44  % (32058)------------------------------
% 0.22/0.44  % (32055)Success in time 0.079 s
%------------------------------------------------------------------------------
