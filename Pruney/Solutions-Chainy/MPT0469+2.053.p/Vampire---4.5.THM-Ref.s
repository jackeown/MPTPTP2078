%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 110 expanded)
%              Number of leaves         :   21 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  209 ( 307 expanded)
%              Number of equality atoms :   38 (  50 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f55,f60,f65,f79,f91,f111,f136])).

fof(f136,plain,
    ( ~ spl8_5
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f121,f77,f63])).

fof(f63,plain,
    ( spl8_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f77,plain,
    ( spl8_6
  <=> r2_hidden(k4_tarski(sK0(k1_relat_1(k1_xboole_0)),sK3(k1_xboole_0,sK0(k1_relat_1(k1_xboole_0)))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f121,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_6 ),
    inference(resolution,[],[f78,f30])).

fof(f30,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f78,plain,
    ( r2_hidden(k4_tarski(sK0(k1_relat_1(k1_xboole_0)),sK3(k1_xboole_0,sK0(k1_relat_1(k1_xboole_0)))),k1_xboole_0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f111,plain,
    ( ~ spl8_5
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f95,f89,f63])).

fof(f89,plain,
    ( spl8_7
  <=> r2_hidden(k4_tarski(sK6(k1_xboole_0,sK0(k2_relat_1(k1_xboole_0))),sK0(k2_relat_1(k1_xboole_0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f95,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_7 ),
    inference(resolution,[],[f90,f30])).

fof(f90,plain,
    ( r2_hidden(k4_tarski(sK6(k1_xboole_0,sK0(k2_relat_1(k1_xboole_0))),sK0(k2_relat_1(k1_xboole_0))),k1_xboole_0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f91,plain,
    ( spl8_7
    | spl8_2 ),
    inference(avatar_split_clause,[],[f87,f49,f89])).

fof(f49,plain,
    ( spl8_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f87,plain,
    ( r2_hidden(k4_tarski(sK6(k1_xboole_0,sK0(k2_relat_1(k1_xboole_0))),sK0(k2_relat_1(k1_xboole_0))),k1_xboole_0)
    | spl8_2 ),
    inference(trivial_inequality_removal,[],[f86])).

fof(f86,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(k4_tarski(sK6(k1_xboole_0,sK0(k2_relat_1(k1_xboole_0))),sK0(k2_relat_1(k1_xboole_0))),k1_xboole_0)
    | spl8_2 ),
    inference(superposition,[],[f50,f71])).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | r2_hidden(k4_tarski(sK6(X0,sK0(k2_relat_1(X0))),sK0(k2_relat_1(X0))),X0) ) ),
    inference(resolution,[],[f69,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f69,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | r2_hidden(k4_tarski(sK6(X0,sK0(k2_relat_1(X0))),sK0(k2_relat_1(X0))),X0) ) ),
    inference(resolution,[],[f44,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f21,f24,f23,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f50,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f79,plain,
    ( spl8_6
    | spl8_1 ),
    inference(avatar_split_clause,[],[f75,f46,f77])).

fof(f46,plain,
    ( spl8_1
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f75,plain,
    ( r2_hidden(k4_tarski(sK0(k1_relat_1(k1_xboole_0)),sK3(k1_xboole_0,sK0(k1_relat_1(k1_xboole_0)))),k1_xboole_0)
    | spl8_1 ),
    inference(trivial_inequality_removal,[],[f72])).

fof(f72,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(k4_tarski(sK0(k1_relat_1(k1_xboole_0)),sK3(k1_xboole_0,sK0(k1_relat_1(k1_xboole_0)))),k1_xboole_0)
    | spl8_1 ),
    inference(superposition,[],[f47,f70])).

fof(f70,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | r2_hidden(k4_tarski(sK0(k1_relat_1(X0)),sK3(X0,sK0(k1_relat_1(X0)))),X0) ) ),
    inference(resolution,[],[f68,f29])).

fof(f68,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | r2_hidden(k4_tarski(sK0(k1_relat_1(X0)),sK3(X0,sK0(k1_relat_1(X0)))),X0) ) ),
    inference(resolution,[],[f42,f31])).

fof(f42,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f18,f17,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

% (1923)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f47,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f65,plain,
    ( spl8_5
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f61,f58,f53,f63])).

fof(f53,plain,
    ( spl8_3
  <=> v1_xboole_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f58,plain,
    ( spl8_4
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f61,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(superposition,[],[f54,f59])).

fof(f59,plain,
    ( k1_xboole_0 = sK7
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f54,plain,
    ( v1_xboole_0(sK7)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f60,plain,
    ( spl8_4
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f56,f53,f58])).

fof(f56,plain,
    ( k1_xboole_0 = sK7
    | ~ spl8_3 ),
    inference(resolution,[],[f29,f54])).

fof(f55,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f40,f53])).

fof(f40,plain,(
    v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    v1_xboole_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f3,f26])).

% (1922)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f26,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK7) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f51,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f28,f49,f46])).

fof(f28,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:54:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (1914)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.46  % (1921)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.46  % (1912)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (1921)Refutation not found, incomplete strategy% (1921)------------------------------
% 0.21/0.47  % (1921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (1912)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (1921)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (1921)Memory used [KB]: 1535
% 0.21/0.47  % (1921)Time elapsed: 0.063 s
% 0.21/0.47  % (1921)------------------------------
% 0.21/0.47  % (1921)------------------------------
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f51,f55,f60,f65,f79,f91,f111,f136])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    ~spl8_5 | ~spl8_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f121,f77,f63])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl8_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    spl8_6 <=> r2_hidden(k4_tarski(sK0(k1_relat_1(k1_xboole_0)),sK3(k1_xboole_0,sK0(k1_relat_1(k1_xboole_0)))),k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    ~v1_xboole_0(k1_xboole_0) | ~spl8_6),
% 0.21/0.47    inference(resolution,[],[f78,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.47    inference(rectify,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.47    inference(nnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    r2_hidden(k4_tarski(sK0(k1_relat_1(k1_xboole_0)),sK3(k1_xboole_0,sK0(k1_relat_1(k1_xboole_0)))),k1_xboole_0) | ~spl8_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f77])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    ~spl8_5 | ~spl8_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f95,f89,f63])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    spl8_7 <=> r2_hidden(k4_tarski(sK6(k1_xboole_0,sK0(k2_relat_1(k1_xboole_0))),sK0(k2_relat_1(k1_xboole_0))),k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    ~v1_xboole_0(k1_xboole_0) | ~spl8_7),
% 0.21/0.47    inference(resolution,[],[f90,f30])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    r2_hidden(k4_tarski(sK6(k1_xboole_0,sK0(k2_relat_1(k1_xboole_0))),sK0(k2_relat_1(k1_xboole_0))),k1_xboole_0) | ~spl8_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f89])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    spl8_7 | spl8_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f87,f49,f89])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    spl8_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    r2_hidden(k4_tarski(sK6(k1_xboole_0,sK0(k2_relat_1(k1_xboole_0))),sK0(k2_relat_1(k1_xboole_0))),k1_xboole_0) | spl8_2),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f86])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    k1_xboole_0 != k1_xboole_0 | r2_hidden(k4_tarski(sK6(k1_xboole_0,sK0(k2_relat_1(k1_xboole_0))),sK0(k2_relat_1(k1_xboole_0))),k1_xboole_0) | spl8_2),
% 0.21/0.47    inference(superposition,[],[f50,f71])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | r2_hidden(k4_tarski(sK6(X0,sK0(k2_relat_1(X0))),sK0(k2_relat_1(X0))),X0)) )),
% 0.21/0.47    inference(resolution,[],[f69,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | r2_hidden(k4_tarski(sK6(X0,sK0(k2_relat_1(X0))),sK0(k2_relat_1(X0))),X0)) )),
% 0.21/0.47    inference(resolution,[],[f44,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(sK0(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X0,X5] : (~r2_hidden(X5,k2_relat_1(X0)) | r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f21,f24,f23,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) => r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.47    inference(rectify,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.21/0.47    inference(nnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    k1_xboole_0 != k2_relat_1(k1_xboole_0) | spl8_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f49])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    spl8_6 | spl8_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f75,f46,f77])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    spl8_1 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    r2_hidden(k4_tarski(sK0(k1_relat_1(k1_xboole_0)),sK3(k1_xboole_0,sK0(k1_relat_1(k1_xboole_0)))),k1_xboole_0) | spl8_1),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f72])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    k1_xboole_0 != k1_xboole_0 | r2_hidden(k4_tarski(sK0(k1_relat_1(k1_xboole_0)),sK3(k1_xboole_0,sK0(k1_relat_1(k1_xboole_0)))),k1_xboole_0) | spl8_1),
% 0.21/0.47    inference(superposition,[],[f47,f70])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | r2_hidden(k4_tarski(sK0(k1_relat_1(X0)),sK3(X0,sK0(k1_relat_1(X0)))),X0)) )),
% 0.21/0.47    inference(resolution,[],[f68,f29])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | r2_hidden(k4_tarski(sK0(k1_relat_1(X0)),sK3(X0,sK0(k1_relat_1(X0)))),X0)) )),
% 0.21/0.47    inference(resolution,[],[f42,f31])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0,X5] : (~r2_hidden(X5,k1_relat_1(X0)) | r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f18,f17,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK1(X0,X1),X3),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  % (1923)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.47    inference(rectify,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.47    inference(nnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl8_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f46])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    spl8_5 | ~spl8_3 | ~spl8_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f61,f58,f53,f63])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl8_3 <=> v1_xboole_0(sK7)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl8_4 <=> k1_xboole_0 = sK7),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0) | (~spl8_3 | ~spl8_4)),
% 0.21/0.47    inference(superposition,[],[f54,f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    k1_xboole_0 = sK7 | ~spl8_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f58])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    v1_xboole_0(sK7) | ~spl8_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f53])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    spl8_4 | ~spl8_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f56,f53,f58])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    k1_xboole_0 = sK7 | ~spl8_3),
% 0.21/0.47    inference(resolution,[],[f29,f54])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    spl8_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f40,f53])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    v1_xboole_0(sK7)),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    v1_xboole_0(sK7)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f3,f26])).
% 0.21/0.47  % (1922)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK7)),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ? [X0] : v1_xboole_0(X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ~spl8_1 | ~spl8_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f28,f49,f46])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,negated_conjecture,(
% 0.21/0.47    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.21/0.47    inference(negated_conjecture,[],[f6])).
% 0.21/0.47  fof(f6,conjecture,(
% 0.21/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (1912)------------------------------
% 0.21/0.47  % (1912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (1912)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (1912)Memory used [KB]: 10618
% 0.21/0.47  % (1912)Time elapsed: 0.065 s
% 0.21/0.47  % (1912)------------------------------
% 0.21/0.47  % (1912)------------------------------
% 0.21/0.47  % (1923)Refutation not found, incomplete strategy% (1923)------------------------------
% 0.21/0.47  % (1923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (1923)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (1923)Memory used [KB]: 6140
% 0.21/0.47  % (1923)Time elapsed: 0.066 s
% 0.21/0.47  % (1923)------------------------------
% 0.21/0.47  % (1923)------------------------------
% 0.21/0.47  % (1905)Success in time 0.121 s
%------------------------------------------------------------------------------
