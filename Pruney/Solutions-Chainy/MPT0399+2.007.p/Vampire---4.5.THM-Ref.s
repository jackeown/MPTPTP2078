%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 (  80 expanded)
%              Number of leaves         :   16 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :  156 ( 212 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f60,f72,f84,f90,f109])).

fof(f109,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f98,f61])).

fof(f61,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f59,f31])).

fof(f31,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
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

fof(f59,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl5_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f98,plain,
    ( r2_hidden(sK4(k1_xboole_0,sK2(sK1)),k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f71,f89,f34])).

fof(f34,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(sK4(X0,X4),X0)
      | ~ r2_hidden(X4,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(sK3(X0,X1),X3)
              | ~ r2_hidden(X3,X0) )
          & r2_hidden(sK3(X0,X1),X1) ) )
      & ( ! [X4] :
            ( ( r1_tarski(X4,sK4(X0,X4))
              & r2_hidden(sK4(X0,X4),X0) )
            | ~ r2_hidden(X4,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f21,f23,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X0) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK3(X0,X1),X3)
            | ~ r2_hidden(X3,X0) )
        & r2_hidden(sK3(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X0) )
     => ( r1_tarski(X4,sK4(X0,X4))
        & r2_hidden(sK4(X0,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X0) )
            & r2_hidden(X2,X1) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X4,X5)
                & r2_hidden(X5,X0) )
            | ~ r2_hidden(X4,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_tarski(X2,X3)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X0) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f89,plain,
    ( r2_hidden(sK2(sK1),sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl5_6
  <=> r2_hidden(sK2(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f71,plain,
    ( sP0(k1_xboole_0,sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl5_4
  <=> sP0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f90,plain,
    ( spl5_6
    | spl5_5 ),
    inference(avatar_split_clause,[],[f85,f80,f87])).

fof(f80,plain,
    ( spl5_5
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f85,plain,
    ( r2_hidden(sK2(sK1),sK1)
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f82,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f82,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f84,plain,
    ( ~ spl5_5
    | spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f77,f57,f47,f80])).

fof(f47,plain,
    ( spl5_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f77,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_1
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f59,f49,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f49,plain,
    ( k1_xboole_0 != sK1
    | spl5_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f72,plain,
    ( spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f67,f52,f69])).

fof(f52,plain,
    ( spl5_2
  <=> r1_setfam_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f67,plain,
    ( sP0(k1_xboole_0,sK1)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f54,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ~ sP0(X1,X0) )
      & ( sP0(X1,X0)
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> sP0(X1,X0) ) ),
    inference(definition_folding,[],[f10,f12])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f54,plain,
    ( r1_setfam_1(sK1,k1_xboole_0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f60,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f30,f57])).

fof(f30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f55,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f28,f52])).

fof(f28,plain,(
    r1_setfam_1(sK1,k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_xboole_0 != sK1
    & r1_setfam_1(sK1,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & r1_setfam_1(X0,k1_xboole_0) )
   => ( k1_xboole_0 != sK1
      & r1_setfam_1(sK1,k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( r1_setfam_1(X0,k1_xboole_0)
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

fof(f50,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f29,f47])).

fof(f29,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:18:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (7142)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.43  % (7142)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f110,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f50,f55,f60,f72,f84,f90,f109])).
% 0.21/0.43  fof(f109,plain,(
% 0.21/0.43    ~spl5_3 | ~spl5_4 | ~spl5_6),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f108])).
% 0.21/0.43  fof(f108,plain,(
% 0.21/0.43    $false | (~spl5_3 | ~spl5_4 | ~spl5_6)),
% 0.21/0.43    inference(subsumption_resolution,[],[f98,f61])).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl5_3),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f59,f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.43    inference(rectify,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.43    inference(nnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0) | ~spl5_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f57])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    spl5_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.43  fof(f98,plain,(
% 0.21/0.43    r2_hidden(sK4(k1_xboole_0,sK2(sK1)),k1_xboole_0) | (~spl5_4 | ~spl5_6)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f71,f89,f34])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ( ! [X4,X0,X1] : (r2_hidden(sK4(X0,X4),X0) | ~r2_hidden(X4,X1) | ~sP0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ! [X0,X1] : ((sP0(X0,X1) | (! [X3] : (~r1_tarski(sK3(X0,X1),X3) | ~r2_hidden(X3,X0)) & r2_hidden(sK3(X0,X1),X1))) & (! [X4] : ((r1_tarski(X4,sK4(X0,X4)) & r2_hidden(sK4(X0,X4),X0)) | ~r2_hidden(X4,X1)) | ~sP0(X0,X1)))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f21,f23,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X0)) & r2_hidden(X2,X1)) => (! [X3] : (~r1_tarski(sK3(X0,X1),X3) | ~r2_hidden(X3,X0)) & r2_hidden(sK3(X0,X1),X1)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ! [X4,X0] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X0)) => (r1_tarski(X4,sK4(X0,X4)) & r2_hidden(sK4(X0,X4),X0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X0)) & r2_hidden(X2,X1))) & (! [X4] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X0)) | ~r2_hidden(X4,X1)) | ~sP0(X0,X1)))),
% 0.21/0.43    inference(rectify,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0))) & (! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)) | ~sP0(X1,X0)))),
% 0.21/0.43    inference(nnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)))),
% 0.21/0.43    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.43  fof(f89,plain,(
% 0.21/0.43    r2_hidden(sK2(sK1),sK1) | ~spl5_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f87])).
% 0.21/0.43  fof(f87,plain,(
% 0.21/0.43    spl5_6 <=> r2_hidden(sK2(sK1),sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    sP0(k1_xboole_0,sK1) | ~spl5_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f69])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    spl5_4 <=> sP0(k1_xboole_0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.43  fof(f90,plain,(
% 0.21/0.43    spl5_6 | spl5_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f85,f80,f87])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    spl5_5 <=> v1_xboole_0(sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    r2_hidden(sK2(sK1),sK1) | spl5_5),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f82,f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    ~v1_xboole_0(sK1) | spl5_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f80])).
% 0.21/0.43  fof(f84,plain,(
% 0.21/0.43    ~spl5_5 | spl5_1 | ~spl5_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f77,f57,f47,f80])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    spl5_1 <=> k1_xboole_0 = sK1),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.43  fof(f77,plain,(
% 0.21/0.43    ~v1_xboole_0(sK1) | (spl5_1 | ~spl5_3)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f59,f49,f43])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    ( ! [X0,X1] : (X0 = X1 | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    k1_xboole_0 != sK1 | spl5_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f47])).
% 0.21/0.43  fof(f72,plain,(
% 0.21/0.43    spl5_4 | ~spl5_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f67,f52,f69])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    spl5_2 <=> r1_setfam_1(sK1,k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    sP0(k1_xboole_0,sK1) | ~spl5_2),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f54,f38])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    ( ! [X0,X1] : (sP0(X1,X0) | ~r1_setfam_1(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ! [X0,X1] : ((r1_setfam_1(X0,X1) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~r1_setfam_1(X0,X1)))),
% 0.21/0.43    inference(nnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> sP0(X1,X0))),
% 0.21/0.43    inference(definition_folding,[],[f10,f12])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    r1_setfam_1(sK1,k1_xboole_0) | ~spl5_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f52])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    spl5_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f30,f57])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    spl5_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f28,f52])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    r1_setfam_1(sK1,k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    k1_xboole_0 != sK1 & r1_setfam_1(sK1,k1_xboole_0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0)) => (k1_xboole_0 != sK1 & r1_setfam_1(sK1,k1_xboole_0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,negated_conjecture,(
% 0.21/0.43    ~! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.43    inference(negated_conjecture,[],[f7])).
% 0.21/0.43  fof(f7,conjecture,(
% 0.21/0.43    ! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    ~spl5_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f29,f47])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    k1_xboole_0 != sK1),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (7142)------------------------------
% 0.21/0.43  % (7142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (7142)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (7142)Memory used [KB]: 10618
% 0.21/0.43  % (7142)Time elapsed: 0.006 s
% 0.21/0.43  % (7142)------------------------------
% 0.21/0.43  % (7142)------------------------------
% 0.21/0.43  % (7125)Success in time 0.07 s
%------------------------------------------------------------------------------
