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
% DateTime   : Thu Dec  3 12:58:13 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   54 (  96 expanded)
%              Number of leaves         :   16 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  202 ( 334 expanded)
%              Number of equality atoms :   53 (  94 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f42,f46,f50,f55,f60,f65,f70,f75])).

fof(f75,plain,
    ( ~ spl10_6
    | ~ spl10_8
    | spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f72,f40,f36,f68,f58])).

fof(f58,plain,
    ( spl10_6
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f68,plain,
    ( spl10_8
  <=> r2_hidden(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f36,plain,
    ( spl10_1
  <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f40,plain,
    ( spl10_2
  <=> sK0 = k4_tarski(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f72,plain,
    ( ~ r2_hidden(sK4,sK2)
    | ~ r2_hidden(sK3,sK1)
    | spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f71,f37])).

fof(f37,plain,
    ( ~ r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK0,k2_zfmisc_1(X0,X1))
        | ~ r2_hidden(sK4,X1)
        | ~ r2_hidden(sK3,X0) )
    | ~ spl10_2 ),
    inference(superposition,[],[f31,f41])).

fof(f41,plain,
    ( sK0 = k4_tarski(sK3,sK4)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f31,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f11,f14,f13,f12])).

fof(f12,plain,(
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

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK5(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2))
        & r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(sK6(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8
        & r2_hidden(sK9(X0,X1,X8),X1)
        & r2_hidden(sK8(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
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
    inference(rectify,[],[f10])).

fof(f10,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f70,plain,
    ( spl10_8
    | ~ spl10_3
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f66,f63,f44,f68])).

fof(f44,plain,
    ( spl10_3
  <=> r2_hidden(k2_mcart_1(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f63,plain,
    ( spl10_7
  <=> k2_mcart_1(sK0) = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f66,plain,
    ( r2_hidden(sK4,sK2)
    | ~ spl10_3
    | ~ spl10_7 ),
    inference(superposition,[],[f45,f64])).

fof(f64,plain,
    ( k2_mcart_1(sK0) = sK4
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f45,plain,
    ( r2_hidden(k2_mcart_1(sK0),sK2)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f65,plain,
    ( spl10_7
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f61,f40,f63])).

fof(f61,plain,
    ( k2_mcart_1(sK0) = sK4
    | ~ spl10_2 ),
    inference(superposition,[],[f21,f41])).

fof(f21,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f60,plain,
    ( spl10_6
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f56,f53,f48,f58])).

fof(f48,plain,
    ( spl10_4
  <=> r2_hidden(k1_mcart_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f53,plain,
    ( spl10_5
  <=> k1_mcart_1(sK0) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f56,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(superposition,[],[f49,f54])).

fof(f54,plain,
    ( k1_mcart_1(sK0) = sK3
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f49,plain,
    ( r2_hidden(k1_mcart_1(sK0),sK1)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f55,plain,
    ( spl10_5
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f51,f40,f53])).

fof(f51,plain,
    ( k1_mcart_1(sK0) = sK3
    | ~ spl10_2 ),
    inference(superposition,[],[f20,f41])).

fof(f20,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f50,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f16,f48])).

fof(f16,plain,(
    r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ~ r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    & sK0 = k4_tarski(sK3,sK4)
    & r2_hidden(k2_mcart_1(sK0),sK2)
    & r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f6,f8,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
        & ? [X3,X4] : k4_tarski(X3,X4) = X0
        & r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
   => ( ~ r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
      & ? [X4,X3] : k4_tarski(X3,X4) = sK0
      & r2_hidden(k2_mcart_1(sK0),sK2)
      & r2_hidden(k1_mcart_1(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( ? [X4,X3] : k4_tarski(X3,X4) = sK0
   => sK0 = k4_tarski(sK3,sK4) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      & ? [X3,X4] : k4_tarski(X3,X4) = X0
      & r2_hidden(k2_mcart_1(X0),X2)
      & r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      & ? [X3,X4] : k4_tarski(X3,X4) = X0
      & r2_hidden(k2_mcart_1(X0),X2)
      & r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(k2_mcart_1(X0),X2)
          & r2_hidden(k1_mcart_1(X0),X1) )
       => ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
          | ! [X3,X4] : k4_tarski(X3,X4) != X0 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
     => ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | ! [X3,X4] : k4_tarski(X3,X4) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_mcart_1)).

fof(f46,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f17,f44])).

fof(f17,plain,(
    r2_hidden(k2_mcart_1(sK0),sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f42,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f18,f40])).

fof(f18,plain,(
    sK0 = k4_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f9])).

fof(f38,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f19,f36])).

fof(f19,plain,(
    ~ r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n010.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 09:35:59 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.40  % (28933)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.18/0.40  % (28933)Refutation found. Thanks to Tanya!
% 0.18/0.40  % SZS status Theorem for theBenchmark
% 0.18/0.40  % SZS output start Proof for theBenchmark
% 0.18/0.40  fof(f76,plain,(
% 0.18/0.40    $false),
% 0.18/0.40    inference(avatar_sat_refutation,[],[f38,f42,f46,f50,f55,f60,f65,f70,f75])).
% 0.18/0.40  fof(f75,plain,(
% 0.18/0.40    ~spl10_6 | ~spl10_8 | spl10_1 | ~spl10_2),
% 0.18/0.40    inference(avatar_split_clause,[],[f72,f40,f36,f68,f58])).
% 0.18/0.40  fof(f58,plain,(
% 0.18/0.40    spl10_6 <=> r2_hidden(sK3,sK1)),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.18/0.40  fof(f68,plain,(
% 0.18/0.40    spl10_8 <=> r2_hidden(sK4,sK2)),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.18/0.40  fof(f36,plain,(
% 0.18/0.40    spl10_1 <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.18/0.40  fof(f40,plain,(
% 0.18/0.40    spl10_2 <=> sK0 = k4_tarski(sK3,sK4)),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.18/0.40  fof(f72,plain,(
% 0.18/0.40    ~r2_hidden(sK4,sK2) | ~r2_hidden(sK3,sK1) | (spl10_1 | ~spl10_2)),
% 0.18/0.40    inference(resolution,[],[f71,f37])).
% 0.18/0.40  fof(f37,plain,(
% 0.18/0.40    ~r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) | spl10_1),
% 0.18/0.40    inference(avatar_component_clause,[],[f36])).
% 0.18/0.40  fof(f71,plain,(
% 0.18/0.40    ( ! [X0,X1] : (r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | ~r2_hidden(sK4,X1) | ~r2_hidden(sK3,X0)) ) | ~spl10_2),
% 0.18/0.40    inference(superposition,[],[f31,f41])).
% 0.18/0.40  fof(f41,plain,(
% 0.18/0.40    sK0 = k4_tarski(sK3,sK4) | ~spl10_2),
% 0.18/0.40    inference(avatar_component_clause,[],[f40])).
% 0.18/0.40  fof(f31,plain,(
% 0.18/0.40    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 0.18/0.40    inference(equality_resolution,[],[f30])).
% 0.18/0.40  fof(f30,plain,(
% 0.18/0.40    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.18/0.40    inference(equality_resolution,[],[f25])).
% 0.18/0.40  fof(f25,plain,(
% 0.18/0.40    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.18/0.40    inference(cnf_transformation,[],[f15])).
% 0.18/0.40  fof(f15,plain,(
% 0.18/0.40    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK5(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8 & r2_hidden(sK9(X0,X1,X8),X1) & r2_hidden(sK8(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.18/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f11,f14,f13,f12])).
% 0.18/0.40  fof(f12,plain,(
% 0.18/0.40    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK5(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK5(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.18/0.40    introduced(choice_axiom,[])).
% 0.18/0.40  fof(f13,plain,(
% 0.18/0.40    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK5(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)))),
% 0.18/0.40    introduced(choice_axiom,[])).
% 0.18/0.40  fof(f14,plain,(
% 0.18/0.40    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8 & r2_hidden(sK9(X0,X1,X8),X1) & r2_hidden(sK8(X0,X1,X8),X0)))),
% 0.18/0.40    introduced(choice_axiom,[])).
% 0.18/0.40  fof(f11,plain,(
% 0.18/0.40    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.18/0.40    inference(rectify,[],[f10])).
% 0.18/0.40  fof(f10,plain,(
% 0.18/0.40    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 0.18/0.40    inference(nnf_transformation,[],[f1])).
% 0.18/0.40  fof(f1,axiom,(
% 0.18/0.40    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.18/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.18/0.40  fof(f70,plain,(
% 0.18/0.40    spl10_8 | ~spl10_3 | ~spl10_7),
% 0.18/0.40    inference(avatar_split_clause,[],[f66,f63,f44,f68])).
% 0.18/0.40  fof(f44,plain,(
% 0.18/0.40    spl10_3 <=> r2_hidden(k2_mcart_1(sK0),sK2)),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.18/0.40  fof(f63,plain,(
% 0.18/0.40    spl10_7 <=> k2_mcart_1(sK0) = sK4),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.18/0.40  fof(f66,plain,(
% 0.18/0.40    r2_hidden(sK4,sK2) | (~spl10_3 | ~spl10_7)),
% 0.18/0.40    inference(superposition,[],[f45,f64])).
% 0.18/0.40  fof(f64,plain,(
% 0.18/0.40    k2_mcart_1(sK0) = sK4 | ~spl10_7),
% 0.18/0.40    inference(avatar_component_clause,[],[f63])).
% 0.18/0.40  fof(f45,plain,(
% 0.18/0.40    r2_hidden(k2_mcart_1(sK0),sK2) | ~spl10_3),
% 0.18/0.40    inference(avatar_component_clause,[],[f44])).
% 0.18/0.40  fof(f65,plain,(
% 0.18/0.40    spl10_7 | ~spl10_2),
% 0.18/0.40    inference(avatar_split_clause,[],[f61,f40,f63])).
% 0.18/0.40  fof(f61,plain,(
% 0.18/0.40    k2_mcart_1(sK0) = sK4 | ~spl10_2),
% 0.18/0.40    inference(superposition,[],[f21,f41])).
% 0.18/0.40  fof(f21,plain,(
% 0.18/0.40    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.18/0.40    inference(cnf_transformation,[],[f2])).
% 0.18/0.40  fof(f2,axiom,(
% 0.18/0.40    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.18/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.18/0.40  fof(f60,plain,(
% 0.18/0.40    spl10_6 | ~spl10_4 | ~spl10_5),
% 0.18/0.40    inference(avatar_split_clause,[],[f56,f53,f48,f58])).
% 0.18/0.40  fof(f48,plain,(
% 0.18/0.40    spl10_4 <=> r2_hidden(k1_mcart_1(sK0),sK1)),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.18/0.40  fof(f53,plain,(
% 0.18/0.40    spl10_5 <=> k1_mcart_1(sK0) = sK3),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.18/0.40  fof(f56,plain,(
% 0.18/0.40    r2_hidden(sK3,sK1) | (~spl10_4 | ~spl10_5)),
% 0.18/0.40    inference(superposition,[],[f49,f54])).
% 0.18/0.40  fof(f54,plain,(
% 0.18/0.40    k1_mcart_1(sK0) = sK3 | ~spl10_5),
% 0.18/0.40    inference(avatar_component_clause,[],[f53])).
% 0.18/0.40  fof(f49,plain,(
% 0.18/0.40    r2_hidden(k1_mcart_1(sK0),sK1) | ~spl10_4),
% 0.18/0.40    inference(avatar_component_clause,[],[f48])).
% 0.18/0.40  fof(f55,plain,(
% 0.18/0.40    spl10_5 | ~spl10_2),
% 0.18/0.40    inference(avatar_split_clause,[],[f51,f40,f53])).
% 0.18/0.40  fof(f51,plain,(
% 0.18/0.40    k1_mcart_1(sK0) = sK3 | ~spl10_2),
% 0.18/0.40    inference(superposition,[],[f20,f41])).
% 0.18/0.40  fof(f20,plain,(
% 0.18/0.40    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.18/0.40    inference(cnf_transformation,[],[f2])).
% 0.18/0.40  fof(f50,plain,(
% 0.18/0.40    spl10_4),
% 0.18/0.40    inference(avatar_split_clause,[],[f16,f48])).
% 0.18/0.40  fof(f16,plain,(
% 0.18/0.40    r2_hidden(k1_mcart_1(sK0),sK1)),
% 0.18/0.40    inference(cnf_transformation,[],[f9])).
% 0.18/0.40  fof(f9,plain,(
% 0.18/0.40    ~r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) & sK0 = k4_tarski(sK3,sK4) & r2_hidden(k2_mcart_1(sK0),sK2) & r2_hidden(k1_mcart_1(sK0),sK1)),
% 0.18/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f6,f8,f7])).
% 0.18/0.40  fof(f7,plain,(
% 0.18/0.40    ? [X0,X1,X2] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) & ? [X3,X4] : k4_tarski(X3,X4) = X0 & r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) => (~r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) & ? [X4,X3] : k4_tarski(X3,X4) = sK0 & r2_hidden(k2_mcart_1(sK0),sK2) & r2_hidden(k1_mcart_1(sK0),sK1))),
% 0.18/0.40    introduced(choice_axiom,[])).
% 0.18/0.40  fof(f8,plain,(
% 0.18/0.40    ? [X4,X3] : k4_tarski(X3,X4) = sK0 => sK0 = k4_tarski(sK3,sK4)),
% 0.18/0.40    introduced(choice_axiom,[])).
% 0.18/0.40  fof(f6,plain,(
% 0.18/0.40    ? [X0,X1,X2] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) & ? [X3,X4] : k4_tarski(X3,X4) = X0 & r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1))),
% 0.18/0.40    inference(flattening,[],[f5])).
% 0.18/0.40  fof(f5,plain,(
% 0.18/0.40    ? [X0,X1,X2] : ((~r2_hidden(X0,k2_zfmisc_1(X1,X2)) & ? [X3,X4] : k4_tarski(X3,X4) = X0) & (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.18/0.40    inference(ennf_transformation,[],[f4])).
% 0.18/0.40  fof(f4,negated_conjecture,(
% 0.18/0.40    ~! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) => (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0))),
% 0.18/0.40    inference(negated_conjecture,[],[f3])).
% 0.18/0.40  fof(f3,conjecture,(
% 0.18/0.40    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) => (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0))),
% 0.18/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_mcart_1)).
% 0.18/0.40  fof(f46,plain,(
% 0.18/0.40    spl10_3),
% 0.18/0.40    inference(avatar_split_clause,[],[f17,f44])).
% 0.18/0.40  fof(f17,plain,(
% 0.18/0.40    r2_hidden(k2_mcart_1(sK0),sK2)),
% 0.18/0.40    inference(cnf_transformation,[],[f9])).
% 0.18/0.40  fof(f42,plain,(
% 0.18/0.40    spl10_2),
% 0.18/0.40    inference(avatar_split_clause,[],[f18,f40])).
% 0.18/0.40  fof(f18,plain,(
% 0.18/0.40    sK0 = k4_tarski(sK3,sK4)),
% 0.18/0.40    inference(cnf_transformation,[],[f9])).
% 0.18/0.40  fof(f38,plain,(
% 0.18/0.40    ~spl10_1),
% 0.18/0.40    inference(avatar_split_clause,[],[f19,f36])).
% 0.18/0.40  fof(f19,plain,(
% 0.18/0.40    ~r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.18/0.40    inference(cnf_transformation,[],[f9])).
% 0.18/0.40  % SZS output end Proof for theBenchmark
% 0.18/0.40  % (28933)------------------------------
% 0.18/0.40  % (28933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.40  % (28933)Termination reason: Refutation
% 0.18/0.40  
% 0.18/0.40  % (28933)Memory used [KB]: 10618
% 0.18/0.40  % (28933)Time elapsed: 0.029 s
% 0.18/0.40  % (28933)------------------------------
% 0.18/0.40  % (28933)------------------------------
% 0.18/0.40  % (28924)Success in time 0.061 s
%------------------------------------------------------------------------------
