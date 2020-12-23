%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:06 EST 2020

% Result     : Theorem 2.55s
% Output     : Refutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 601 expanded)
%              Number of leaves         :   31 ( 249 expanded)
%              Depth                    :   11
%              Number of atoms          :  643 (2617 expanded)
%              Number of equality atoms :   98 ( 615 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2647,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f169,f174,f179,f180,f181,f182,f311,f757,f790,f2024,f2025,f2026,f2068,f2069,f2070,f2123,f2144,f2145,f2465,f2486,f2487,f2488,f2491,f2560,f2598,f2607,f2646])).

fof(f2646,plain,
    ( ~ spl18_5
    | ~ spl18_9 ),
    inference(avatar_contradiction_clause,[],[f2634])).

fof(f2634,plain,
    ( $false
    | ~ spl18_5
    | ~ spl18_9 ),
    inference(resolution,[],[f2032,f173])).

fof(f173,plain,
    ( r2_hidden(sK7(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))
    | ~ spl18_9 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl18_9
  <=> r2_hidden(sK7(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_9])])).

fof(f2032,plain,
    ( ! [X4,X5] : ~ r2_hidden(sK7(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),k2_zfmisc_1(X4,X5))
    | ~ spl18_5 ),
    inference(resolution,[],[f157,f123])).

fof(f123,plain,(
    ! [X0,X8,X1] :
      ( sQ17_eqProxy(k4_tarski(sK13(X0,X1,X8),sK14(X0,X1,X8)),X8)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_proxy_replacement,[],[f103,f106])).

fof(f106,plain,(
    ! [X1,X0] :
      ( sQ17_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ17_eqProxy])])).

fof(f103,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK13(X0,X1,X8),sK14(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK13(X0,X1,X8),sK14(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK10(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK10(X0,X1,X2),X2) )
          & ( ( sK10(X0,X1,X2) = k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2))
              & r2_hidden(sK12(X0,X1,X2),X1)
              & r2_hidden(sK11(X0,X1,X2),X0) )
            | r2_hidden(sK10(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK13(X0,X1,X8),sK14(X0,X1,X8)) = X8
                & r2_hidden(sK14(X0,X1,X8),X1)
                & r2_hidden(sK13(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12,sK13,sK14])],[f38,f41,f40,f39])).

fof(f39,plain,(
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
              ( k4_tarski(X4,X5) != sK10(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK10(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK10(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK10(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK10(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK10(X0,X1,X2) = k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2))
        & r2_hidden(sK12(X0,X1,X2),X1)
        & r2_hidden(sK11(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK13(X0,X1,X8),sK14(X0,X1,X8)) = X8
        & r2_hidden(sK14(X0,X1,X8),X1)
        & r2_hidden(sK13(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f157,plain,
    ( ! [X4,X5] : ~ sQ17_eqProxy(k4_tarski(X4,X5),sK7(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))))
    | ~ spl18_5 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl18_5
  <=> ! [X5,X4] : ~ sQ17_eqProxy(k4_tarski(X4,X5),sK7(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_5])])).

fof(f2607,plain,
    ( ~ spl18_18
    | ~ spl18_20
    | spl18_51 ),
    inference(avatar_split_clause,[],[f2207,f2118,f785,f752])).

fof(f752,plain,
    ( spl18_18
  <=> r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_18])])).

fof(f785,plain,
    ( spl18_20
  <=> r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_20])])).

fof(f2118,plain,
    ( spl18_51
  <=> r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_51])])).

fof(f2207,plain,
    ( ~ r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK3)
    | ~ r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK2)
    | spl18_51 ),
    inference(resolution,[],[f2120,f98])).

fof(f98,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f65,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK9(X0,X1,X2),X1)
            | ~ r2_hidden(sK9(X0,X1,X2),X0)
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK9(X0,X1,X2),X1)
              & r2_hidden(sK9(X0,X1,X2),X0) )
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK9(X0,X1,X2),X1)
          | ~ r2_hidden(sK9(X0,X1,X2),X0)
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK9(X0,X1,X2),X1)
            & r2_hidden(sK9(X0,X1,X2),X0) )
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f2120,plain,
    ( ~ r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | spl18_51 ),
    inference(avatar_component_clause,[],[f2118])).

fof(f2598,plain,
    ( ~ spl18_6
    | ~ spl18_11 ),
    inference(avatar_contradiction_clause,[],[f2583])).

fof(f2583,plain,
    ( $false
    | ~ spl18_6
    | ~ spl18_11 ),
    inference(resolution,[],[f210,f2496])).

fof(f2496,plain,
    ( ! [X4,X5] : ~ r2_hidden(sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k2_zfmisc_1(X4,X5))
    | ~ spl18_6 ),
    inference(resolution,[],[f160,f123])).

fof(f160,plain,
    ( ! [X2,X3] : ~ sQ17_eqProxy(k4_tarski(X2,X3),sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))))
    | ~ spl18_6 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl18_6
  <=> ! [X3,X2] : ~ sQ17_eqProxy(k4_tarski(X2,X3),sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_6])])).

fof(f210,plain,
    ( r2_hidden(sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k2_zfmisc_1(sK0,sK2))
    | ~ spl18_11 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl18_11
  <=> r2_hidden(sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k2_zfmisc_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_11])])).

fof(f2560,plain,
    ( ~ spl18_10
    | spl18_11 ),
    inference(avatar_contradiction_clause,[],[f2539])).

fof(f2539,plain,
    ( $false
    | ~ spl18_10
    | spl18_11 ),
    inference(resolution,[],[f178,f249])).

fof(f249,plain,
    ( ! [X10] : ~ r2_hidden(sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),X10)))
    | spl18_11 ),
    inference(resolution,[],[f211,f100])).

fof(f100,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f63,f51])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f211,plain,
    ( ~ r2_hidden(sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k2_zfmisc_1(sK0,sK2))
    | spl18_11 ),
    inference(avatar_component_clause,[],[f209])).

fof(f178,plain,
    ( r2_hidden(sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))
    | ~ spl18_10 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl18_10
  <=> r2_hidden(sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_10])])).

fof(f2491,plain,
    ( spl18_17
    | ~ spl18_15 ),
    inference(avatar_split_clause,[],[f2446,f304,f748])).

fof(f748,plain,
    ( spl18_17
  <=> r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_17])])).

fof(f304,plain,
    ( spl18_15
  <=> r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_15])])).

fof(f2446,plain,
    ( r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK0)
    | ~ spl18_15 ),
    inference(resolution,[],[f305,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f305,plain,
    ( r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(sK0,sK2))
    | ~ spl18_15 ),
    inference(avatar_component_clause,[],[f304])).

fof(f2488,plain,
    ( ~ spl18_17
    | ~ spl18_19
    | spl18_50 ),
    inference(avatar_split_clause,[],[f2199,f2114,f781,f748])).

fof(f781,plain,
    ( spl18_19
  <=> r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_19])])).

fof(f2114,plain,
    ( spl18_50
  <=> r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_50])])).

fof(f2199,plain,
    ( ~ r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK1)
    | ~ r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK0)
    | spl18_50 ),
    inference(resolution,[],[f2116,f98])).

fof(f2116,plain,
    ( ~ r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl18_50 ),
    inference(avatar_component_clause,[],[f2114])).

fof(f2487,plain,
    ( spl18_20
    | ~ spl18_16 ),
    inference(avatar_split_clause,[],[f2469,f308,f785])).

fof(f308,plain,
    ( spl18_16
  <=> r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_16])])).

fof(f2469,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK3)
    | ~ spl18_16 ),
    inference(resolution,[],[f309,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f309,plain,
    ( r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(sK1,sK3))
    | ~ spl18_16 ),
    inference(avatar_component_clause,[],[f308])).

fof(f2486,plain,
    ( spl18_19
    | ~ spl18_16 ),
    inference(avatar_split_clause,[],[f2468,f308,f781])).

fof(f2468,plain,
    ( r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK1)
    | ~ spl18_16 ),
    inference(resolution,[],[f309,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f2465,plain,
    ( spl18_18
    | ~ spl18_15 ),
    inference(avatar_split_clause,[],[f2449,f304,f752])).

fof(f2449,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK2)
    | ~ spl18_15 ),
    inference(resolution,[],[f305,f79])).

fof(f2145,plain,
    ( spl18_16
    | ~ spl18_8 ),
    inference(avatar_split_clause,[],[f2132,f166,f308])).

fof(f166,plain,
    ( spl18_8
  <=> r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_8])])).

fof(f2132,plain,
    ( r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(sK1,sK3))
    | ~ spl18_8 ),
    inference(resolution,[],[f167,f99])).

fof(f99,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f64,f51])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f167,plain,
    ( r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))
    | ~ spl18_8 ),
    inference(avatar_component_clause,[],[f166])).

fof(f2144,plain,
    ( spl18_15
    | ~ spl18_8 ),
    inference(avatar_split_clause,[],[f2131,f166,f304])).

fof(f2131,plain,
    ( r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(sK0,sK2))
    | ~ spl18_8 ),
    inference(resolution,[],[f167,f100])).

fof(f2123,plain,
    ( ~ spl18_50
    | ~ spl18_51
    | spl18_7 ),
    inference(avatar_split_clause,[],[f2101,f162,f2118,f2114])).

fof(f162,plain,
    ( spl18_7
  <=> r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_7])])).

fof(f2101,plain,
    ( ~ r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | ~ r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl18_7 ),
    inference(resolution,[],[f164,f102])).

fof(f102,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f164,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))
    | spl18_7 ),
    inference(avatar_component_clause,[],[f162])).

fof(f2070,plain,
    ( spl18_19
    | ~ spl18_7 ),
    inference(avatar_split_clause,[],[f489,f162,f781])).

fof(f489,plain,
    ( r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK1)
    | ~ spl18_7 ),
    inference(resolution,[],[f273,f99])).

fof(f273,plain,
    ( r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl18_7 ),
    inference(resolution,[],[f163,f81])).

fof(f163,plain,
    ( r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))
    | ~ spl18_7 ),
    inference(avatar_component_clause,[],[f162])).

fof(f2069,plain,
    ( spl18_18
    | ~ spl18_7 ),
    inference(avatar_split_clause,[],[f510,f162,f752])).

fof(f510,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK2)
    | ~ spl18_7 ),
    inference(resolution,[],[f274,f100])).

fof(f274,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | ~ spl18_7 ),
    inference(resolution,[],[f163,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f2068,plain,
    ( spl18_20
    | ~ spl18_7 ),
    inference(avatar_split_clause,[],[f511,f162,f785])).

fof(f511,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK3)
    | ~ spl18_7 ),
    inference(resolution,[],[f274,f99])).

fof(f2026,plain,
    ( spl18_9
    | spl18_7
    | spl18_8
    | spl18_10 ),
    inference(avatar_split_clause,[],[f1776,f176,f166,f162,f171])).

fof(f1776,plain,
    ( r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))
    | r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))
    | r2_hidden(sK7(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))
    | spl18_10 ),
    inference(resolution,[],[f197,f107])).

fof(f107,plain,(
    ~ sQ17_eqProxy(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))) ),
    inference(equality_proxy_replacement,[],[f87,f106])).

fof(f87,plain,(
    k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))) ),
    inference(definition_unfolding,[],[f49,f51,f51,f51])).

fof(f49,plain,(
    k2_zfmisc_1(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK3)) != k3_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    k2_zfmisc_1(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK3)) != k3_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) != k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
   => k2_zfmisc_1(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK3)) != k3_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) != k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f197,plain,
    ( ! [X0] :
        ( sQ17_eqProxy(X0,k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))
        | r2_hidden(k4_tarski(sK4(X0,k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(X0,k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))
        | r2_hidden(k4_tarski(sK4(X0,k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(X0,k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),X0)
        | r2_hidden(sK7(X0),X0) )
    | spl18_10 ),
    inference(resolution,[],[f177,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( sQ17_eqProxy(X0,X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | r2_hidden(sK6(X1),X1)
      | r2_hidden(sK7(X0),X0) ) ),
    inference(equality_proxy_replacement,[],[f52,f106])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | r2_hidden(sK6(X1),X1)
      | r2_hidden(sK7(X0),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) )
      | ( ! [X5,X6] : k4_tarski(X5,X6) != sK6(X1)
        & r2_hidden(sK6(X1),X1) )
      | ( ! [X8,X9] : k4_tarski(X8,X9) != sK7(X0)
        & r2_hidden(sK7(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f23,f26,f25,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1] :
      ( ? [X4] :
          ( ! [X5,X6] : k4_tarski(X5,X6) != X4
          & r2_hidden(X4,X1) )
     => ( ! [X6,X5] : k4_tarski(X5,X6) != sK6(X1)
        & r2_hidden(sK6(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X7] :
          ( ! [X8,X9] : k4_tarski(X8,X9) != X7
          & r2_hidden(X7,X0) )
     => ( ! [X9,X8] : k4_tarski(X8,X9) != sK7(X0)
        & r2_hidden(sK7(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ? [X4] :
          ( ! [X5,X6] : k4_tarski(X5,X6) != X4
          & r2_hidden(X4,X1) )
      | ? [X7] :
          ( ! [X8,X9] : k4_tarski(X8,X9) != X7
          & r2_hidden(X7,X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2,X3] :
          ( r2_hidden(k4_tarski(X2,X3),X0)
        <~> r2_hidden(k4_tarski(X2,X3),X1) )
      | ? [X4] :
          ( ! [X5,X6] : k4_tarski(X5,X6) != X4
          & r2_hidden(X4,X1) )
      | ? [X7] :
          ( ! [X8,X9] : k4_tarski(X8,X9) != X7
          & r2_hidden(X7,X0) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2,X3] :
          ( r2_hidden(k4_tarski(X2,X3),X0)
        <~> r2_hidden(k4_tarski(X2,X3),X1) )
      | ? [X4] :
          ( ! [X5,X6] : k4_tarski(X5,X6) != X4
          & r2_hidden(X4,X1) )
      | ? [X7] :
          ( ! [X8,X9] : k4_tarski(X8,X9) != X7
          & r2_hidden(X7,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X0)
          <=> r2_hidden(k4_tarski(X2,X3),X1) )
        & ! [X4] :
            ~ ( ! [X5,X6] : k4_tarski(X5,X6) != X4
              & r2_hidden(X4,X1) )
        & ! [X7] :
            ~ ( ! [X8,X9] : k4_tarski(X8,X9) != X7
              & r2_hidden(X7,X0) ) )
     => X0 = X1 ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X0)
          <=> r2_hidden(k4_tarski(X2,X3),X1) )
        & ! [X2] :
            ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X2
              & r2_hidden(X2,X1) )
        & ! [X2] :
            ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X2
              & r2_hidden(X2,X0) ) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l131_zfmisc_1)).

fof(f177,plain,
    ( ~ r2_hidden(sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))
    | spl18_10 ),
    inference(avatar_component_clause,[],[f176])).

fof(f2025,plain,
    ( spl18_5
    | spl18_7
    | spl18_8
    | spl18_10 ),
    inference(avatar_split_clause,[],[f1795,f176,f166,f162,f156])).

fof(f1795,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))
        | r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))
        | ~ sQ17_eqProxy(k4_tarski(X0,X1),sK7(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))) )
    | spl18_10 ),
    inference(resolution,[],[f198,f107])).

fof(f198,plain,
    ( ! [X2,X3,X1] :
        ( sQ17_eqProxy(X1,k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))
        | r2_hidden(k4_tarski(sK4(X1,k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(X1,k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))
        | r2_hidden(k4_tarski(sK4(X1,k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(X1,k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),X1)
        | ~ sQ17_eqProxy(k4_tarski(X2,X3),sK7(X1)) )
    | spl18_10 ),
    inference(resolution,[],[f177,f114])).

fof(f114,plain,(
    ! [X0,X8,X1,X9] :
      ( sQ17_eqProxy(X0,X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | r2_hidden(sK6(X1),X1)
      | ~ sQ17_eqProxy(k4_tarski(X8,X9),sK7(X0)) ) ),
    inference(equality_proxy_replacement,[],[f53,f106,f106])).

fof(f53,plain,(
    ! [X0,X8,X1,X9] :
      ( X0 = X1
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | r2_hidden(sK6(X1),X1)
      | k4_tarski(X8,X9) != sK7(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2024,plain,
    ( ~ spl18_7
    | spl18_17 ),
    inference(avatar_contradiction_clause,[],[f2016])).

fof(f2016,plain,
    ( $false
    | ~ spl18_7
    | spl18_17 ),
    inference(resolution,[],[f750,f488])).

fof(f488,plain,
    ( r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK0)
    | ~ spl18_7 ),
    inference(resolution,[],[f273,f100])).

fof(f750,plain,
    ( ~ r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK0)
    | spl18_17 ),
    inference(avatar_component_clause,[],[f748])).

fof(f790,plain,
    ( ~ spl18_19
    | ~ spl18_20
    | spl18_16 ),
    inference(avatar_split_clause,[],[f772,f308,f785,f781])).

fof(f772,plain,
    ( ~ r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK3)
    | ~ r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK1)
    | spl18_16 ),
    inference(resolution,[],[f310,f102])).

fof(f310,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(sK1,sK3))
    | spl18_16 ),
    inference(avatar_component_clause,[],[f308])).

fof(f757,plain,
    ( ~ spl18_17
    | ~ spl18_18
    | spl18_15 ),
    inference(avatar_split_clause,[],[f739,f304,f752,f748])).

fof(f739,plain,
    ( ~ r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK2)
    | ~ r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK0)
    | spl18_15 ),
    inference(resolution,[],[f306,f102])).

fof(f306,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(sK0,sK2))
    | spl18_15 ),
    inference(avatar_component_clause,[],[f304])).

fof(f311,plain,
    ( ~ spl18_15
    | ~ spl18_16
    | spl18_8 ),
    inference(avatar_split_clause,[],[f291,f166,f308,f304])).

fof(f291,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(sK1,sK3))
    | ~ r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(sK0,sK2))
    | spl18_8 ),
    inference(resolution,[],[f168,f98])).

fof(f168,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))
    | spl18_8 ),
    inference(avatar_component_clause,[],[f166])).

fof(f182,plain,
    ( spl18_9
    | spl18_6
    | spl18_7
    | spl18_8 ),
    inference(avatar_split_clause,[],[f134,f166,f162,f159,f171])).

fof(f134,plain,(
    ! [X14,X15] :
      ( r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))
      | r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))
      | ~ sQ17_eqProxy(k4_tarski(X14,X15),sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))))
      | r2_hidden(sK7(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) ) ),
    inference(resolution,[],[f107,f113])).

fof(f113,plain,(
    ! [X6,X0,X5,X1] :
      ( sQ17_eqProxy(X0,X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | ~ sQ17_eqProxy(k4_tarski(X5,X6),sK6(X1))
      | r2_hidden(sK7(X0),X0) ) ),
    inference(equality_proxy_replacement,[],[f54,f106,f106])).

fof(f54,plain,(
    ! [X6,X0,X5,X1] :
      ( X0 = X1
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | k4_tarski(X5,X6) != sK6(X1)
      | r2_hidden(sK7(X0),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f181,plain,
    ( spl18_5
    | spl18_6
    | spl18_7
    | spl18_8 ),
    inference(avatar_split_clause,[],[f133,f166,f162,f159,f156])).

fof(f133,plain,(
    ! [X12,X10,X13,X11] :
      ( r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))
      | r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))
      | ~ sQ17_eqProxy(k4_tarski(X10,X11),sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))))
      | ~ sQ17_eqProxy(k4_tarski(X12,X13),sK7(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))) ) ),
    inference(resolution,[],[f107,f112])).

fof(f112,plain,(
    ! [X6,X0,X8,X5,X1,X9] :
      ( sQ17_eqProxy(X0,X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | ~ sQ17_eqProxy(k4_tarski(X5,X6),sK6(X1))
      | ~ sQ17_eqProxy(k4_tarski(X8,X9),sK7(X0)) ) ),
    inference(equality_proxy_replacement,[],[f55,f106,f106,f106])).

fof(f55,plain,(
    ! [X6,X0,X8,X5,X1,X9] :
      ( X0 = X1
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | k4_tarski(X5,X6) != sK6(X1)
      | k4_tarski(X8,X9) != sK7(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f180,plain,
    ( spl18_9
    | spl18_10
    | ~ spl18_7
    | ~ spl18_8 ),
    inference(avatar_split_clause,[],[f132,f166,f162,f176,f171])).

fof(f132,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))
    | ~ r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))
    | r2_hidden(sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))
    | r2_hidden(sK7(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) ),
    inference(resolution,[],[f107,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( sQ17_eqProxy(X0,X1)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | r2_hidden(sK6(X1),X1)
      | r2_hidden(sK7(X0),X0) ) ),
    inference(equality_proxy_replacement,[],[f56,f106])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | r2_hidden(sK6(X1),X1)
      | r2_hidden(sK7(X0),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f179,plain,
    ( spl18_5
    | spl18_10
    | ~ spl18_7
    | ~ spl18_8 ),
    inference(avatar_split_clause,[],[f131,f166,f162,f176,f156])).

fof(f131,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))
      | ~ r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))
      | r2_hidden(sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))
      | ~ sQ17_eqProxy(k4_tarski(X8,X9),sK7(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))) ) ),
    inference(resolution,[],[f107,f110])).

fof(f110,plain,(
    ! [X0,X8,X1,X9] :
      ( sQ17_eqProxy(X0,X1)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | r2_hidden(sK6(X1),X1)
      | ~ sQ17_eqProxy(k4_tarski(X8,X9),sK7(X0)) ) ),
    inference(equality_proxy_replacement,[],[f57,f106,f106])).

fof(f57,plain,(
    ! [X0,X8,X1,X9] :
      ( X0 = X1
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | r2_hidden(sK6(X1),X1)
      | k4_tarski(X8,X9) != sK7(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f174,plain,
    ( spl18_9
    | spl18_6
    | ~ spl18_7
    | ~ spl18_8 ),
    inference(avatar_split_clause,[],[f130,f166,f162,f159,f171])).

fof(f130,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))
      | ~ r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))
      | ~ sQ17_eqProxy(k4_tarski(X6,X7),sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))))
      | r2_hidden(sK7(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) ) ),
    inference(resolution,[],[f107,f109])).

fof(f109,plain,(
    ! [X6,X0,X5,X1] :
      ( sQ17_eqProxy(X0,X1)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | ~ sQ17_eqProxy(k4_tarski(X5,X6),sK6(X1))
      | r2_hidden(sK7(X0),X0) ) ),
    inference(equality_proxy_replacement,[],[f58,f106,f106])).

fof(f58,plain,(
    ! [X6,X0,X5,X1] :
      ( X0 = X1
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | k4_tarski(X5,X6) != sK6(X1)
      | r2_hidden(sK7(X0),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f169,plain,
    ( spl18_5
    | spl18_6
    | ~ spl18_7
    | ~ spl18_8 ),
    inference(avatar_split_clause,[],[f129,f166,f162,f159,f156])).

fof(f129,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))
      | ~ r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))
      | ~ sQ17_eqProxy(k4_tarski(X2,X3),sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))))
      | ~ sQ17_eqProxy(k4_tarski(X4,X5),sK7(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))) ) ),
    inference(resolution,[],[f107,f108])).

fof(f108,plain,(
    ! [X6,X0,X8,X5,X1,X9] :
      ( sQ17_eqProxy(X0,X1)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | ~ sQ17_eqProxy(k4_tarski(X5,X6),sK6(X1))
      | ~ sQ17_eqProxy(k4_tarski(X8,X9),sK7(X0)) ) ),
    inference(equality_proxy_replacement,[],[f59,f106,f106,f106])).

fof(f59,plain,(
    ! [X6,X0,X8,X5,X1,X9] :
      ( X0 = X1
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | k4_tarski(X5,X6) != sK6(X1)
      | k4_tarski(X8,X9) != sK7(X0) ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:27:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (32597)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (32589)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (32575)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (32592)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (32574)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (32572)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (32581)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (32581)Refutation not found, incomplete strategy% (32581)------------------------------
% 0.21/0.53  % (32581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32581)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (32581)Memory used [KB]: 10746
% 0.21/0.53  % (32581)Time elapsed: 0.119 s
% 0.21/0.53  % (32581)------------------------------
% 0.21/0.53  % (32581)------------------------------
% 0.21/0.53  % (32592)Refutation not found, incomplete strategy% (32592)------------------------------
% 0.21/0.53  % (32592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32592)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (32592)Memory used [KB]: 1791
% 0.21/0.53  % (32592)Time elapsed: 0.088 s
% 0.21/0.53  % (32592)------------------------------
% 0.21/0.53  % (32592)------------------------------
% 0.21/0.53  % (32570)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (32583)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (32595)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (32572)Refutation not found, incomplete strategy% (32572)------------------------------
% 0.21/0.53  % (32572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32572)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (32572)Memory used [KB]: 10746
% 0.21/0.53  % (32572)Time elapsed: 0.109 s
% 0.21/0.53  % (32572)------------------------------
% 0.21/0.53  % (32572)------------------------------
% 0.21/0.53  % (32593)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (32599)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (32594)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (32591)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (32577)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (32585)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (32600)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (32580)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (32579)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (32576)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (32573)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (32579)Refutation not found, incomplete strategy% (32579)------------------------------
% 0.21/0.54  % (32579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32579)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (32579)Memory used [KB]: 10746
% 0.21/0.54  % (32579)Time elapsed: 0.123 s
% 0.21/0.54  % (32579)------------------------------
% 0.21/0.54  % (32579)------------------------------
% 0.21/0.54  % (32574)Refutation not found, incomplete strategy% (32574)------------------------------
% 0.21/0.54  % (32574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32574)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (32574)Memory used [KB]: 6268
% 0.21/0.54  % (32574)Time elapsed: 0.135 s
% 0.21/0.54  % (32574)------------------------------
% 0.21/0.54  % (32574)------------------------------
% 0.21/0.55  % (32587)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (32571)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (32588)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (32582)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (32584)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (32596)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (32596)Refutation not found, incomplete strategy% (32596)------------------------------
% 0.21/0.56  % (32596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (32596)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (32596)Memory used [KB]: 6268
% 0.21/0.56  % (32596)Time elapsed: 0.147 s
% 0.21/0.56  % (32596)------------------------------
% 0.21/0.56  % (32596)------------------------------
% 0.21/0.56  % (32598)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % (32586)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (32590)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (32591)Refutation not found, incomplete strategy% (32591)------------------------------
% 0.21/0.56  % (32591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (32591)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (32591)Memory used [KB]: 10746
% 0.21/0.56  % (32591)Time elapsed: 0.145 s
% 0.21/0.56  % (32591)------------------------------
% 0.21/0.56  % (32591)------------------------------
% 2.07/0.66  % (32629)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.07/0.67  % (32630)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.07/0.67  % (32640)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.07/0.68  % (32641)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.07/0.69  % (32646)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.07/0.70  % (32650)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.07/0.70  % (32645)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.55/0.73  % (32586)Refutation found. Thanks to Tanya!
% 2.55/0.73  % SZS status Theorem for theBenchmark
% 2.55/0.73  % SZS output start Proof for theBenchmark
% 2.55/0.73  fof(f2647,plain,(
% 2.55/0.73    $false),
% 2.55/0.73    inference(avatar_sat_refutation,[],[f169,f174,f179,f180,f181,f182,f311,f757,f790,f2024,f2025,f2026,f2068,f2069,f2070,f2123,f2144,f2145,f2465,f2486,f2487,f2488,f2491,f2560,f2598,f2607,f2646])).
% 2.55/0.73  fof(f2646,plain,(
% 2.55/0.73    ~spl18_5 | ~spl18_9),
% 2.55/0.73    inference(avatar_contradiction_clause,[],[f2634])).
% 2.55/0.73  fof(f2634,plain,(
% 2.55/0.73    $false | (~spl18_5 | ~spl18_9)),
% 2.55/0.73    inference(resolution,[],[f2032,f173])).
% 2.55/0.73  fof(f173,plain,(
% 2.55/0.73    r2_hidden(sK7(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) | ~spl18_9),
% 2.55/0.73    inference(avatar_component_clause,[],[f171])).
% 2.55/0.73  fof(f171,plain,(
% 2.55/0.73    spl18_9 <=> r2_hidden(sK7(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))),
% 2.55/0.73    introduced(avatar_definition,[new_symbols(naming,[spl18_9])])).
% 2.55/0.73  fof(f2032,plain,(
% 2.55/0.73    ( ! [X4,X5] : (~r2_hidden(sK7(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),k2_zfmisc_1(X4,X5))) ) | ~spl18_5),
% 2.55/0.73    inference(resolution,[],[f157,f123])).
% 2.55/0.73  fof(f123,plain,(
% 2.55/0.73    ( ! [X0,X8,X1] : (sQ17_eqProxy(k4_tarski(sK13(X0,X1,X8),sK14(X0,X1,X8)),X8) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 2.55/0.73    inference(equality_proxy_replacement,[],[f103,f106])).
% 2.55/0.73  fof(f106,plain,(
% 2.55/0.73    ! [X1,X0] : (sQ17_eqProxy(X0,X1) <=> X0 = X1)),
% 2.55/0.73    introduced(equality_proxy_definition,[new_symbols(naming,[sQ17_eqProxy])])).
% 2.55/0.73  fof(f103,plain,(
% 2.55/0.73    ( ! [X0,X8,X1] : (k4_tarski(sK13(X0,X1,X8),sK14(X0,X1,X8)) = X8 | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 2.55/0.73    inference(equality_resolution,[],[f71])).
% 2.55/0.73  fof(f71,plain,(
% 2.55/0.73    ( ! [X2,X0,X8,X1] : (k4_tarski(sK13(X0,X1,X8),sK14(X0,X1,X8)) = X8 | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.55/0.73    inference(cnf_transformation,[],[f42])).
% 2.55/0.73  fof(f42,plain,(
% 2.55/0.73    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK10(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK10(X0,X1,X2),X2)) & ((sK10(X0,X1,X2) = k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)) & r2_hidden(sK12(X0,X1,X2),X1) & r2_hidden(sK11(X0,X1,X2),X0)) | r2_hidden(sK10(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK13(X0,X1,X8),sK14(X0,X1,X8)) = X8 & r2_hidden(sK14(X0,X1,X8),X1) & r2_hidden(sK13(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.55/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12,sK13,sK14])],[f38,f41,f40,f39])).
% 2.55/0.73  fof(f39,plain,(
% 2.55/0.73    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK10(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK10(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK10(X0,X1,X2),X2))))),
% 2.55/0.73    introduced(choice_axiom,[])).
% 2.55/0.73  fof(f40,plain,(
% 2.55/0.73    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK10(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK10(X0,X1,X2) = k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)) & r2_hidden(sK12(X0,X1,X2),X1) & r2_hidden(sK11(X0,X1,X2),X0)))),
% 2.55/0.73    introduced(choice_axiom,[])).
% 2.55/0.73  fof(f41,plain,(
% 2.55/0.73    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK13(X0,X1,X8),sK14(X0,X1,X8)) = X8 & r2_hidden(sK14(X0,X1,X8),X1) & r2_hidden(sK13(X0,X1,X8),X0)))),
% 2.55/0.73    introduced(choice_axiom,[])).
% 2.55/0.73  fof(f38,plain,(
% 2.55/0.73    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.55/0.73    inference(rectify,[],[f37])).
% 2.55/0.73  fof(f37,plain,(
% 2.55/0.73    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 2.55/0.73    inference(nnf_transformation,[],[f5])).
% 2.55/0.73  fof(f5,axiom,(
% 2.55/0.73    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 2.55/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 2.55/0.73  fof(f157,plain,(
% 2.55/0.73    ( ! [X4,X5] : (~sQ17_eqProxy(k4_tarski(X4,X5),sK7(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))))) ) | ~spl18_5),
% 2.55/0.73    inference(avatar_component_clause,[],[f156])).
% 2.55/0.73  fof(f156,plain,(
% 2.55/0.73    spl18_5 <=> ! [X5,X4] : ~sQ17_eqProxy(k4_tarski(X4,X5),sK7(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))))),
% 2.55/0.73    introduced(avatar_definition,[new_symbols(naming,[spl18_5])])).
% 2.55/0.73  fof(f2607,plain,(
% 2.55/0.73    ~spl18_18 | ~spl18_20 | spl18_51),
% 2.55/0.73    inference(avatar_split_clause,[],[f2207,f2118,f785,f752])).
% 2.55/0.73  fof(f752,plain,(
% 2.55/0.73    spl18_18 <=> r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK2)),
% 2.55/0.73    introduced(avatar_definition,[new_symbols(naming,[spl18_18])])).
% 2.55/0.73  fof(f785,plain,(
% 2.55/0.73    spl18_20 <=> r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK3)),
% 2.55/0.73    introduced(avatar_definition,[new_symbols(naming,[spl18_20])])).
% 2.55/0.73  fof(f2118,plain,(
% 2.55/0.73    spl18_51 <=> r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),
% 2.55/0.73    introduced(avatar_definition,[new_symbols(naming,[spl18_51])])).
% 2.55/0.73  fof(f2207,plain,(
% 2.55/0.73    ~r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK3) | ~r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK2) | spl18_51),
% 2.55/0.73    inference(resolution,[],[f2120,f98])).
% 2.55/0.73  fof(f98,plain,(
% 2.55/0.73    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.55/0.73    inference(equality_resolution,[],[f92])).
% 2.55/0.73  fof(f92,plain,(
% 2.55/0.73    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 2.55/0.73    inference(definition_unfolding,[],[f65,f51])).
% 2.55/0.73  fof(f51,plain,(
% 2.55/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.55/0.73    inference(cnf_transformation,[],[f4])).
% 2.55/0.73  fof(f4,axiom,(
% 2.55/0.73    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.55/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.55/0.73  fof(f65,plain,(
% 2.55/0.73    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 2.55/0.73    inference(cnf_transformation,[],[f36])).
% 2.55/0.73  fof(f36,plain,(
% 2.55/0.73    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK9(X0,X1,X2),X1) | ~r2_hidden(sK9(X0,X1,X2),X0) | ~r2_hidden(sK9(X0,X1,X2),X2)) & ((r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(sK9(X0,X1,X2),X0)) | r2_hidden(sK9(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.55/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f34,f35])).
% 2.55/0.73  fof(f35,plain,(
% 2.55/0.73    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK9(X0,X1,X2),X1) | ~r2_hidden(sK9(X0,X1,X2),X0) | ~r2_hidden(sK9(X0,X1,X2),X2)) & ((r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(sK9(X0,X1,X2),X0)) | r2_hidden(sK9(X0,X1,X2),X2))))),
% 2.55/0.73    introduced(choice_axiom,[])).
% 2.55/0.73  fof(f34,plain,(
% 2.55/0.73    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.55/0.73    inference(rectify,[],[f33])).
% 2.55/0.73  fof(f33,plain,(
% 2.55/0.73    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.55/0.73    inference(flattening,[],[f32])).
% 2.55/0.73  fof(f32,plain,(
% 2.55/0.73    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.55/0.73    inference(nnf_transformation,[],[f2])).
% 2.55/0.73  fof(f2,axiom,(
% 2.55/0.73    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.55/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.55/0.73  fof(f2120,plain,(
% 2.55/0.73    ~r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) | spl18_51),
% 2.55/0.73    inference(avatar_component_clause,[],[f2118])).
% 2.55/0.73  fof(f2598,plain,(
% 2.55/0.73    ~spl18_6 | ~spl18_11),
% 2.55/0.73    inference(avatar_contradiction_clause,[],[f2583])).
% 2.55/0.73  fof(f2583,plain,(
% 2.55/0.73    $false | (~spl18_6 | ~spl18_11)),
% 2.55/0.73    inference(resolution,[],[f210,f2496])).
% 2.55/0.73  fof(f2496,plain,(
% 2.55/0.73    ( ! [X4,X5] : (~r2_hidden(sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k2_zfmisc_1(X4,X5))) ) | ~spl18_6),
% 2.55/0.73    inference(resolution,[],[f160,f123])).
% 2.55/0.73  fof(f160,plain,(
% 2.55/0.73    ( ! [X2,X3] : (~sQ17_eqProxy(k4_tarski(X2,X3),sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))))) ) | ~spl18_6),
% 2.55/0.73    inference(avatar_component_clause,[],[f159])).
% 2.55/0.73  fof(f159,plain,(
% 2.55/0.73    spl18_6 <=> ! [X3,X2] : ~sQ17_eqProxy(k4_tarski(X2,X3),sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))))),
% 2.55/0.73    introduced(avatar_definition,[new_symbols(naming,[spl18_6])])).
% 2.55/0.73  fof(f210,plain,(
% 2.55/0.73    r2_hidden(sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k2_zfmisc_1(sK0,sK2)) | ~spl18_11),
% 2.55/0.73    inference(avatar_component_clause,[],[f209])).
% 2.55/0.73  fof(f209,plain,(
% 2.55/0.73    spl18_11 <=> r2_hidden(sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k2_zfmisc_1(sK0,sK2))),
% 2.55/0.73    introduced(avatar_definition,[new_symbols(naming,[spl18_11])])).
% 2.55/0.73  fof(f2560,plain,(
% 2.55/0.73    ~spl18_10 | spl18_11),
% 2.55/0.73    inference(avatar_contradiction_clause,[],[f2539])).
% 2.55/0.73  fof(f2539,plain,(
% 2.55/0.73    $false | (~spl18_10 | spl18_11)),
% 2.55/0.73    inference(resolution,[],[f178,f249])).
% 2.55/0.73  fof(f249,plain,(
% 2.55/0.73    ( ! [X10] : (~r2_hidden(sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),X10)))) ) | spl18_11),
% 2.55/0.73    inference(resolution,[],[f211,f100])).
% 2.55/0.73  fof(f100,plain,(
% 2.55/0.73    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.55/0.73    inference(equality_resolution,[],[f94])).
% 2.55/0.73  fof(f94,plain,(
% 2.55/0.73    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 2.55/0.73    inference(definition_unfolding,[],[f63,f51])).
% 2.55/0.73  fof(f63,plain,(
% 2.55/0.73    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.55/0.73    inference(cnf_transformation,[],[f36])).
% 2.55/0.73  fof(f211,plain,(
% 2.55/0.73    ~r2_hidden(sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k2_zfmisc_1(sK0,sK2)) | spl18_11),
% 2.55/0.73    inference(avatar_component_clause,[],[f209])).
% 2.55/0.73  fof(f178,plain,(
% 2.55/0.73    r2_hidden(sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))) | ~spl18_10),
% 2.55/0.73    inference(avatar_component_clause,[],[f176])).
% 2.55/0.73  fof(f176,plain,(
% 2.55/0.73    spl18_10 <=> r2_hidden(sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),
% 2.55/0.73    introduced(avatar_definition,[new_symbols(naming,[spl18_10])])).
% 2.55/0.73  fof(f2491,plain,(
% 2.55/0.73    spl18_17 | ~spl18_15),
% 2.55/0.73    inference(avatar_split_clause,[],[f2446,f304,f748])).
% 2.55/0.73  fof(f748,plain,(
% 2.55/0.73    spl18_17 <=> r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK0)),
% 2.55/0.73    introduced(avatar_definition,[new_symbols(naming,[spl18_17])])).
% 2.55/0.73  fof(f304,plain,(
% 2.55/0.73    spl18_15 <=> r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(sK0,sK2))),
% 2.55/0.73    introduced(avatar_definition,[new_symbols(naming,[spl18_15])])).
% 2.55/0.73  fof(f2446,plain,(
% 2.55/0.73    r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK0) | ~spl18_15),
% 2.55/0.73    inference(resolution,[],[f305,f81])).
% 2.55/0.73  fof(f81,plain,(
% 2.55/0.73    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.55/0.73    inference(cnf_transformation,[],[f46])).
% 2.55/0.73  fof(f46,plain,(
% 2.55/0.73    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.55/0.73    inference(flattening,[],[f45])).
% 2.55/0.73  fof(f45,plain,(
% 2.55/0.73    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.55/0.73    inference(nnf_transformation,[],[f9])).
% 2.55/0.73  fof(f9,axiom,(
% 2.55/0.73    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.55/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).
% 2.55/0.73  fof(f305,plain,(
% 2.55/0.73    r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(sK0,sK2)) | ~spl18_15),
% 2.55/0.73    inference(avatar_component_clause,[],[f304])).
% 2.55/0.73  fof(f2488,plain,(
% 2.55/0.73    ~spl18_17 | ~spl18_19 | spl18_50),
% 2.55/0.73    inference(avatar_split_clause,[],[f2199,f2114,f781,f748])).
% 2.55/0.73  fof(f781,plain,(
% 2.55/0.73    spl18_19 <=> r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK1)),
% 2.55/0.73    introduced(avatar_definition,[new_symbols(naming,[spl18_19])])).
% 2.55/0.73  fof(f2114,plain,(
% 2.55/0.73    spl18_50 <=> r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.55/0.73    introduced(avatar_definition,[new_symbols(naming,[spl18_50])])).
% 2.55/0.73  fof(f2199,plain,(
% 2.55/0.73    ~r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK1) | ~r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK0) | spl18_50),
% 2.55/0.73    inference(resolution,[],[f2116,f98])).
% 2.55/0.73  fof(f2116,plain,(
% 2.55/0.73    ~r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl18_50),
% 2.55/0.73    inference(avatar_component_clause,[],[f2114])).
% 2.55/0.73  fof(f2487,plain,(
% 2.55/0.73    spl18_20 | ~spl18_16),
% 2.55/0.73    inference(avatar_split_clause,[],[f2469,f308,f785])).
% 2.55/0.73  fof(f308,plain,(
% 2.55/0.73    spl18_16 <=> r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(sK1,sK3))),
% 2.55/0.73    introduced(avatar_definition,[new_symbols(naming,[spl18_16])])).
% 2.55/0.73  fof(f2469,plain,(
% 2.55/0.73    r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK3) | ~spl18_16),
% 2.55/0.73    inference(resolution,[],[f309,f79])).
% 2.55/0.73  fof(f79,plain,(
% 2.55/0.73    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.55/0.73    inference(cnf_transformation,[],[f44])).
% 2.55/0.73  fof(f44,plain,(
% 2.55/0.73    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.55/0.73    inference(flattening,[],[f43])).
% 2.55/0.73  fof(f43,plain,(
% 2.55/0.73    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.55/0.73    inference(nnf_transformation,[],[f7])).
% 2.55/0.73  fof(f7,axiom,(
% 2.55/0.73    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.55/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 2.55/0.73  fof(f309,plain,(
% 2.55/0.73    r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(sK1,sK3)) | ~spl18_16),
% 2.55/0.73    inference(avatar_component_clause,[],[f308])).
% 2.55/0.73  fof(f2486,plain,(
% 2.55/0.73    spl18_19 | ~spl18_16),
% 2.55/0.73    inference(avatar_split_clause,[],[f2468,f308,f781])).
% 2.55/0.73  fof(f2468,plain,(
% 2.55/0.73    r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK1) | ~spl18_16),
% 2.55/0.73    inference(resolution,[],[f309,f78])).
% 2.55/0.73  fof(f78,plain,(
% 2.55/0.73    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.55/0.73    inference(cnf_transformation,[],[f44])).
% 2.55/0.73  fof(f2465,plain,(
% 2.55/0.73    spl18_18 | ~spl18_15),
% 2.55/0.73    inference(avatar_split_clause,[],[f2449,f304,f752])).
% 2.55/0.73  fof(f2449,plain,(
% 2.55/0.73    r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK2) | ~spl18_15),
% 2.55/0.73    inference(resolution,[],[f305,f79])).
% 2.55/0.73  fof(f2145,plain,(
% 2.55/0.73    spl18_16 | ~spl18_8),
% 2.55/0.73    inference(avatar_split_clause,[],[f2132,f166,f308])).
% 2.55/0.73  fof(f166,plain,(
% 2.55/0.73    spl18_8 <=> r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),
% 2.55/0.73    introduced(avatar_definition,[new_symbols(naming,[spl18_8])])).
% 2.55/0.73  fof(f2132,plain,(
% 2.55/0.73    r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(sK1,sK3)) | ~spl18_8),
% 2.55/0.73    inference(resolution,[],[f167,f99])).
% 2.55/0.73  fof(f99,plain,(
% 2.55/0.73    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.55/0.73    inference(equality_resolution,[],[f93])).
% 2.55/0.73  fof(f93,plain,(
% 2.55/0.73    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 2.55/0.73    inference(definition_unfolding,[],[f64,f51])).
% 2.55/0.73  fof(f64,plain,(
% 2.55/0.73    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.55/0.73    inference(cnf_transformation,[],[f36])).
% 2.55/0.73  fof(f167,plain,(
% 2.55/0.73    r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))) | ~spl18_8),
% 2.55/0.73    inference(avatar_component_clause,[],[f166])).
% 2.55/0.73  fof(f2144,plain,(
% 2.55/0.73    spl18_15 | ~spl18_8),
% 2.55/0.73    inference(avatar_split_clause,[],[f2131,f166,f304])).
% 2.55/0.73  fof(f2131,plain,(
% 2.55/0.73    r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(sK0,sK2)) | ~spl18_8),
% 2.55/0.73    inference(resolution,[],[f167,f100])).
% 2.55/0.73  fof(f2123,plain,(
% 2.55/0.73    ~spl18_50 | ~spl18_51 | spl18_7),
% 2.55/0.73    inference(avatar_split_clause,[],[f2101,f162,f2118,f2114])).
% 2.55/0.73  fof(f162,plain,(
% 2.55/0.73    spl18_7 <=> r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))),
% 2.55/0.73    introduced(avatar_definition,[new_symbols(naming,[spl18_7])])).
% 2.55/0.73  fof(f2101,plain,(
% 2.55/0.73    ~r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) | ~r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl18_7),
% 2.55/0.73    inference(resolution,[],[f164,f102])).
% 2.55/0.73  fof(f102,plain,(
% 2.55/0.73    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 2.55/0.73    inference(equality_resolution,[],[f101])).
% 2.55/0.73  fof(f101,plain,(
% 2.55/0.73    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.55/0.73    inference(equality_resolution,[],[f72])).
% 2.55/0.73  fof(f72,plain,(
% 2.55/0.73    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.55/0.73    inference(cnf_transformation,[],[f42])).
% 2.55/0.73  fof(f164,plain,(
% 2.55/0.73    ~r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) | spl18_7),
% 2.55/0.73    inference(avatar_component_clause,[],[f162])).
% 2.55/0.73  fof(f2070,plain,(
% 2.55/0.73    spl18_19 | ~spl18_7),
% 2.55/0.73    inference(avatar_split_clause,[],[f489,f162,f781])).
% 2.55/0.73  fof(f489,plain,(
% 2.55/0.73    r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK1) | ~spl18_7),
% 2.55/0.73    inference(resolution,[],[f273,f99])).
% 2.55/0.73  fof(f273,plain,(
% 2.55/0.73    r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl18_7),
% 2.55/0.73    inference(resolution,[],[f163,f81])).
% 2.55/0.73  fof(f163,plain,(
% 2.55/0.73    r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) | ~spl18_7),
% 2.55/0.73    inference(avatar_component_clause,[],[f162])).
% 2.55/0.73  fof(f2069,plain,(
% 2.55/0.73    spl18_18 | ~spl18_7),
% 2.55/0.73    inference(avatar_split_clause,[],[f510,f162,f752])).
% 2.55/0.73  fof(f510,plain,(
% 2.55/0.73    r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK2) | ~spl18_7),
% 2.55/0.73    inference(resolution,[],[f274,f100])).
% 2.55/0.73  fof(f274,plain,(
% 2.55/0.73    r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) | ~spl18_7),
% 2.55/0.73    inference(resolution,[],[f163,f82])).
% 2.55/0.73  fof(f82,plain,(
% 2.55/0.73    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.55/0.73    inference(cnf_transformation,[],[f46])).
% 2.55/0.73  fof(f2068,plain,(
% 2.55/0.73    spl18_20 | ~spl18_7),
% 2.55/0.73    inference(avatar_split_clause,[],[f511,f162,f785])).
% 2.55/0.73  fof(f511,plain,(
% 2.55/0.73    r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK3) | ~spl18_7),
% 2.55/0.73    inference(resolution,[],[f274,f99])).
% 2.55/0.73  fof(f2026,plain,(
% 2.55/0.73    spl18_9 | spl18_7 | spl18_8 | spl18_10),
% 2.55/0.73    inference(avatar_split_clause,[],[f1776,f176,f166,f162,f171])).
% 2.55/0.73  fof(f1776,plain,(
% 2.55/0.73    r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))) | r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) | r2_hidden(sK7(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) | spl18_10),
% 2.55/0.73    inference(resolution,[],[f197,f107])).
% 2.55/0.74  fof(f107,plain,(
% 2.55/0.74    ~sQ17_eqProxy(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),
% 2.55/0.74    inference(equality_proxy_replacement,[],[f87,f106])).
% 2.55/0.74  fof(f87,plain,(
% 2.55/0.74    k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),
% 2.55/0.74    inference(definition_unfolding,[],[f49,f51,f51,f51])).
% 2.55/0.74  fof(f49,plain,(
% 2.55/0.74    k2_zfmisc_1(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK3)) != k3_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 2.55/0.74    inference(cnf_transformation,[],[f22])).
% 2.55/0.74  fof(f22,plain,(
% 2.55/0.74    k2_zfmisc_1(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK3)) != k3_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 2.55/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f21])).
% 2.55/0.74  fof(f21,plain,(
% 2.55/0.74    ? [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) != k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) => k2_zfmisc_1(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK3)) != k3_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 2.55/0.74    introduced(choice_axiom,[])).
% 2.55/0.74  fof(f14,plain,(
% 2.55/0.74    ? [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) != k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 2.55/0.74    inference(ennf_transformation,[],[f12])).
% 2.55/0.74  fof(f12,negated_conjecture,(
% 2.55/0.74    ~! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 2.55/0.74    inference(negated_conjecture,[],[f11])).
% 2.55/0.74  fof(f11,conjecture,(
% 2.55/0.74    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 2.55/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 2.55/0.74  fof(f197,plain,(
% 2.55/0.74    ( ! [X0] : (sQ17_eqProxy(X0,k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))) | r2_hidden(k4_tarski(sK4(X0,k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(X0,k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))) | r2_hidden(k4_tarski(sK4(X0,k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(X0,k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),X0) | r2_hidden(sK7(X0),X0)) ) | spl18_10),
% 2.55/0.74    inference(resolution,[],[f177,f115])).
% 2.55/0.74  fof(f115,plain,(
% 2.55/0.74    ( ! [X0,X1] : (sQ17_eqProxy(X0,X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK6(X1),X1) | r2_hidden(sK7(X0),X0)) )),
% 2.55/0.74    inference(equality_proxy_replacement,[],[f52,f106])).
% 2.55/0.74  fof(f52,plain,(
% 2.55/0.74    ( ! [X0,X1] : (X0 = X1 | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK6(X1),X1) | r2_hidden(sK7(X0),X0)) )),
% 2.55/0.74    inference(cnf_transformation,[],[f27])).
% 2.55/0.74  fof(f27,plain,(
% 2.55/0.74    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0))) | (! [X5,X6] : k4_tarski(X5,X6) != sK6(X1) & r2_hidden(sK6(X1),X1)) | (! [X8,X9] : k4_tarski(X8,X9) != sK7(X0) & r2_hidden(sK7(X0),X0)))),
% 2.55/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f23,f26,f25,f24])).
% 2.55/0.74  fof(f24,plain,(
% 2.55/0.74    ! [X1,X0] : (? [X2,X3] : ((~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r2_hidden(k4_tarski(X2,X3),X1) | r2_hidden(k4_tarski(X2,X3),X0))) => ((~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0))))),
% 2.55/0.74    introduced(choice_axiom,[])).
% 2.55/0.74  fof(f25,plain,(
% 2.55/0.74    ! [X1] : (? [X4] : (! [X5,X6] : k4_tarski(X5,X6) != X4 & r2_hidden(X4,X1)) => (! [X6,X5] : k4_tarski(X5,X6) != sK6(X1) & r2_hidden(sK6(X1),X1)))),
% 2.55/0.74    introduced(choice_axiom,[])).
% 2.55/0.74  fof(f26,plain,(
% 2.55/0.74    ! [X0] : (? [X7] : (! [X8,X9] : k4_tarski(X8,X9) != X7 & r2_hidden(X7,X0)) => (! [X9,X8] : k4_tarski(X8,X9) != sK7(X0) & r2_hidden(sK7(X0),X0)))),
% 2.55/0.74    introduced(choice_axiom,[])).
% 2.55/0.74  fof(f23,plain,(
% 2.55/0.74    ! [X0,X1] : (X0 = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r2_hidden(k4_tarski(X2,X3),X1) | r2_hidden(k4_tarski(X2,X3),X0))) | ? [X4] : (! [X5,X6] : k4_tarski(X5,X6) != X4 & r2_hidden(X4,X1)) | ? [X7] : (! [X8,X9] : k4_tarski(X8,X9) != X7 & r2_hidden(X7,X0)))),
% 2.55/0.74    inference(nnf_transformation,[],[f16])).
% 2.55/0.74  fof(f16,plain,(
% 2.55/0.74    ! [X0,X1] : (X0 = X1 | ? [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) <~> r2_hidden(k4_tarski(X2,X3),X1)) | ? [X4] : (! [X5,X6] : k4_tarski(X5,X6) != X4 & r2_hidden(X4,X1)) | ? [X7] : (! [X8,X9] : k4_tarski(X8,X9) != X7 & r2_hidden(X7,X0)))),
% 2.55/0.74    inference(flattening,[],[f15])).
% 2.55/0.74  fof(f15,plain,(
% 2.55/0.74    ! [X0,X1] : (X0 = X1 | (? [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) <~> r2_hidden(k4_tarski(X2,X3),X1)) | ? [X4] : (! [X5,X6] : k4_tarski(X5,X6) != X4 & r2_hidden(X4,X1)) | ? [X7] : (! [X8,X9] : k4_tarski(X8,X9) != X7 & r2_hidden(X7,X0))))),
% 2.55/0.74    inference(ennf_transformation,[],[f13])).
% 2.55/0.74  fof(f13,plain,(
% 2.55/0.74    ! [X0,X1] : ((! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) <=> r2_hidden(k4_tarski(X2,X3),X1)) & ! [X4] : ~(! [X5,X6] : k4_tarski(X5,X6) != X4 & r2_hidden(X4,X1)) & ! [X7] : ~(! [X8,X9] : k4_tarski(X8,X9) != X7 & r2_hidden(X7,X0))) => X0 = X1)),
% 2.55/0.74    inference(rectify,[],[f6])).
% 2.55/0.74  fof(f6,axiom,(
% 2.55/0.74    ! [X0,X1] : ((! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) <=> r2_hidden(k4_tarski(X2,X3),X1)) & ! [X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X2 & r2_hidden(X2,X1)) & ! [X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X2 & r2_hidden(X2,X0))) => X0 = X1)),
% 2.55/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l131_zfmisc_1)).
% 2.55/0.74  fof(f177,plain,(
% 2.55/0.74    ~r2_hidden(sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))) | spl18_10),
% 2.55/0.74    inference(avatar_component_clause,[],[f176])).
% 2.55/0.74  fof(f2025,plain,(
% 2.55/0.74    spl18_5 | spl18_7 | spl18_8 | spl18_10),
% 2.55/0.74    inference(avatar_split_clause,[],[f1795,f176,f166,f162,f156])).
% 2.55/0.74  fof(f1795,plain,(
% 2.55/0.74    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))) | r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) | ~sQ17_eqProxy(k4_tarski(X0,X1),sK7(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))))) ) | spl18_10),
% 2.55/0.74    inference(resolution,[],[f198,f107])).
% 2.55/0.74  fof(f198,plain,(
% 2.55/0.74    ( ! [X2,X3,X1] : (sQ17_eqProxy(X1,k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))) | r2_hidden(k4_tarski(sK4(X1,k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(X1,k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))) | r2_hidden(k4_tarski(sK4(X1,k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(X1,k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),X1) | ~sQ17_eqProxy(k4_tarski(X2,X3),sK7(X1))) ) | spl18_10),
% 2.55/0.74    inference(resolution,[],[f177,f114])).
% 2.55/0.74  fof(f114,plain,(
% 2.55/0.74    ( ! [X0,X8,X1,X9] : (sQ17_eqProxy(X0,X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK6(X1),X1) | ~sQ17_eqProxy(k4_tarski(X8,X9),sK7(X0))) )),
% 2.55/0.74    inference(equality_proxy_replacement,[],[f53,f106,f106])).
% 2.55/0.74  fof(f53,plain,(
% 2.55/0.74    ( ! [X0,X8,X1,X9] : (X0 = X1 | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK6(X1),X1) | k4_tarski(X8,X9) != sK7(X0)) )),
% 2.55/0.74    inference(cnf_transformation,[],[f27])).
% 2.55/0.74  fof(f2024,plain,(
% 2.55/0.74    ~spl18_7 | spl18_17),
% 2.55/0.74    inference(avatar_contradiction_clause,[],[f2016])).
% 2.55/0.74  fof(f2016,plain,(
% 2.55/0.74    $false | (~spl18_7 | spl18_17)),
% 2.55/0.74    inference(resolution,[],[f750,f488])).
% 2.55/0.74  fof(f488,plain,(
% 2.55/0.74    r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK0) | ~spl18_7),
% 2.55/0.74    inference(resolution,[],[f273,f100])).
% 2.55/0.74  fof(f750,plain,(
% 2.55/0.74    ~r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK0) | spl18_17),
% 2.55/0.74    inference(avatar_component_clause,[],[f748])).
% 2.55/0.74  fof(f790,plain,(
% 2.55/0.74    ~spl18_19 | ~spl18_20 | spl18_16),
% 2.55/0.74    inference(avatar_split_clause,[],[f772,f308,f785,f781])).
% 2.55/0.74  fof(f772,plain,(
% 2.55/0.74    ~r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK3) | ~r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK1) | spl18_16),
% 2.55/0.74    inference(resolution,[],[f310,f102])).
% 2.55/0.74  fof(f310,plain,(
% 2.55/0.74    ~r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(sK1,sK3)) | spl18_16),
% 2.55/0.74    inference(avatar_component_clause,[],[f308])).
% 2.55/0.74  fof(f757,plain,(
% 2.55/0.74    ~spl18_17 | ~spl18_18 | spl18_15),
% 2.55/0.74    inference(avatar_split_clause,[],[f739,f304,f752,f748])).
% 2.55/0.74  fof(f739,plain,(
% 2.55/0.74    ~r2_hidden(sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK2) | ~r2_hidden(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK0) | spl18_15),
% 2.55/0.74    inference(resolution,[],[f306,f102])).
% 2.55/0.74  fof(f306,plain,(
% 2.55/0.74    ~r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(sK0,sK2)) | spl18_15),
% 2.55/0.74    inference(avatar_component_clause,[],[f304])).
% 2.55/0.74  fof(f311,plain,(
% 2.55/0.74    ~spl18_15 | ~spl18_16 | spl18_8),
% 2.55/0.74    inference(avatar_split_clause,[],[f291,f166,f308,f304])).
% 2.55/0.74  fof(f291,plain,(
% 2.55/0.74    ~r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(sK1,sK3)) | ~r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(sK0,sK2)) | spl18_8),
% 2.55/0.74    inference(resolution,[],[f168,f98])).
% 2.55/0.74  fof(f168,plain,(
% 2.55/0.74    ~r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))) | spl18_8),
% 2.55/0.74    inference(avatar_component_clause,[],[f166])).
% 2.55/0.74  fof(f182,plain,(
% 2.55/0.74    spl18_9 | spl18_6 | spl18_7 | spl18_8),
% 2.55/0.74    inference(avatar_split_clause,[],[f134,f166,f162,f159,f171])).
% 2.55/0.74  fof(f134,plain,(
% 2.55/0.74    ( ! [X14,X15] : (r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))) | r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) | ~sQ17_eqProxy(k4_tarski(X14,X15),sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))) | r2_hidden(sK7(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))) )),
% 2.55/0.74    inference(resolution,[],[f107,f113])).
% 2.55/0.74  fof(f113,plain,(
% 2.55/0.74    ( ! [X6,X0,X5,X1] : (sQ17_eqProxy(X0,X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | ~sQ17_eqProxy(k4_tarski(X5,X6),sK6(X1)) | r2_hidden(sK7(X0),X0)) )),
% 2.55/0.74    inference(equality_proxy_replacement,[],[f54,f106,f106])).
% 2.55/0.74  fof(f54,plain,(
% 2.55/0.74    ( ! [X6,X0,X5,X1] : (X0 = X1 | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | k4_tarski(X5,X6) != sK6(X1) | r2_hidden(sK7(X0),X0)) )),
% 2.55/0.74    inference(cnf_transformation,[],[f27])).
% 2.55/0.74  fof(f181,plain,(
% 2.55/0.74    spl18_5 | spl18_6 | spl18_7 | spl18_8),
% 2.55/0.74    inference(avatar_split_clause,[],[f133,f166,f162,f159,f156])).
% 2.55/0.74  fof(f133,plain,(
% 2.55/0.74    ( ! [X12,X10,X13,X11] : (r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))) | r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) | ~sQ17_eqProxy(k4_tarski(X10,X11),sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))) | ~sQ17_eqProxy(k4_tarski(X12,X13),sK7(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))))) )),
% 2.55/0.74    inference(resolution,[],[f107,f112])).
% 2.55/0.74  fof(f112,plain,(
% 2.55/0.74    ( ! [X6,X0,X8,X5,X1,X9] : (sQ17_eqProxy(X0,X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | ~sQ17_eqProxy(k4_tarski(X5,X6),sK6(X1)) | ~sQ17_eqProxy(k4_tarski(X8,X9),sK7(X0))) )),
% 2.55/0.74    inference(equality_proxy_replacement,[],[f55,f106,f106,f106])).
% 2.55/0.74  fof(f55,plain,(
% 2.55/0.74    ( ! [X6,X0,X8,X5,X1,X9] : (X0 = X1 | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | k4_tarski(X5,X6) != sK6(X1) | k4_tarski(X8,X9) != sK7(X0)) )),
% 2.55/0.74    inference(cnf_transformation,[],[f27])).
% 2.55/0.74  fof(f180,plain,(
% 2.55/0.74    spl18_9 | spl18_10 | ~spl18_7 | ~spl18_8),
% 2.55/0.74    inference(avatar_split_clause,[],[f132,f166,f162,f176,f171])).
% 2.55/0.74  fof(f132,plain,(
% 2.55/0.74    ~r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))) | ~r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) | r2_hidden(sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))) | r2_hidden(sK7(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))),
% 2.55/0.74    inference(resolution,[],[f107,f111])).
% 2.55/0.74  fof(f111,plain,(
% 2.55/0.74    ( ! [X0,X1] : (sQ17_eqProxy(X0,X1) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK6(X1),X1) | r2_hidden(sK7(X0),X0)) )),
% 2.55/0.74    inference(equality_proxy_replacement,[],[f56,f106])).
% 2.55/0.74  fof(f56,plain,(
% 2.55/0.74    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK6(X1),X1) | r2_hidden(sK7(X0),X0)) )),
% 2.55/0.74    inference(cnf_transformation,[],[f27])).
% 2.55/0.74  fof(f179,plain,(
% 2.55/0.74    spl18_5 | spl18_10 | ~spl18_7 | ~spl18_8),
% 2.55/0.74    inference(avatar_split_clause,[],[f131,f166,f162,f176,f156])).
% 2.55/0.74  fof(f131,plain,(
% 2.55/0.74    ( ! [X8,X9] : (~r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))) | ~r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) | r2_hidden(sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))) | ~sQ17_eqProxy(k4_tarski(X8,X9),sK7(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))))) )),
% 2.55/0.74    inference(resolution,[],[f107,f110])).
% 2.55/0.74  fof(f110,plain,(
% 2.55/0.74    ( ! [X0,X8,X1,X9] : (sQ17_eqProxy(X0,X1) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK6(X1),X1) | ~sQ17_eqProxy(k4_tarski(X8,X9),sK7(X0))) )),
% 2.55/0.74    inference(equality_proxy_replacement,[],[f57,f106,f106])).
% 2.55/0.74  fof(f57,plain,(
% 2.55/0.74    ( ! [X0,X8,X1,X9] : (X0 = X1 | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK6(X1),X1) | k4_tarski(X8,X9) != sK7(X0)) )),
% 2.55/0.74    inference(cnf_transformation,[],[f27])).
% 2.55/0.74  fof(f174,plain,(
% 2.55/0.74    spl18_9 | spl18_6 | ~spl18_7 | ~spl18_8),
% 2.55/0.74    inference(avatar_split_clause,[],[f130,f166,f162,f159,f171])).
% 2.55/0.74  fof(f130,plain,(
% 2.55/0.74    ( ! [X6,X7] : (~r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))) | ~r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) | ~sQ17_eqProxy(k4_tarski(X6,X7),sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))) | r2_hidden(sK7(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))) )),
% 2.55/0.74    inference(resolution,[],[f107,f109])).
% 2.55/0.74  fof(f109,plain,(
% 2.55/0.74    ( ! [X6,X0,X5,X1] : (sQ17_eqProxy(X0,X1) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | ~sQ17_eqProxy(k4_tarski(X5,X6),sK6(X1)) | r2_hidden(sK7(X0),X0)) )),
% 2.55/0.74    inference(equality_proxy_replacement,[],[f58,f106,f106])).
% 2.55/0.74  fof(f58,plain,(
% 2.55/0.74    ( ! [X6,X0,X5,X1] : (X0 = X1 | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | k4_tarski(X5,X6) != sK6(X1) | r2_hidden(sK7(X0),X0)) )),
% 2.55/0.74    inference(cnf_transformation,[],[f27])).
% 2.55/0.74  fof(f169,plain,(
% 2.55/0.74    spl18_5 | spl18_6 | ~spl18_7 | ~spl18_8),
% 2.55/0.74    inference(avatar_split_clause,[],[f129,f166,f162,f159,f156])).
% 2.55/0.74  fof(f129,plain,(
% 2.55/0.74    ( ! [X4,X2,X5,X3] : (~r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))) | ~r2_hidden(k4_tarski(sK4(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),sK5(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) | ~sQ17_eqProxy(k4_tarski(X2,X3),sK6(k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))) | ~sQ17_eqProxy(k4_tarski(X4,X5),sK7(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))))) )),
% 2.55/0.74    inference(resolution,[],[f107,f108])).
% 2.55/0.74  fof(f108,plain,(
% 2.55/0.74    ( ! [X6,X0,X8,X5,X1,X9] : (sQ17_eqProxy(X0,X1) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | ~sQ17_eqProxy(k4_tarski(X5,X6),sK6(X1)) | ~sQ17_eqProxy(k4_tarski(X8,X9),sK7(X0))) )),
% 2.55/0.74    inference(equality_proxy_replacement,[],[f59,f106,f106,f106])).
% 2.55/0.74  fof(f59,plain,(
% 2.55/0.74    ( ! [X6,X0,X8,X5,X1,X9] : (X0 = X1 | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | k4_tarski(X5,X6) != sK6(X1) | k4_tarski(X8,X9) != sK7(X0)) )),
% 2.55/0.74    inference(cnf_transformation,[],[f27])).
% 2.55/0.74  % SZS output end Proof for theBenchmark
% 2.55/0.74  % (32586)------------------------------
% 2.55/0.74  % (32586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.55/0.74  % (32586)Termination reason: Refutation
% 2.55/0.74  
% 2.55/0.74  % (32586)Memory used [KB]: 7931
% 2.55/0.74  % (32586)Time elapsed: 0.301 s
% 2.55/0.74  % (32586)------------------------------
% 2.55/0.74  % (32586)------------------------------
% 2.55/0.74  % (32569)Success in time 0.369 s
%------------------------------------------------------------------------------
