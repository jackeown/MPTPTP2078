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
% DateTime   : Thu Dec  3 12:59:36 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 229 expanded)
%              Number of leaves         :   14 (  98 expanded)
%              Depth                    :   11
%              Number of atoms          :  279 (1353 expanded)
%              Number of equality atoms :   54 ( 354 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (17008)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f104,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f58,f60,f62,f67,f69,f79,f87,f101,f103])).

fof(f103,plain,
    ( ~ spl11_5
    | spl11_3
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f102,f65,f50,f65])).

fof(f50,plain,
    ( spl11_3
  <=> r2_hidden(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f65,plain,
    ( spl11_5
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f102,plain,
    ( r2_hidden(sK1,sK4)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | ~ spl11_5 ),
    inference(superposition,[],[f41,f95])).

fof(f95,plain,
    ( sK1 = sK10(sK3,sK4,k4_tarski(sK0,sK1))
    | ~ spl11_5 ),
    inference(forward_demodulation,[],[f93,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f93,plain,
    ( sK10(sK3,sK4,k4_tarski(sK0,sK1)) = k2_mcart_1(k4_tarski(sK0,sK1))
    | ~ spl11_5 ),
    inference(superposition,[],[f23,f88])).

fof(f88,plain,
    ( k4_tarski(sK0,sK1) = k4_tarski(sK9(sK3,sK4,k4_tarski(sK0,sK1)),sK10(sK3,sK4,k4_tarski(sK0,sK1)))
    | ~ spl11_5 ),
    inference(resolution,[],[f86,f40])).

fof(f40,plain,(
    ! [X0,X8,X1] :
      ( ~ r2_hidden(X8,k2_zfmisc_1(X0,X1))
      | k4_tarski(sK9(X0,X1,X8),sK10(X0,X1,X8)) = X8 ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK9(X0,X1,X8),sK10(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f13,f16,f15,f14])).

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

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK6(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK6(X0,X1,X2) = k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2))
        & r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(sK7(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK9(X0,X1,X8),sK10(X0,X1,X8)) = X8
        & r2_hidden(sK10(X0,X1,X8),X1)
        & r2_hidden(sK9(X0,X1,X8),X0) ) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f86,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f41,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK10(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK10(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f101,plain,
    ( ~ spl11_5
    | spl11_2
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f100,f65,f47,f65])).

fof(f47,plain,
    ( spl11_2
  <=> r2_hidden(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f100,plain,
    ( r2_hidden(sK0,sK3)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | ~ spl11_5 ),
    inference(superposition,[],[f42,f94])).

fof(f94,plain,
    ( sK0 = sK9(sK3,sK4,k4_tarski(sK0,sK1))
    | ~ spl11_5 ),
    inference(forward_demodulation,[],[f92,f22])).

fof(f22,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f92,plain,
    ( sK9(sK3,sK4,k4_tarski(sK0,sK1)) = k1_mcart_1(k4_tarski(sK0,sK1))
    | ~ spl11_5 ),
    inference(superposition,[],[f22,f88])).

fof(f42,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK9(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK9(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f87,plain,
    ( ~ spl11_1
    | spl11_5
    | ~ spl11_1 ),
    inference(avatar_split_clause,[],[f85,f44,f65,f44])).

fof(f44,plain,
    ( spl11_1
  <=> r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f85,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | ~ spl11_1 ),
    inference(superposition,[],[f42,f75])).

fof(f75,plain,
    ( k4_tarski(sK0,sK1) = sK9(k2_zfmisc_1(sK3,sK4),sK5,k4_tarski(k4_tarski(sK0,sK1),sK2))
    | ~ spl11_1 ),
    inference(forward_demodulation,[],[f73,f22])).

fof(f73,plain,
    ( sK9(k2_zfmisc_1(sK3,sK4),sK5,k4_tarski(k4_tarski(sK0,sK1),sK2)) = k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))
    | ~ spl11_1 ),
    inference(superposition,[],[f22,f70])).

fof(f70,plain,
    ( k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(sK9(k2_zfmisc_1(sK3,sK4),sK5,k4_tarski(k4_tarski(sK0,sK1),sK2)),sK10(k2_zfmisc_1(sK3,sK4),sK5,k4_tarski(k4_tarski(sK0,sK1),sK2)))
    | ~ spl11_1 ),
    inference(resolution,[],[f56,f40])).

fof(f56,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f79,plain,
    ( ~ spl11_1
    | spl11_4
    | ~ spl11_1 ),
    inference(avatar_split_clause,[],[f78,f44,f53,f44])).

fof(f53,plain,
    ( spl11_4
  <=> r2_hidden(sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f78,plain,
    ( r2_hidden(sK2,sK5)
    | ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | ~ spl11_1 ),
    inference(superposition,[],[f41,f76])).

fof(f76,plain,
    ( sK2 = sK10(k2_zfmisc_1(sK3,sK4),sK5,k4_tarski(k4_tarski(sK0,sK1),sK2))
    | ~ spl11_1 ),
    inference(forward_demodulation,[],[f74,f23])).

fof(f74,plain,
    ( sK10(k2_zfmisc_1(sK3,sK4),sK5,k4_tarski(k4_tarski(sK0,sK1),sK2)) = k2_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2))
    | ~ spl11_1 ),
    inference(superposition,[],[f23,f70])).

fof(f69,plain,
    ( ~ spl11_2
    | ~ spl11_3
    | spl11_5 ),
    inference(avatar_split_clause,[],[f68,f65,f50,f47])).

fof(f68,plain,
    ( ~ r2_hidden(sK1,sK4)
    | ~ r2_hidden(sK0,sK3)
    | spl11_5 ),
    inference(resolution,[],[f66,f39])).

fof(f39,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f66,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | spl11_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f67,plain,
    ( ~ spl11_5
    | ~ spl11_4
    | spl11_1 ),
    inference(avatar_split_clause,[],[f63,f44,f53,f65])).

fof(f63,plain,
    ( ~ r2_hidden(sK2,sK5)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4))
    | spl11_1 ),
    inference(resolution,[],[f45,f39])).

fof(f45,plain,
    ( ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | spl11_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f62,plain,
    ( spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f37,f47,f44])).

fof(f37,plain,
    ( r2_hidden(sK0,sK3)
    | r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f18,f25,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f18,plain,
    ( r2_hidden(sK0,sK3)
    | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( ~ r2_hidden(sK2,sK5)
      | ~ r2_hidden(sK1,sK4)
      | ~ r2_hidden(sK0,sK3)
      | ~ r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) )
    & ( ( r2_hidden(sK2,sK5)
        & r2_hidden(sK1,sK4)
        & r2_hidden(sK0,sK3) )
      | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( ~ r2_hidden(X2,X5)
          | ~ r2_hidden(X1,X4)
          | ~ r2_hidden(X0,X3)
          | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) )
        & ( ( r2_hidden(X2,X5)
            & r2_hidden(X1,X4)
            & r2_hidden(X0,X3) )
          | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) )
   => ( ( ~ r2_hidden(sK2,sK5)
        | ~ r2_hidden(sK1,sK4)
        | ~ r2_hidden(sK0,sK3)
        | ~ r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) )
      & ( ( r2_hidden(sK2,sK5)
          & r2_hidden(sK1,sK4)
          & r2_hidden(sK0,sK3) )
        | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( ~ r2_hidden(X2,X5)
        | ~ r2_hidden(X1,X4)
        | ~ r2_hidden(X0,X3)
        | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) )
      & ( ( r2_hidden(X2,X5)
          & r2_hidden(X1,X4)
          & r2_hidden(X0,X3) )
        | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( ~ r2_hidden(X2,X5)
        | ~ r2_hidden(X1,X4)
        | ~ r2_hidden(X0,X3)
        | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) )
      & ( ( r2_hidden(X2,X5)
          & r2_hidden(X1,X4)
          & r2_hidden(X0,X3) )
        | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
    <~> ( r2_hidden(X2,X5)
        & r2_hidden(X1,X4)
        & r2_hidden(X0,X3) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
      <=> ( r2_hidden(X2,X5)
          & r2_hidden(X1,X4)
          & r2_hidden(X0,X3) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
    <=> ( r2_hidden(X2,X5)
        & r2_hidden(X1,X4)
        & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_mcart_1)).

fof(f60,plain,
    ( spl11_1
    | spl11_3 ),
    inference(avatar_split_clause,[],[f36,f50,f44])).

fof(f36,plain,
    ( r2_hidden(sK1,sK4)
    | r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f19,f25,f24])).

fof(f19,plain,
    ( r2_hidden(sK1,sK4)
    | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f11])).

fof(f58,plain,
    ( spl11_1
    | spl11_4 ),
    inference(avatar_split_clause,[],[f35,f53,f44])).

fof(f35,plain,
    ( r2_hidden(sK2,sK5)
    | r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f20,f25,f24])).

fof(f20,plain,
    ( r2_hidden(sK2,sK5)
    | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,
    ( ~ spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f34,f53,f50,f47,f44])).

fof(f34,plain,
    ( ~ r2_hidden(sK2,sK5)
    | ~ r2_hidden(sK1,sK4)
    | ~ r2_hidden(sK0,sK3)
    | ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f21,f25,f24])).

fof(f21,plain,
    ( ~ r2_hidden(sK2,sK5)
    | ~ r2_hidden(sK1,sK4)
    | ~ r2_hidden(sK0,sK3)
    | ~ r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:31:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (16989)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (16986)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (16995)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (17006)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.28/0.53  % (16985)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.28/0.53  % (17005)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.28/0.53  % (16997)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.28/0.53  % (16988)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.28/0.53  % (16987)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.53  % (16990)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.28/0.53  % (16987)Refutation found. Thanks to Tanya!
% 1.28/0.53  % SZS status Theorem for theBenchmark
% 1.28/0.53  % SZS output start Proof for theBenchmark
% 1.28/0.53  % (17008)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.28/0.53  fof(f104,plain,(
% 1.28/0.53    $false),
% 1.28/0.53    inference(avatar_sat_refutation,[],[f55,f58,f60,f62,f67,f69,f79,f87,f101,f103])).
% 1.28/0.53  fof(f103,plain,(
% 1.28/0.53    ~spl11_5 | spl11_3 | ~spl11_5),
% 1.28/0.53    inference(avatar_split_clause,[],[f102,f65,f50,f65])).
% 1.28/0.53  fof(f50,plain,(
% 1.28/0.53    spl11_3 <=> r2_hidden(sK1,sK4)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 1.28/0.53  fof(f65,plain,(
% 1.28/0.53    spl11_5 <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4))),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 1.28/0.53  fof(f102,plain,(
% 1.28/0.53    r2_hidden(sK1,sK4) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4)) | ~spl11_5),
% 1.28/0.53    inference(superposition,[],[f41,f95])).
% 1.28/0.53  fof(f95,plain,(
% 1.28/0.53    sK1 = sK10(sK3,sK4,k4_tarski(sK0,sK1)) | ~spl11_5),
% 1.28/0.53    inference(forward_demodulation,[],[f93,f23])).
% 1.28/0.53  fof(f23,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.28/0.53    inference(cnf_transformation,[],[f4])).
% 1.28/0.53  fof(f4,axiom,(
% 1.28/0.53    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.28/0.53  fof(f93,plain,(
% 1.28/0.53    sK10(sK3,sK4,k4_tarski(sK0,sK1)) = k2_mcart_1(k4_tarski(sK0,sK1)) | ~spl11_5),
% 1.28/0.53    inference(superposition,[],[f23,f88])).
% 1.28/0.53  fof(f88,plain,(
% 1.28/0.53    k4_tarski(sK0,sK1) = k4_tarski(sK9(sK3,sK4,k4_tarski(sK0,sK1)),sK10(sK3,sK4,k4_tarski(sK0,sK1))) | ~spl11_5),
% 1.28/0.53    inference(resolution,[],[f86,f40])).
% 1.28/0.53  fof(f40,plain,(
% 1.28/0.53    ( ! [X0,X8,X1] : (~r2_hidden(X8,k2_zfmisc_1(X0,X1)) | k4_tarski(sK9(X0,X1,X8),sK10(X0,X1,X8)) = X8) )),
% 1.28/0.53    inference(equality_resolution,[],[f28])).
% 1.28/0.53  fof(f28,plain,(
% 1.28/0.53    ( ! [X2,X0,X8,X1] : (k4_tarski(sK9(X0,X1,X8),sK10(X0,X1,X8)) = X8 | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.28/0.53    inference(cnf_transformation,[],[f17])).
% 1.28/0.53  fof(f17,plain,(
% 1.28/0.53    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK6(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((sK6(X0,X1,X2) = k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK9(X0,X1,X8),sK10(X0,X1,X8)) = X8 & r2_hidden(sK10(X0,X1,X8),X1) & r2_hidden(sK9(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.28/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f13,f16,f15,f14])).
% 1.28/0.53  fof(f14,plain,(
% 1.28/0.53    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK6(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK6(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f15,plain,(
% 1.28/0.53    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK6(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (sK6(X0,X1,X2) = k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X0)))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f16,plain,(
% 1.28/0.53    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK9(X0,X1,X8),sK10(X0,X1,X8)) = X8 & r2_hidden(sK10(X0,X1,X8),X1) & r2_hidden(sK9(X0,X1,X8),X0)))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f13,plain,(
% 1.28/0.53    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.28/0.53    inference(rectify,[],[f12])).
% 1.28/0.53  fof(f12,plain,(
% 1.28/0.53    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.28/0.53    inference(nnf_transformation,[],[f1])).
% 1.28/0.53  fof(f1,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.28/0.53  fof(f86,plain,(
% 1.28/0.53    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4)) | ~spl11_5),
% 1.28/0.53    inference(avatar_component_clause,[],[f65])).
% 1.28/0.53  fof(f41,plain,(
% 1.28/0.53    ( ! [X0,X8,X1] : (r2_hidden(sK10(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 1.28/0.53    inference(equality_resolution,[],[f27])).
% 1.28/0.53  fof(f27,plain,(
% 1.28/0.53    ( ! [X2,X0,X8,X1] : (r2_hidden(sK10(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.28/0.53    inference(cnf_transformation,[],[f17])).
% 1.28/0.53  fof(f101,plain,(
% 1.28/0.53    ~spl11_5 | spl11_2 | ~spl11_5),
% 1.28/0.53    inference(avatar_split_clause,[],[f100,f65,f47,f65])).
% 1.28/0.53  fof(f47,plain,(
% 1.28/0.53    spl11_2 <=> r2_hidden(sK0,sK3)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.28/0.53  fof(f100,plain,(
% 1.28/0.53    r2_hidden(sK0,sK3) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4)) | ~spl11_5),
% 1.28/0.53    inference(superposition,[],[f42,f94])).
% 1.28/0.53  fof(f94,plain,(
% 1.28/0.53    sK0 = sK9(sK3,sK4,k4_tarski(sK0,sK1)) | ~spl11_5),
% 1.28/0.53    inference(forward_demodulation,[],[f92,f22])).
% 1.28/0.53  fof(f22,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.28/0.53    inference(cnf_transformation,[],[f4])).
% 1.28/0.53  fof(f92,plain,(
% 1.28/0.53    sK9(sK3,sK4,k4_tarski(sK0,sK1)) = k1_mcart_1(k4_tarski(sK0,sK1)) | ~spl11_5),
% 1.28/0.53    inference(superposition,[],[f22,f88])).
% 1.28/0.53  fof(f42,plain,(
% 1.28/0.53    ( ! [X0,X8,X1] : (r2_hidden(sK9(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 1.28/0.53    inference(equality_resolution,[],[f26])).
% 1.28/0.53  fof(f26,plain,(
% 1.28/0.53    ( ! [X2,X0,X8,X1] : (r2_hidden(sK9(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.28/0.53    inference(cnf_transformation,[],[f17])).
% 1.28/0.53  fof(f87,plain,(
% 1.28/0.53    ~spl11_1 | spl11_5 | ~spl11_1),
% 1.28/0.53    inference(avatar_split_clause,[],[f85,f44,f65,f44])).
% 1.28/0.53  fof(f44,plain,(
% 1.28/0.53    spl11_1 <=> r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.28/0.53  fof(f85,plain,(
% 1.28/0.53    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4)) | ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | ~spl11_1),
% 1.28/0.53    inference(superposition,[],[f42,f75])).
% 1.28/0.53  fof(f75,plain,(
% 1.28/0.53    k4_tarski(sK0,sK1) = sK9(k2_zfmisc_1(sK3,sK4),sK5,k4_tarski(k4_tarski(sK0,sK1),sK2)) | ~spl11_1),
% 1.28/0.53    inference(forward_demodulation,[],[f73,f22])).
% 1.28/0.53  fof(f73,plain,(
% 1.28/0.53    sK9(k2_zfmisc_1(sK3,sK4),sK5,k4_tarski(k4_tarski(sK0,sK1),sK2)) = k1_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)) | ~spl11_1),
% 1.28/0.53    inference(superposition,[],[f22,f70])).
% 1.28/0.53  fof(f70,plain,(
% 1.28/0.53    k4_tarski(k4_tarski(sK0,sK1),sK2) = k4_tarski(sK9(k2_zfmisc_1(sK3,sK4),sK5,k4_tarski(k4_tarski(sK0,sK1),sK2)),sK10(k2_zfmisc_1(sK3,sK4),sK5,k4_tarski(k4_tarski(sK0,sK1),sK2))) | ~spl11_1),
% 1.28/0.53    inference(resolution,[],[f56,f40])).
% 1.28/0.53  fof(f56,plain,(
% 1.28/0.53    r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | ~spl11_1),
% 1.28/0.53    inference(avatar_component_clause,[],[f44])).
% 1.28/0.53  fof(f79,plain,(
% 1.28/0.53    ~spl11_1 | spl11_4 | ~spl11_1),
% 1.28/0.53    inference(avatar_split_clause,[],[f78,f44,f53,f44])).
% 1.28/0.53  fof(f53,plain,(
% 1.28/0.53    spl11_4 <=> r2_hidden(sK2,sK5)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 1.28/0.53  fof(f78,plain,(
% 1.28/0.53    r2_hidden(sK2,sK5) | ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | ~spl11_1),
% 1.28/0.53    inference(superposition,[],[f41,f76])).
% 1.28/0.53  fof(f76,plain,(
% 1.28/0.53    sK2 = sK10(k2_zfmisc_1(sK3,sK4),sK5,k4_tarski(k4_tarski(sK0,sK1),sK2)) | ~spl11_1),
% 1.28/0.53    inference(forward_demodulation,[],[f74,f23])).
% 1.28/0.53  fof(f74,plain,(
% 1.28/0.53    sK10(k2_zfmisc_1(sK3,sK4),sK5,k4_tarski(k4_tarski(sK0,sK1),sK2)) = k2_mcart_1(k4_tarski(k4_tarski(sK0,sK1),sK2)) | ~spl11_1),
% 1.28/0.53    inference(superposition,[],[f23,f70])).
% 1.28/0.53  fof(f69,plain,(
% 1.28/0.53    ~spl11_2 | ~spl11_3 | spl11_5),
% 1.28/0.53    inference(avatar_split_clause,[],[f68,f65,f50,f47])).
% 1.28/0.53  fof(f68,plain,(
% 1.28/0.53    ~r2_hidden(sK1,sK4) | ~r2_hidden(sK0,sK3) | spl11_5),
% 1.28/0.53    inference(resolution,[],[f66,f39])).
% 1.28/0.53  fof(f39,plain,(
% 1.28/0.53    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 1.28/0.53    inference(equality_resolution,[],[f38])).
% 1.28/0.53  fof(f38,plain,(
% 1.28/0.53    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.28/0.53    inference(equality_resolution,[],[f29])).
% 1.28/0.53  fof(f29,plain,(
% 1.28/0.53    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.28/0.53    inference(cnf_transformation,[],[f17])).
% 1.28/0.53  fof(f66,plain,(
% 1.28/0.53    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4)) | spl11_5),
% 1.28/0.53    inference(avatar_component_clause,[],[f65])).
% 1.28/0.53  fof(f67,plain,(
% 1.28/0.53    ~spl11_5 | ~spl11_4 | spl11_1),
% 1.28/0.53    inference(avatar_split_clause,[],[f63,f44,f53,f65])).
% 1.28/0.53  fof(f63,plain,(
% 1.28/0.53    ~r2_hidden(sK2,sK5) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK3,sK4)) | spl11_1),
% 1.28/0.53    inference(resolution,[],[f45,f39])).
% 1.28/0.53  fof(f45,plain,(
% 1.28/0.53    ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | spl11_1),
% 1.28/0.53    inference(avatar_component_clause,[],[f44])).
% 1.28/0.53  fof(f62,plain,(
% 1.28/0.53    spl11_1 | spl11_2),
% 1.28/0.53    inference(avatar_split_clause,[],[f37,f47,f44])).
% 1.28/0.53  fof(f37,plain,(
% 1.28/0.53    r2_hidden(sK0,sK3) | r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 1.28/0.53    inference(definition_unfolding,[],[f18,f25,f24])).
% 1.28/0.53  fof(f24,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f3])).
% 1.28/0.53  fof(f3,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.28/0.53  fof(f25,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f2])).
% 1.28/0.53  fof(f2,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.28/0.53  fof(f18,plain,(
% 1.28/0.53    r2_hidden(sK0,sK3) | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5))),
% 1.28/0.53    inference(cnf_transformation,[],[f11])).
% 1.28/0.53  fof(f11,plain,(
% 1.28/0.53    (~r2_hidden(sK2,sK5) | ~r2_hidden(sK1,sK4) | ~r2_hidden(sK0,sK3) | ~r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5))) & ((r2_hidden(sK2,sK5) & r2_hidden(sK1,sK4) & r2_hidden(sK0,sK3)) | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5)))),
% 1.28/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f9,f10])).
% 1.28/0.53  fof(f10,plain,(
% 1.28/0.53    ? [X0,X1,X2,X3,X4,X5] : ((~r2_hidden(X2,X5) | ~r2_hidden(X1,X4) | ~r2_hidden(X0,X3) | ~r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))) & ((r2_hidden(X2,X5) & r2_hidden(X1,X4) & r2_hidden(X0,X3)) | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)))) => ((~r2_hidden(sK2,sK5) | ~r2_hidden(sK1,sK4) | ~r2_hidden(sK0,sK3) | ~r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5))) & ((r2_hidden(sK2,sK5) & r2_hidden(sK1,sK4) & r2_hidden(sK0,sK3)) | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5))))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f9,plain,(
% 1.28/0.53    ? [X0,X1,X2,X3,X4,X5] : ((~r2_hidden(X2,X5) | ~r2_hidden(X1,X4) | ~r2_hidden(X0,X3) | ~r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))) & ((r2_hidden(X2,X5) & r2_hidden(X1,X4) & r2_hidden(X0,X3)) | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))))),
% 1.28/0.53    inference(flattening,[],[f8])).
% 1.28/0.53  fof(f8,plain,(
% 1.28/0.53    ? [X0,X1,X2,X3,X4,X5] : (((~r2_hidden(X2,X5) | ~r2_hidden(X1,X4) | ~r2_hidden(X0,X3)) | ~r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))) & ((r2_hidden(X2,X5) & r2_hidden(X1,X4) & r2_hidden(X0,X3)) | r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))))),
% 1.28/0.53    inference(nnf_transformation,[],[f7])).
% 1.28/0.53  fof(f7,plain,(
% 1.28/0.53    ? [X0,X1,X2,X3,X4,X5] : (r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) <~> (r2_hidden(X2,X5) & r2_hidden(X1,X4) & r2_hidden(X0,X3)))),
% 1.28/0.53    inference(ennf_transformation,[],[f6])).
% 1.28/0.53  fof(f6,negated_conjecture,(
% 1.28/0.53    ~! [X0,X1,X2,X3,X4,X5] : (r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) <=> (r2_hidden(X2,X5) & r2_hidden(X1,X4) & r2_hidden(X0,X3)))),
% 1.28/0.53    inference(negated_conjecture,[],[f5])).
% 1.28/0.53  fof(f5,conjecture,(
% 1.28/0.53    ! [X0,X1,X2,X3,X4,X5] : (r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) <=> (r2_hidden(X2,X5) & r2_hidden(X1,X4) & r2_hidden(X0,X3)))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_mcart_1)).
% 1.28/0.53  fof(f60,plain,(
% 1.28/0.53    spl11_1 | spl11_3),
% 1.28/0.53    inference(avatar_split_clause,[],[f36,f50,f44])).
% 1.28/0.53  fof(f36,plain,(
% 1.28/0.53    r2_hidden(sK1,sK4) | r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 1.28/0.53    inference(definition_unfolding,[],[f19,f25,f24])).
% 1.28/0.53  fof(f19,plain,(
% 1.28/0.53    r2_hidden(sK1,sK4) | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5))),
% 1.28/0.53    inference(cnf_transformation,[],[f11])).
% 1.28/0.53  fof(f58,plain,(
% 1.28/0.53    spl11_1 | spl11_4),
% 1.28/0.53    inference(avatar_split_clause,[],[f35,f53,f44])).
% 1.28/0.53  fof(f35,plain,(
% 1.28/0.53    r2_hidden(sK2,sK5) | r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 1.28/0.53    inference(definition_unfolding,[],[f20,f25,f24])).
% 1.28/0.53  fof(f20,plain,(
% 1.28/0.53    r2_hidden(sK2,sK5) | r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5))),
% 1.28/0.53    inference(cnf_transformation,[],[f11])).
% 1.28/0.53  fof(f55,plain,(
% 1.28/0.53    ~spl11_1 | ~spl11_2 | ~spl11_3 | ~spl11_4),
% 1.28/0.53    inference(avatar_split_clause,[],[f34,f53,f50,f47,f44])).
% 1.28/0.53  fof(f34,plain,(
% 1.28/0.53    ~r2_hidden(sK2,sK5) | ~r2_hidden(sK1,sK4) | ~r2_hidden(sK0,sK3) | ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 1.28/0.53    inference(definition_unfolding,[],[f21,f25,f24])).
% 1.28/0.53  fof(f21,plain,(
% 1.28/0.53    ~r2_hidden(sK2,sK5) | ~r2_hidden(sK1,sK4) | ~r2_hidden(sK0,sK3) | ~r2_hidden(k3_mcart_1(sK0,sK1,sK2),k3_zfmisc_1(sK3,sK4,sK5))),
% 1.28/0.53    inference(cnf_transformation,[],[f11])).
% 1.28/0.53  % SZS output end Proof for theBenchmark
% 1.28/0.53  % (16987)------------------------------
% 1.28/0.53  % (16987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (16987)Termination reason: Refutation
% 1.28/0.53  
% 1.28/0.53  % (16987)Memory used [KB]: 10746
% 1.28/0.53  % (16987)Time elapsed: 0.117 s
% 1.28/0.53  % (16987)------------------------------
% 1.28/0.53  % (16987)------------------------------
% 1.28/0.53  % (17006)Refutation not found, incomplete strategy% (17006)------------------------------
% 1.28/0.53  % (17006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (17006)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (17006)Memory used [KB]: 10746
% 1.28/0.53  % (17006)Time elapsed: 0.121 s
% 1.28/0.53  % (17006)------------------------------
% 1.28/0.53  % (17006)------------------------------
% 1.28/0.54  % (16999)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.28/0.54  % (17014)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.28/0.54  % (17000)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.28/0.54  % (16991)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.28/0.54  % (16993)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.54  % (16996)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.54  % (17002)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.55  % (17009)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.55  % (16994)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.41/0.55  % (16982)Success in time 0.186 s
%------------------------------------------------------------------------------
