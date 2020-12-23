%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 108 expanded)
%              Number of leaves         :    9 (  38 expanded)
%              Depth                    :   21
%              Number of atoms          :  223 ( 761 expanded)
%              Number of equality atoms :   55 ( 190 expanded)
%              Maximal formula depth    :   15 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f54,plain,(
    $false ),
    inference(resolution,[],[f53,f33])).

fof(f33,plain,(
    r2_hidden(sK1,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(definition_unfolding,[],[f18,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f18,plain,(
    r2_hidden(sK1,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ! [X4,X5,X6] :
        ( k3_mcart_1(X4,X5,X6) != sK1
        | ~ r2_hidden(X6,sK4)
        | ~ r2_hidden(X5,sK3)
        | ~ r2_hidden(X4,sK2) )
    & r2_hidden(sK1,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4,X5,X6] :
            ( k3_mcart_1(X4,X5,X6) != X0
            | ~ r2_hidden(X6,X3)
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X4,X1) )
        & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) )
   => ( ! [X6,X5,X4] :
          ( k3_mcart_1(X4,X5,X6) != sK1
          | ~ r2_hidden(X6,sK4)
          | ~ r2_hidden(X5,sK3)
          | ~ r2_hidden(X4,sK2) )
      & r2_hidden(sK1,k3_zfmisc_1(sK2,sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5,X6] :
          ( k3_mcart_1(X4,X5,X6) != X0
          | ~ r2_hidden(X6,X3)
          | ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4,X5,X6] :
              ~ ( k3_mcart_1(X4,X5,X6) = X0
                & r2_hidden(X6,X3)
                & r2_hidden(X5,X2)
                & r2_hidden(X4,X1) )
          & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5,X6] :
            ~ ( k3_mcart_1(X4,X5,X6) = X0
              & r2_hidden(X6,X3)
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_mcart_1)).

fof(f53,plain,(
    ~ r2_hidden(sK1,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ) ),
    inference(duplicate_literal_removal,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ) ),
    inference(resolution,[],[f50,f35])).

fof(f35,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_zfmisc_1(X0,X1)) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f7])).

fof(f7,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

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

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK4,k2_zfmisc_1(sK2,sK3),X1)
      | sK1 != X0
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | sK1 != X0
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
      | ~ sP0(sK4,k2_zfmisc_1(sK2,sK3),X1)
      | ~ sP0(sK4,k2_zfmisc_1(sK2,sK3),X1) ) ),
    inference(condensation,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sK1 != X0
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
      | ~ r2_hidden(X0,X1)
      | ~ sP0(sK4,k2_zfmisc_1(sK2,sK3),X1)
      | ~ r2_hidden(X0,X2)
      | ~ sP0(sK4,k2_zfmisc_1(sK2,sK3),X2) ) ),
    inference(resolution,[],[f47,f22])).

fof(f22,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK8(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK5(X0,X1,X2)
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X1) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2))
              & r2_hidden(sK7(X0,X1,X2),X0)
              & r2_hidden(sK6(X0,X1,X2),X1) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X0)
                  | ~ r2_hidden(X9,X1) ) )
            & ( ( k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8
                & r2_hidden(sK9(X0,X1,X8),X0)
                & r2_hidden(sK8(X0,X1,X8),X1) )
              | ~ r2_hidden(X8,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f12,f15,f14,f13])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X0)
                & r2_hidden(X6,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK5(X0,X1,X2)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X1) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK5(X0,X1,X2)
              & r2_hidden(X7,X0)
              & r2_hidden(X6,X1) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK5(X0,X1,X2)
          & r2_hidden(X7,X0)
          & r2_hidden(X6,X1) )
     => ( sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2))
        & r2_hidden(sK7(X0,X1,X2),X0)
        & r2_hidden(sK6(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X0)
          & r2_hidden(X11,X1) )
     => ( k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8
        & r2_hidden(sK9(X0,X1,X8),X0)
        & r2_hidden(sK8(X0,X1,X8),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X0)
                  | ~ r2_hidden(X4,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X0)
                  & r2_hidden(X6,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X0)
                  | ~ r2_hidden(X9,X1) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X0)
                  & r2_hidden(X11,X1) )
              | ~ r2_hidden(X8,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK8(sK4,X1,X0),k2_zfmisc_1(sK2,sK3))
      | sK1 != X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,sK4))
      | ~ r2_hidden(X0,X2)
      | ~ sP0(sK4,X1,X2) ) ),
    inference(resolution,[],[f46,f23])).

fof(f23,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK9(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1,X2),sK4)
      | sK1 != X2
      | ~ r2_hidden(sK8(X0,X1,X2),k2_zfmisc_1(sK2,sK3))
      | ~ r2_hidden(X2,k2_zfmisc_1(X1,X0)) ) ),
    inference(superposition,[],[f45,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK8(X2,X1,X0),sK9(X2,X1,X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(resolution,[],[f24,f35])).

fof(f24,plain,(
    ! [X2,X0,X8,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X8,X2)
      | k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,X1) != sK1
      | ~ r2_hidden(X1,sK4)
      | ~ r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) ) ),
    inference(duplicate_literal_removal,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,X1) != sK1
      | ~ r2_hidden(X1,sK4)
      | ~ r2_hidden(X0,k2_zfmisc_1(sK2,sK3))
      | ~ r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) ) ),
    inference(resolution,[],[f43,f35])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(sK3,sK2,X1)
      | sK1 != k4_tarski(X0,X2)
      | ~ r2_hidden(X2,sK4)
      | ~ r2_hidden(X0,k2_zfmisc_1(sK2,sK3))
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | sK1 != k4_tarski(X0,X2)
      | ~ r2_hidden(X2,sK4)
      | ~ r2_hidden(X0,k2_zfmisc_1(sK2,sK3))
      | ~ sP0(sK3,sK2,X1)
      | ~ sP0(sK3,sK2,X1) ) ),
    inference(condensation,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != sK1
      | ~ r2_hidden(X1,sK4)
      | ~ r2_hidden(X0,k2_zfmisc_1(sK2,sK3))
      | ~ r2_hidden(X0,X2)
      | ~ sP0(sK3,sK2,X2)
      | ~ r2_hidden(X0,X3)
      | ~ sP0(sK3,sK2,X3) ) ),
    inference(resolution,[],[f40,f22])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK8(sK3,X2,X1),sK2)
      | sK1 != k4_tarski(X1,X0)
      | ~ r2_hidden(X0,sK4)
      | ~ r2_hidden(X1,k2_zfmisc_1(X2,sK3))
      | ~ r2_hidden(X1,X3)
      | ~ sP0(sK3,X2,X3) ) ),
    inference(resolution,[],[f39,f23])).

fof(f39,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r2_hidden(sK9(X6,X7,X8),sK3)
      | ~ r2_hidden(X9,sK4)
      | sK1 != k4_tarski(X8,X9)
      | ~ r2_hidden(sK8(X6,X7,X8),sK2)
      | ~ r2_hidden(X8,k2_zfmisc_1(X7,X6)) ) ),
    inference(superposition,[],[f32,f37])).

fof(f32,plain,(
    ! [X6,X4,X5] :
      ( sK1 != k4_tarski(k4_tarski(X4,X5),X6)
      | ~ r2_hidden(X6,sK4)
      | ~ r2_hidden(X5,sK3)
      | ~ r2_hidden(X4,sK2) ) ),
    inference(definition_unfolding,[],[f19,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f19,plain,(
    ! [X6,X4,X5] :
      ( k3_mcart_1(X4,X5,X6) != sK1
      | ~ r2_hidden(X6,sK4)
      | ~ r2_hidden(X5,sK3)
      | ~ r2_hidden(X4,sK2) ) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:33:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (21095)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.50  % (21075)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (21089)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (21075)Refutation not found, incomplete strategy% (21075)------------------------------
% 0.20/0.51  % (21075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (21095)Refutation not found, incomplete strategy% (21095)------------------------------
% 0.20/0.51  % (21095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (21095)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (21095)Memory used [KB]: 10618
% 0.20/0.51  % (21095)Time elapsed: 0.111 s
% 0.20/0.51  % (21095)------------------------------
% 0.20/0.51  % (21095)------------------------------
% 0.20/0.51  % (21075)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (21075)Memory used [KB]: 10874
% 0.20/0.51  % (21075)Time elapsed: 0.100 s
% 0.20/0.51  % (21075)------------------------------
% 0.20/0.51  % (21075)------------------------------
% 0.20/0.51  % (21081)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (21085)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (21079)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (21085)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(resolution,[],[f53,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    r2_hidden(sK1,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 0.20/0.52    inference(definition_unfolding,[],[f18,f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    r2_hidden(sK1,k3_zfmisc_1(sK2,sK3,sK4))),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ! [X4,X5,X6] : (k3_mcart_1(X4,X5,X6) != sK1 | ~r2_hidden(X6,sK4) | ~r2_hidden(X5,sK3) | ~r2_hidden(X4,sK2)) & r2_hidden(sK1,k3_zfmisc_1(sK2,sK3,sK4))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f6,f9])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : (! [X4,X5,X6] : (k3_mcart_1(X4,X5,X6) != X0 | ~r2_hidden(X6,X3) | ~r2_hidden(X5,X2) | ~r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3))) => (! [X6,X5,X4] : (k3_mcart_1(X4,X5,X6) != sK1 | ~r2_hidden(X6,sK4) | ~r2_hidden(X5,sK3) | ~r2_hidden(X4,sK2)) & r2_hidden(sK1,k3_zfmisc_1(sK2,sK3,sK4)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f6,plain,(
% 0.20/0.52    ? [X0,X1,X2,X3] : (! [X4,X5,X6] : (k3_mcart_1(X4,X5,X6) != X0 | ~r2_hidden(X6,X3) | ~r2_hidden(X5,X2) | ~r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2,X3] : ~(! [X4,X5,X6] : ~(k3_mcart_1(X4,X5,X6) = X0 & r2_hidden(X6,X3) & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)))),
% 0.20/0.52    inference(negated_conjecture,[],[f4])).
% 0.20/0.52  fof(f4,conjecture,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ~(! [X4,X5,X6] : ~(k3_mcart_1(X4,X5,X6) = X0 & r2_hidden(X6,X3) & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_mcart_1)).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ~r2_hidden(sK1,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 0.20/0.52    inference(equality_resolution,[],[f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X0] : (sK1 != X0 | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0] : (sK1 != X0 | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))) )),
% 0.20/0.52    inference(resolution,[],[f50,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X0,X1] : (sP0(X1,X0,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_zfmisc_1(X0,X1) != X2))),
% 0.20/0.52    inference(nnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.20/0.52    inference(definition_folding,[],[f1,f7])).
% 0.20/0.52  fof(f7,plain,(
% 0.20/0.52    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~sP0(sK4,k2_zfmisc_1(sK2,sK3),X1) | sK1 != X0 | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | sK1 != X0 | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) | ~sP0(sK4,k2_zfmisc_1(sK2,sK3),X1) | ~sP0(sK4,k2_zfmisc_1(sK2,sK3),X1)) )),
% 0.20/0.52    inference(condensation,[],[f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (sK1 != X0 | ~r2_hidden(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) | ~r2_hidden(X0,X1) | ~sP0(sK4,k2_zfmisc_1(sK2,sK3),X1) | ~r2_hidden(X0,X2) | ~sP0(sK4,k2_zfmisc_1(sK2,sK3),X2)) )),
% 0.20/0.52    inference(resolution,[],[f47,f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ( ! [X2,X0,X8,X1] : (r2_hidden(sK8(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | ~sP0(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4,X5] : (k4_tarski(X4,X5) != sK5(X0,X1,X2) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_hidden(sK7(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1))) & ((k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8 & r2_hidden(sK9(X0,X1,X8),X0) & r2_hidden(sK8(X0,X1,X8),X1)) | ~r2_hidden(X8,X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f12,f15,f14,f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK5(X0,X1,X2) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK5(X0,X1,X2) & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X2,X1,X0] : (? [X7,X6] : (k4_tarski(X6,X7) = sK5(X0,X1,X2) & r2_hidden(X7,X0) & r2_hidden(X6,X1)) => (sK5(X0,X1,X2) = k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) & r2_hidden(sK7(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X0) & r2_hidden(X11,X1)) => (k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8 & r2_hidden(sK9(X0,X1,X8),X0) & r2_hidden(sK8(X0,X1,X8),X1)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X1)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X0) & r2_hidden(X6,X1)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X0) | ~r2_hidden(X9,X1))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X0) & r2_hidden(X11,X1)) | ~r2_hidden(X8,X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.52    inference(rectify,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.20/0.52    inference(nnf_transformation,[],[f7])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(sK8(sK4,X1,X0),k2_zfmisc_1(sK2,sK3)) | sK1 != X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,sK4)) | ~r2_hidden(X0,X2) | ~sP0(sK4,X1,X2)) )),
% 0.20/0.52    inference(resolution,[],[f46,f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ( ! [X2,X0,X8,X1] : (r2_hidden(sK9(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | ~sP0(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(sK9(X0,X1,X2),sK4) | sK1 != X2 | ~r2_hidden(sK8(X0,X1,X2),k2_zfmisc_1(sK2,sK3)) | ~r2_hidden(X2,k2_zfmisc_1(X1,X0))) )),
% 0.20/0.52    inference(superposition,[],[f45,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k4_tarski(sK8(X2,X1,X0),sK9(X2,X1,X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.52    inference(resolution,[],[f24,f35])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ( ! [X2,X0,X8,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X8,X2) | k4_tarski(sK8(X0,X1,X8),sK9(X0,X1,X8)) = X8) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_tarski(X0,X1) != sK1 | ~r2_hidden(X1,sK4) | ~r2_hidden(X0,k2_zfmisc_1(sK2,sK3))) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_tarski(X0,X1) != sK1 | ~r2_hidden(X1,sK4) | ~r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) | ~r2_hidden(X0,k2_zfmisc_1(sK2,sK3))) )),
% 0.20/0.52    inference(resolution,[],[f43,f35])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~sP0(sK3,sK2,X1) | sK1 != k4_tarski(X0,X2) | ~r2_hidden(X2,sK4) | ~r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | sK1 != k4_tarski(X0,X2) | ~r2_hidden(X2,sK4) | ~r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) | ~sP0(sK3,sK2,X1) | ~sP0(sK3,sK2,X1)) )),
% 0.20/0.52    inference(condensation,[],[f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (k4_tarski(X0,X1) != sK1 | ~r2_hidden(X1,sK4) | ~r2_hidden(X0,k2_zfmisc_1(sK2,sK3)) | ~r2_hidden(X0,X2) | ~sP0(sK3,sK2,X2) | ~r2_hidden(X0,X3) | ~sP0(sK3,sK2,X3)) )),
% 0.20/0.52    inference(resolution,[],[f40,f22])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK8(sK3,X2,X1),sK2) | sK1 != k4_tarski(X1,X0) | ~r2_hidden(X0,sK4) | ~r2_hidden(X1,k2_zfmisc_1(X2,sK3)) | ~r2_hidden(X1,X3) | ~sP0(sK3,X2,X3)) )),
% 0.20/0.52    inference(resolution,[],[f39,f23])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X6,X8,X7,X9] : (~r2_hidden(sK9(X6,X7,X8),sK3) | ~r2_hidden(X9,sK4) | sK1 != k4_tarski(X8,X9) | ~r2_hidden(sK8(X6,X7,X8),sK2) | ~r2_hidden(X8,k2_zfmisc_1(X7,X6))) )),
% 0.20/0.52    inference(superposition,[],[f32,f37])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X6,X4,X5] : (sK1 != k4_tarski(k4_tarski(X4,X5),X6) | ~r2_hidden(X6,sK4) | ~r2_hidden(X5,sK3) | ~r2_hidden(X4,sK2)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f19,f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ( ! [X6,X4,X5] : (k3_mcart_1(X4,X5,X6) != sK1 | ~r2_hidden(X6,sK4) | ~r2_hidden(X5,sK3) | ~r2_hidden(X4,sK2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (21085)------------------------------
% 0.20/0.52  % (21085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (21085)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (21085)Memory used [KB]: 6268
% 0.20/0.52  % (21085)Time elapsed: 0.113 s
% 0.20/0.52  % (21085)------------------------------
% 0.20/0.52  % (21085)------------------------------
% 0.20/0.52  % (21077)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.30/0.52  % (21069)Success in time 0.162 s
%------------------------------------------------------------------------------
