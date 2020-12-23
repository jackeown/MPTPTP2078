%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t2_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:06 EDT 2019

% Result     : Theorem 10.20s
% Output     : Refutation 10.20s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 295 expanded)
%              Number of leaves         :   35 ( 105 expanded)
%              Depth                    :   15
%              Number of atoms          :  466 (1130 expanded)
%              Number of equality atoms :   62 ( 169 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f226444,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f122,f127,f616,f637,f217799,f217821,f220043,f221740,f221763,f226434,f226437])).

fof(f226437,plain,
    ( spl10_2998
    | spl10_3449 ),
    inference(avatar_split_clause,[],[f226435,f226432,f217785])).

fof(f217785,plain,
    ( spl10_2998
  <=> k1_xboole_0 = k2_xboole_0(sK0,sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2998])])).

fof(f226432,plain,
    ( spl10_3449
  <=> ~ r2_hidden(sK2(k2_xboole_0(sK0,sK4(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3449])])).

fof(f226435,plain,
    ( k1_xboole_0 = k2_xboole_0(sK0,sK4(sK0))
    | ~ spl10_3449 ),
    inference(resolution,[],[f226433,f44111])).

fof(f44111,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k2_xboole_0(X0,sK4(X0))),X0)
      | k1_xboole_0 = k2_xboole_0(X0,sK4(X0)) ) ),
    inference(duplicate_literal_removal,[],[f44110])).

fof(f44110,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_xboole_0(X0,sK4(X0))
      | r2_hidden(sK2(k2_xboole_0(X0,sK4(X0))),X0)
      | k1_xboole_0 = k2_xboole_0(X0,sK4(X0)) ) ),
    inference(forward_demodulation,[],[f44064,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t2_mcart_1.p',commutativity_k2_xboole_0)).

fof(f44064,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k2_xboole_0(X0,sK4(X0))),X0)
      | k1_xboole_0 = k2_xboole_0(X0,sK4(X0))
      | k1_xboole_0 = k2_xboole_0(sK4(X0),X0) ) ),
    inference(resolution,[],[f8570,f6215])).

fof(f6215,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(sK2(k2_xboole_0(X6,X7)),sK4(X7))
      | k1_xboole_0 = k2_xboole_0(X6,X7) ) ),
    inference(resolution,[],[f854,f75])).

fof(f75,plain,(
    ! [X2,X0] :
      ( ~ r1_xboole_0(X2,X0)
      | ~ r2_hidden(X2,sK4(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X2] :
      ( ( r2_hidden(X2,sK4(X0))
        | r1_xboole_0(X2,X0)
        | ~ r2_hidden(X2,k3_tarski(X0)) )
      & ( ( ~ r1_xboole_0(X2,X0)
          & r2_hidden(X2,k3_tarski(X0)) )
        | ~ r2_hidden(X2,sK4(X0)) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ( r2_hidden(X2,X1)
            | r1_xboole_0(X2,X0)
            | ~ r2_hidden(X2,k3_tarski(X0)) )
          & ( ( ~ r1_xboole_0(X2,X0)
              & r2_hidden(X2,k3_tarski(X0)) )
            | ~ r2_hidden(X2,X1) ) )
     => ! [X2] :
          ( ( r2_hidden(X2,sK4(X0))
            | r1_xboole_0(X2,X0)
            | ~ r2_hidden(X2,k3_tarski(X0)) )
          & ( ( ~ r1_xboole_0(X2,X0)
              & r2_hidden(X2,k3_tarski(X0)) )
            | ~ r2_hidden(X2,sK4(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | r1_xboole_0(X2,X0)
        | ~ r2_hidden(X2,k3_tarski(X0)) )
      & ( ( ~ r1_xboole_0(X2,X0)
          & r2_hidden(X2,k3_tarski(X0)) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | r1_xboole_0(X2,X0)
        | ~ r2_hidden(X2,k3_tarski(X0)) )
      & ( ( ~ r1_xboole_0(X2,X0)
          & r2_hidden(X2,k3_tarski(X0)) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( r2_hidden(X2,X1)
    <=> ( ~ r1_xboole_0(X2,X0)
        & r2_hidden(X2,k3_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t2_mcart_1.p',s1_xboole_0__e1_2__mcart_1)).

fof(f854,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(sK2(k2_xboole_0(X0,X1)),X1)
      | k1_xboole_0 = k2_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f97,f72])).

fof(f72,plain,(
    ! [X0] :
      ( r1_xboole_0(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( r1_xboole_0(sK2(X0),X0)
        & r2_hidden(sK2(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r1_xboole_0(X1,X0)
          & r2_hidden(X1,X0) )
     => ( r1_xboole_0(sK2(X0),X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r1_xboole_0(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t2_mcart_1.p',t1_mcart_1)).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t2_mcart_1.p',t70_xboole_1)).

fof(f8570,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK2(k2_xboole_0(X3,X2)),X3)
      | r2_hidden(sK2(k2_xboole_0(X2,X3)),X2)
      | k1_xboole_0 = k2_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f1596,f78])).

fof(f1596,plain,(
    ! [X10,X11] :
      ( r2_hidden(sK2(k2_xboole_0(X10,X11)),X11)
      | r2_hidden(sK2(k2_xboole_0(X10,X11)),X10)
      | k1_xboole_0 = k2_xboole_0(X10,X11) ) ),
    inference(resolution,[],[f109,f71])).

fof(f71,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f109,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK9(X0,X1,X2),X1)
              & ~ r2_hidden(sK9(X0,X1,X2),X0) )
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( r2_hidden(sK9(X0,X1,X2),X1)
            | r2_hidden(sK9(X0,X1,X2),X0)
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f62,f63])).

fof(f63,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK9(X0,X1,X2),X1)
            & ~ r2_hidden(sK9(X0,X1,X2),X0) )
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( r2_hidden(sK9(X0,X1,X2),X1)
          | r2_hidden(sK9(X0,X1,X2),X0)
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
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
    inference(rectify,[],[f61])).

fof(f61,plain,(
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
    inference(flattening,[],[f60])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t2_mcart_1.p',d3_xboole_0)).

fof(f226433,plain,
    ( ~ r2_hidden(sK2(k2_xboole_0(sK0,sK4(sK0))),sK0)
    | ~ spl10_3449 ),
    inference(avatar_component_clause,[],[f226432])).

fof(f226434,plain,
    ( ~ spl10_3449
    | ~ spl10_3442 ),
    inference(avatar_split_clause,[],[f226430,f221735,f226432])).

fof(f221735,plain,
    ( spl10_3442
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(sK1(sK2(k2_xboole_0(sK0,sK4(sK0)))),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3442])])).

fof(f226430,plain,
    ( ~ r2_hidden(sK2(k2_xboole_0(sK0,sK4(sK0))),sK0)
    | ~ spl10_3442 ),
    inference(duplicate_literal_removal,[],[f226423])).

fof(f226423,plain,
    ( ~ r2_hidden(sK2(k2_xboole_0(sK0,sK4(sK0))),sK0)
    | ~ r2_hidden(sK2(k2_xboole_0(sK0,sK4(sK0))),sK0)
    | ~ spl10_3442 ),
    inference(resolution,[],[f221736,f66])).

fof(f66,plain,(
    ! [X1] :
      ( r2_hidden(sK1(X1),X1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ! [X1] :
        ( ( ~ r1_xboole_0(sK1(X1),sK0)
          & r2_hidden(sK1(X1),X1) )
        | ~ r2_hidden(X1,sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ? [X2] :
                ( ~ r1_xboole_0(X2,X0)
                & r2_hidden(X2,X1) )
            | ~ r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 )
   => ( ! [X1] :
          ( ? [X2] :
              ( ~ r1_xboole_0(X2,sK0)
              & r2_hidden(X2,X1) )
          | ~ r2_hidden(X1,sK0) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_xboole_0(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r1_xboole_0(sK1(X1),X0)
        & r2_hidden(sK1(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ~ r1_xboole_0(X2,X0)
              & r2_hidden(X2,X1) )
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( ! [X2] :
                    ( r2_hidden(X2,X1)
                   => r1_xboole_0(X2,X0) )
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2] :
                  ( r2_hidden(X2,X1)
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t2_mcart_1.p',t2_mcart_1)).

fof(f221736,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1(sK2(k2_xboole_0(sK0,sK4(sK0)))),X0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl10_3442 ),
    inference(avatar_component_clause,[],[f221735])).

fof(f221763,plain,
    ( ~ spl10_3445
    | ~ spl10_3010 ),
    inference(avatar_split_clause,[],[f221756,f217819,f221760])).

fof(f221760,plain,
    ( spl10_3445
  <=> ~ r1_xboole_0(sK1(sK2(k2_xboole_0(sK0,sK4(sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3445])])).

fof(f217819,plain,
    ( spl10_3010
  <=> ! [X27] : ~ r1_xboole_0(sK1(sK2(k2_xboole_0(sK0,sK4(sK0)))),k2_xboole_0(sK0,X27)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3010])])).

fof(f221756,plain,
    ( ~ r1_xboole_0(sK1(sK2(k2_xboole_0(sK0,sK4(sK0)))),sK0)
    | ~ spl10_3010 ),
    inference(superposition,[],[f217820,f77])).

fof(f77,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t2_mcart_1.p',idempotence_k2_xboole_0)).

fof(f217820,plain,
    ( ! [X27] : ~ r1_xboole_0(sK1(sK2(k2_xboole_0(sK0,sK4(sK0)))),k2_xboole_0(sK0,X27))
    | ~ spl10_3010 ),
    inference(avatar_component_clause,[],[f217819])).

fof(f221740,plain,
    ( spl10_3442
    | spl10_3444
    | spl10_3001 ),
    inference(avatar_split_clause,[],[f221733,f217788,f221738,f221735])).

fof(f221738,plain,
    ( spl10_3444
  <=> r1_xboole_0(sK1(sK2(k2_xboole_0(sK0,sK4(sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3444])])).

fof(f217788,plain,
    ( spl10_3001
  <=> ~ r2_hidden(sK1(sK2(k2_xboole_0(sK0,sK4(sK0)))),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3001])])).

fof(f221733,plain,
    ( ! [X0] :
        ( r1_xboole_0(sK1(sK2(k2_xboole_0(sK0,sK4(sK0)))),sK0)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(sK1(sK2(k2_xboole_0(sK0,sK4(sK0)))),X0) )
    | ~ spl10_3001 ),
    inference(resolution,[],[f217789,f1502])).

fof(f1502,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,sK4(X1))
      | r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f76,f104])).

fof(f104,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK6(X0,X1),X3) )
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( ( r2_hidden(sK7(X0,X1),X0)
              & r2_hidden(sK6(X0,X1),sK7(X0,X1)) )
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK8(X0,X5),X0)
                & r2_hidden(X5,sK8(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f55,f58,f57,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK6(X0,X1),X3) )
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK6(X0,X1),X4) )
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK7(X0,X1),X0)
        & r2_hidden(X2,sK7(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK8(X0,X5),X0)
        & r2_hidden(X5,sK8(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t2_mcart_1.p',d4_tarski)).

fof(f76,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k3_tarski(X0))
      | r1_xboole_0(X2,X0)
      | r2_hidden(X2,sK4(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f217789,plain,
    ( ~ r2_hidden(sK1(sK2(k2_xboole_0(sK0,sK4(sK0)))),sK4(sK0))
    | ~ spl10_3001 ),
    inference(avatar_component_clause,[],[f217788])).

fof(f220043,plain,
    ( ~ spl10_6
    | spl10_29
    | ~ spl10_2998 ),
    inference(avatar_contradiction_clause,[],[f219960])).

fof(f219960,plain,
    ( $false
    | ~ spl10_6
    | ~ spl10_29
    | ~ spl10_2998 ),
    inference(subsumption_resolution,[],[f126,f219955])).

fof(f219955,plain,
    ( ! [X3] : ~ v1_xboole_0(X3)
    | ~ spl10_29
    | ~ spl10_2998 ),
    inference(forward_demodulation,[],[f217841,f69])).

fof(f69,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t2_mcart_1.p',t1_boole)).

fof(f217841,plain,
    ( ! [X3] : ~ v1_xboole_0(k2_xboole_0(X3,k1_xboole_0))
    | ~ spl10_29
    | ~ spl10_2998 ),
    inference(superposition,[],[f643,f217786])).

fof(f217786,plain,
    ( k1_xboole_0 = k2_xboole_0(sK0,sK4(sK0))
    | ~ spl10_2998 ),
    inference(avatar_component_clause,[],[f217785])).

fof(f643,plain,
    ( ! [X0,X1] : ~ v1_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK0,X1)))
    | ~ spl10_29 ),
    inference(resolution,[],[f641,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_xboole_0(k2_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t2_mcart_1.p',fc5_xboole_0)).

fof(f641,plain,
    ( ! [X0] : ~ v1_xboole_0(k2_xboole_0(sK0,X0))
    | ~ spl10_29 ),
    inference(superposition,[],[f638,f78])).

fof(f638,plain,
    ( ! [X0] : ~ v1_xboole_0(k2_xboole_0(X0,sK0))
    | ~ spl10_29 ),
    inference(resolution,[],[f636,f82])).

fof(f636,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f635])).

fof(f635,plain,
    ( spl10_29
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f126,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl10_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f217821,plain,
    ( spl10_3010
    | spl10_2998 ),
    inference(avatar_split_clause,[],[f217752,f217785,f217819])).

fof(f217752,plain,(
    ! [X27] :
      ( k1_xboole_0 = k2_xboole_0(sK0,sK4(sK0))
      | ~ r1_xboole_0(sK1(sK2(k2_xboole_0(sK0,sK4(sK0)))),k2_xboole_0(sK0,X27)) ) ),
    inference(resolution,[],[f44111,f771])).

fof(f771,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r1_xboole_0(sK1(X0),k2_xboole_0(sK0,X1)) ) ),
    inference(resolution,[],[f96,f67])).

fof(f67,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(sK1(X1),sK0)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f217799,plain,
    ( ~ spl10_3001
    | spl10_2998 ),
    inference(avatar_split_clause,[],[f217779,f217785,f217788])).

fof(f217779,plain,
    ( k1_xboole_0 = k2_xboole_0(sK0,sK4(sK0))
    | ~ r2_hidden(sK1(sK2(k2_xboole_0(sK0,sK4(sK0)))),sK4(sK0)) ),
    inference(duplicate_literal_removal,[],[f217731])).

fof(f217731,plain,
    ( k1_xboole_0 = k2_xboole_0(sK0,sK4(sK0))
    | k1_xboole_0 = k2_xboole_0(sK0,sK4(sK0))
    | ~ r2_hidden(sK1(sK2(k2_xboole_0(sK0,sK4(sK0)))),sK4(sK0)) ),
    inference(resolution,[],[f44111,f35803])).

fof(f35803,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(k2_xboole_0(X0,X1)),sK0)
      | k1_xboole_0 = k2_xboole_0(X0,X1)
      | ~ r2_hidden(sK1(sK2(k2_xboole_0(X0,X1))),X1) ) ),
    inference(resolution,[],[f6214,f66])).

fof(f6214,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,sK2(k2_xboole_0(X3,X4)))
      | ~ r2_hidden(X5,X4)
      | k1_xboole_0 = k2_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f854,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t2_mcart_1.p',t3_xboole_0)).

fof(f637,plain,
    ( ~ spl10_29
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f621,f614,f635])).

fof(f614,plain,
    ( spl10_20
  <=> r2_hidden(sK5(sK1(sK2(sK0)),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f621,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl10_20 ),
    inference(resolution,[],[f615,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t2_mcart_1.p',t7_boole)).

fof(f615,plain,
    ( r2_hidden(sK5(sK1(sK2(sK0)),sK0),sK0)
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f614])).

fof(f616,plain,(
    spl10_20 ),
    inference(avatar_split_clause,[],[f612,f614])).

fof(f612,plain,(
    r2_hidden(sK5(sK1(sK2(sK0)),sK0),sK0) ),
    inference(global_subsumption,[],[f65,f610])).

fof(f610,plain,
    ( r2_hidden(sK5(sK1(sK2(sK0)),sK0),sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f606,f71])).

fof(f606,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(sK5(sK1(X0),sK0),sK0) ) ),
    inference(resolution,[],[f80,f67])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f65,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f43])).

fof(f127,plain,
    ( spl10_6
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f123,f120,f115,f125])).

fof(f115,plain,
    ( spl10_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f120,plain,
    ( spl10_4
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f123,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(superposition,[],[f116,f121])).

fof(f121,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f116,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f115])).

fof(f122,plain,
    ( spl10_4
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f118,f115,f120])).

fof(f118,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl10_2 ),
    inference(resolution,[],[f70,f116])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t2_mcart_1.p',t6_boole)).

fof(f117,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f68,f115])).

fof(f68,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t2_mcart_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
