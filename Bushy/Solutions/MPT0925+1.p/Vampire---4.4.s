%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t85_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:15 EDT 2019

% Result     : Theorem 2.36s
% Output     : Refutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :  100 (1230 expanded)
%              Number of leaves         :   16 ( 377 expanded)
%              Depth                    :   31
%              Number of atoms          :  466 (9507 expanded)
%              Number of equality atoms :   95 (2312 expanded)
%              Maximal formula depth    :   20 (   8 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9528,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f7745,f9521,f9527])).

fof(f9527,plain,(
    ~ spl19_286 ),
    inference(avatar_contradiction_clause,[],[f9526])).

fof(f9526,plain,
    ( $false
    | ~ spl19_286 ),
    inference(subsumption_resolution,[],[f9525,f1753])).

fof(f1753,plain,(
    r2_hidden(sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0),k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4)) ),
    inference(subsumption_resolution,[],[f1752,f90])).

fof(f90,plain,(
    k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4) != sK0 ),
    inference(definition_unfolding,[],[f61,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t85_mcart_1.p',d4_zfmisc_1)).

fof(f61,plain,(
    k4_zfmisc_1(sK1,sK2,sK3,sK4) != sK0 ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( k4_zfmisc_1(sK1,sK2,sK3,sK4) != sK0
    & ! [X5] :
        ( ( r2_hidden(X5,sK0)
          | ! [X6,X7,X8,X9] :
              ( k4_mcart_1(X6,X7,X8,X9) != X5
              | ~ r2_hidden(X9,sK4)
              | ~ r2_hidden(X8,sK3)
              | ~ r2_hidden(X7,sK2)
              | ~ r2_hidden(X6,sK1) ) )
        & ( ( k4_mcart_1(sK5(X5),sK6(X5),sK7(X5),sK8(X5)) = X5
            & r2_hidden(sK8(X5),sK4)
            & r2_hidden(sK7(X5),sK3)
            & r2_hidden(sK6(X5),sK2)
            & r2_hidden(sK5(X5),sK1) )
          | ~ r2_hidden(X5,sK0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f36,f38,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k4_zfmisc_1(X1,X2,X3,X4) != X0
        & ! [X5] :
            ( ( r2_hidden(X5,X0)
              | ! [X6,X7,X8,X9] :
                  ( k4_mcart_1(X6,X7,X8,X9) != X5
                  | ~ r2_hidden(X9,X4)
                  | ~ r2_hidden(X8,X3)
                  | ~ r2_hidden(X7,X2)
                  | ~ r2_hidden(X6,X1) ) )
            & ( ? [X10,X11,X12,X13] :
                  ( k4_mcart_1(X10,X11,X12,X13) = X5
                  & r2_hidden(X13,X4)
                  & r2_hidden(X12,X3)
                  & r2_hidden(X11,X2)
                  & r2_hidden(X10,X1) )
              | ~ r2_hidden(X5,X0) ) ) )
   => ( k4_zfmisc_1(sK1,sK2,sK3,sK4) != sK0
      & ! [X5] :
          ( ( r2_hidden(X5,sK0)
            | ! [X9,X8,X7,X6] :
                ( k4_mcart_1(X6,X7,X8,X9) != X5
                | ~ r2_hidden(X9,sK4)
                | ~ r2_hidden(X8,sK3)
                | ~ r2_hidden(X7,sK2)
                | ~ r2_hidden(X6,sK1) ) )
          & ( ? [X13,X12,X11,X10] :
                ( k4_mcart_1(X10,X11,X12,X13) = X5
                & r2_hidden(X13,sK4)
                & r2_hidden(X12,sK3)
                & r2_hidden(X11,sK2)
                & r2_hidden(X10,sK1) )
            | ~ r2_hidden(X5,sK0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X4,X2,X3,X1,X5] :
      ( ? [X10,X11,X12,X13] :
          ( k4_mcart_1(X10,X11,X12,X13) = X5
          & r2_hidden(X13,X4)
          & r2_hidden(X12,X3)
          & r2_hidden(X11,X2)
          & r2_hidden(X10,X1) )
     => ( k4_mcart_1(sK5(X5),sK6(X5),sK7(X5),sK8(X5)) = X5
        & r2_hidden(sK8(X5),X4)
        & r2_hidden(sK7(X5),X3)
        & r2_hidden(sK6(X5),X2)
        & r2_hidden(sK5(X5),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k4_zfmisc_1(X1,X2,X3,X4) != X0
      & ! [X5] :
          ( ( r2_hidden(X5,X0)
            | ! [X6,X7,X8,X9] :
                ( k4_mcart_1(X6,X7,X8,X9) != X5
                | ~ r2_hidden(X9,X4)
                | ~ r2_hidden(X8,X3)
                | ~ r2_hidden(X7,X2)
                | ~ r2_hidden(X6,X1) ) )
          & ( ? [X10,X11,X12,X13] :
                ( k4_mcart_1(X10,X11,X12,X13) = X5
                & r2_hidden(X13,X4)
                & r2_hidden(X12,X3)
                & r2_hidden(X11,X2)
                & r2_hidden(X10,X1) )
            | ~ r2_hidden(X5,X0) ) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k4_zfmisc_1(X1,X2,X3,X4) != X0
      & ! [X5] :
          ( ( r2_hidden(X5,X0)
            | ! [X6,X7,X8,X9] :
                ( k4_mcart_1(X6,X7,X8,X9) != X5
                | ~ r2_hidden(X9,X4)
                | ~ r2_hidden(X8,X3)
                | ~ r2_hidden(X7,X2)
                | ~ r2_hidden(X6,X1) ) )
          & ( ? [X6,X7,X8,X9] :
                ( k4_mcart_1(X6,X7,X8,X9) = X5
                & r2_hidden(X9,X4)
                & r2_hidden(X8,X3)
                & r2_hidden(X7,X2)
                & r2_hidden(X6,X1) )
            | ~ r2_hidden(X5,X0) ) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k4_zfmisc_1(X1,X2,X3,X4) != X0
      & ! [X5] :
          ( r2_hidden(X5,X0)
        <=> ? [X6,X7,X8,X9] :
              ( k4_mcart_1(X6,X7,X8,X9) = X5
              & r2_hidden(X9,X4)
              & r2_hidden(X8,X3)
              & r2_hidden(X7,X2)
              & r2_hidden(X6,X1) ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( ! [X5] :
            ( r2_hidden(X5,X0)
          <=> ? [X6,X7,X8,X9] :
                ( k4_mcart_1(X6,X7,X8,X9) = X5
                & r2_hidden(X9,X4)
                & r2_hidden(X8,X3)
                & r2_hidden(X7,X2)
                & r2_hidden(X6,X1) ) )
       => k4_zfmisc_1(X1,X2,X3,X4) = X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( ! [X5] :
          ( r2_hidden(X5,X0)
        <=> ? [X6,X7,X8,X9] :
              ( k4_mcart_1(X6,X7,X8,X9) = X5
              & r2_hidden(X9,X4)
              & r2_hidden(X8,X3)
              & r2_hidden(X7,X2)
              & r2_hidden(X6,X1) ) )
     => k4_zfmisc_1(X1,X2,X3,X4) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t85_mcart_1.p',t85_mcart_1)).

fof(f1752,plain,
    ( r2_hidden(sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0),k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4))
    | k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4) = sK0 ),
    inference(factoring,[],[f1748])).

fof(f1748,plain,(
    ! [X0] :
      ( r2_hidden(sK10(X0,sK0),k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4))
      | r2_hidden(sK10(X0,sK0),X0)
      | sK0 = X0 ) ),
    inference(subsumption_resolution,[],[f1747,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK10(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK10(X0,X1),X1)
          | ~ r2_hidden(sK10(X0,X1),X0) )
        & ( r2_hidden(sK10(X0,X1),X1)
          | r2_hidden(sK10(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK10(X0,X1),X1)
          | ~ r2_hidden(sK10(X0,X1),X0) )
        & ( r2_hidden(sK10(X0,X1),X1)
          | r2_hidden(sK10(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t85_mcart_1.p',t2_tarski)).

fof(f1747,plain,(
    ! [X0] :
      ( r2_hidden(sK10(X0,sK0),k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4))
      | r2_hidden(sK10(X0,sK0),X0)
      | sK0 = X0
      | ~ r2_hidden(sK10(X0,sK0),sK0) ) ),
    inference(resolution,[],[f1746,f55])).

fof(f55,plain,(
    ! [X5] :
      ( r2_hidden(sK5(X5),sK1)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1746,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(sK10(X0,sK0)),X1)
      | r2_hidden(sK10(X0,sK0),k2_zfmisc_1(k3_zfmisc_1(X1,sK2,sK3),sK4))
      | r2_hidden(sK10(X0,sK0),X0)
      | sK0 = X0 ) ),
    inference(subsumption_resolution,[],[f1745,f68])).

fof(f1745,plain,(
    ! [X0,X1] :
      ( sK0 = X0
      | r2_hidden(sK10(X0,sK0),k2_zfmisc_1(k3_zfmisc_1(X1,sK2,sK3),sK4))
      | r2_hidden(sK10(X0,sK0),X0)
      | ~ r2_hidden(sK5(sK10(X0,sK0)),X1)
      | ~ r2_hidden(sK10(X0,sK0),sK0) ) ),
    inference(resolution,[],[f1744,f56])).

fof(f56,plain,(
    ! [X5] :
      ( r2_hidden(sK6(X5),sK2)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1744,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(sK10(X0,sK0)),X2)
      | sK0 = X0
      | r2_hidden(sK10(X0,sK0),k2_zfmisc_1(k3_zfmisc_1(X1,X2,sK3),sK4))
      | r2_hidden(sK10(X0,sK0),X0)
      | ~ r2_hidden(sK5(sK10(X0,sK0)),X1) ) ),
    inference(subsumption_resolution,[],[f1743,f68])).

fof(f1743,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK10(X0,sK0),X0)
      | sK0 = X0
      | r2_hidden(sK10(X0,sK0),k2_zfmisc_1(k3_zfmisc_1(X1,X2,sK3),sK4))
      | ~ r2_hidden(sK6(sK10(X0,sK0)),X2)
      | ~ r2_hidden(sK5(sK10(X0,sK0)),X1)
      | ~ r2_hidden(sK10(X0,sK0),sK0) ) ),
    inference(resolution,[],[f1691,f57])).

fof(f57,plain,(
    ! [X5] :
      ( r2_hidden(sK7(X5),sK3)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1691,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK7(sK10(X0,sK0)),X3)
      | r2_hidden(sK10(X0,sK0),X0)
      | sK0 = X0
      | r2_hidden(sK10(X0,sK0),k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),sK4))
      | ~ r2_hidden(sK6(sK10(X0,sK0)),X2)
      | ~ r2_hidden(sK5(sK10(X0,sK0)),X1) ) ),
    inference(resolution,[],[f1690,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
      | ~ r2_hidden(X2,X5)
      | ~ r2_hidden(X1,X4)
      | ~ r2_hidden(X0,X3) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
        | ~ r2_hidden(X2,X5)
        | ~ r2_hidden(X1,X4)
        | ~ r2_hidden(X0,X3) )
      & ( ( r2_hidden(X2,X5)
          & r2_hidden(X1,X4)
          & r2_hidden(X0,X3) )
        | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
        | ~ r2_hidden(X2,X5)
        | ~ r2_hidden(X1,X4)
        | ~ r2_hidden(X0,X3) )
      & ( ( r2_hidden(X2,X5)
          & r2_hidden(X1,X4)
          & r2_hidden(X0,X3) )
        | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
    <=> ( r2_hidden(X2,X5)
        & r2_hidden(X1,X4)
        & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t85_mcart_1.p',t73_mcart_1)).

fof(f1690,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k3_mcart_1(sK5(sK10(X0,sK0)),sK6(sK10(X0,sK0)),sK7(sK10(X0,sK0))),X1)
      | r2_hidden(sK10(X0,sK0),k2_zfmisc_1(X1,sK4))
      | r2_hidden(sK10(X0,sK0),X0)
      | sK0 = X0 ) ),
    inference(subsumption_resolution,[],[f1689,f68])).

fof(f1689,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,sK0),k2_zfmisc_1(X1,sK4))
      | ~ r2_hidden(k3_mcart_1(sK5(sK10(X0,sK0)),sK6(sK10(X0,sK0)),sK7(sK10(X0,sK0))),X1)
      | r2_hidden(sK10(X0,sK0),X0)
      | sK0 = X0
      | ~ r2_hidden(sK10(X0,sK0),sK0) ) ),
    inference(resolution,[],[f289,f58])).

fof(f58,plain,(
    ! [X5] :
      ( r2_hidden(sK8(X5),sK4)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f289,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(sK8(sK10(X4,sK0)),X6)
      | r2_hidden(sK10(X4,sK0),k2_zfmisc_1(X5,X6))
      | ~ r2_hidden(k3_mcart_1(sK5(sK10(X4,sK0)),sK6(sK10(X4,sK0)),sK7(sK10(X4,sK0))),X5)
      | r2_hidden(sK10(X4,sK0),X4)
      | sK0 = X4 ) ),
    inference(superposition,[],[f95,f204])).

fof(f204,plain,(
    ! [X9] :
      ( k4_tarski(k3_mcart_1(sK5(sK10(X9,sK0)),sK6(sK10(X9,sK0)),sK7(sK10(X9,sK0))),sK8(sK10(X9,sK0))) = sK10(X9,sK0)
      | r2_hidden(sK10(X9,sK0),X9)
      | sK0 = X9 ) ),
    inference(resolution,[],[f68,f92])).

fof(f92,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK0)
      | k4_tarski(k3_mcart_1(sK5(X5),sK6(X5),sK7(X5)),sK8(X5)) = X5 ) ),
    inference(definition_unfolding,[],[f59,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t85_mcart_1.p',d4_mcart_1)).

fof(f59,plain,(
    ! [X5] :
      ( k4_mcart_1(sK5(X5),sK6(X5),sK7(X5),sK8(X5)) = X5
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f95,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK11(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK11(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK12(X0,X1,X2),sK13(X0,X1,X2)) = sK11(X0,X1,X2)
              & r2_hidden(sK13(X0,X1,X2),X1)
              & r2_hidden(sK12(X0,X1,X2),X0) )
            | r2_hidden(sK11(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK14(X0,X1,X8),sK15(X0,X1,X8)) = X8
                & r2_hidden(sK15(X0,X1,X8),X1)
                & r2_hidden(sK14(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13,sK14,sK15])],[f46,f49,f48,f47])).

fof(f47,plain,(
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
              ( k4_tarski(X4,X5) != sK11(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK11(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK11(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK11(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK12(X0,X1,X2),sK13(X0,X1,X2)) = X3
        & r2_hidden(sK13(X0,X1,X2),X1)
        & r2_hidden(sK12(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK14(X0,X1,X8),sK15(X0,X1,X8)) = X8
        & r2_hidden(sK15(X0,X1,X8),X1)
        & r2_hidden(sK14(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t85_mcart_1.p',d2_zfmisc_1)).

fof(f9525,plain,
    ( ~ r2_hidden(sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0),k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4))
    | ~ spl19_286 ),
    inference(subsumption_resolution,[],[f9522,f90])).

fof(f9522,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4) = sK0
    | ~ r2_hidden(sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0),k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4))
    | ~ spl19_286 ),
    inference(resolution,[],[f7744,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK10(X0,X1),X1)
      | X0 = X1
      | ~ r2_hidden(sK10(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f7744,plain,
    ( r2_hidden(sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0),sK0)
    | ~ spl19_286 ),
    inference(avatar_component_clause,[],[f7743])).

fof(f7743,plain,
    ( spl19_286
  <=> r2_hidden(sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_286])])).

fof(f9521,plain,(
    ~ spl19_284 ),
    inference(avatar_contradiction_clause,[],[f9520])).

fof(f9520,plain,
    ( $false
    | ~ spl19_284 ),
    inference(subsumption_resolution,[],[f9519,f1754])).

fof(f1754,plain,(
    r2_hidden(sK14(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0)),k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(resolution,[],[f1753,f98])).

fof(f98,plain,(
    ! [X0,X8,X1] :
      ( ~ r2_hidden(X8,k2_zfmisc_1(X0,X1))
      | r2_hidden(sK14(X0,X1,X8),X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK14(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f9519,plain,
    ( ~ r2_hidden(sK14(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0)),k3_zfmisc_1(sK1,sK2,sK3))
    | ~ spl19_284 ),
    inference(subsumption_resolution,[],[f9515,f1753])).

fof(f9515,plain,
    ( ~ r2_hidden(sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0),k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4))
    | ~ r2_hidden(sK14(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0)),k3_zfmisc_1(sK1,sK2,sK3))
    | ~ spl19_284 ),
    inference(resolution,[],[f7738,f1755])).

fof(f1755,plain,(
    r2_hidden(sK15(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0)),sK4) ),
    inference(resolution,[],[f1753,f97])).

fof(f97,plain,(
    ! [X0,X8,X1] :
      ( ~ r2_hidden(X8,k2_zfmisc_1(X0,X1))
      | r2_hidden(sK15(X0,X1,X8),X1) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK15(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f7738,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK15(X0,X1,sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0)),sK4)
        | ~ r2_hidden(sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0),k2_zfmisc_1(X0,X1))
        | ~ r2_hidden(sK14(X0,X1,sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0)),k3_zfmisc_1(sK1,sK2,sK3)) )
    | ~ spl19_284 ),
    inference(avatar_component_clause,[],[f7737])).

fof(f7737,plain,
    ( spl19_284
  <=> ! [X1,X0] :
        ( ~ r2_hidden(sK14(X0,X1,sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0)),k3_zfmisc_1(sK1,sK2,sK3))
        | ~ r2_hidden(sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0),k2_zfmisc_1(X0,X1))
        | ~ r2_hidden(sK15(X0,X1,sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0)),sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_284])])).

fof(f7745,plain,
    ( spl19_284
    | spl19_286 ),
    inference(avatar_split_clause,[],[f7735,f7743,f7737])).

fof(f7735,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0),sK0)
      | ~ r2_hidden(sK14(X0,X1,sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0)),k3_zfmisc_1(sK1,sK2,sK3))
      | ~ r2_hidden(sK15(X0,X1,sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0)),sK4)
      | ~ r2_hidden(sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0),k2_zfmisc_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f7734,f1753])).

fof(f7734,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0),sK0)
      | ~ r2_hidden(sK14(X0,X1,sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0)),k3_zfmisc_1(sK1,sK2,sK3))
      | ~ r2_hidden(sK15(X0,X1,sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0)),sK4)
      | ~ r2_hidden(sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0),k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4)) ) ),
    inference(superposition,[],[f3712,f96])).

fof(f96,plain,(
    ! [X0,X8,X1] :
      ( k4_tarski(sK14(X0,X1,X8),sK15(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X8,X1] :
      ( k4_tarski(sK14(X0,X1,X8),sK15(X0,X1,X8)) = X8
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f3712,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK14(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0)),sK15(X3,sK4,X2)),sK0)
      | ~ r2_hidden(sK14(X0,X1,X2),X3)
      | ~ r2_hidden(sK15(X0,X1,X2),sK4)
      | ~ r2_hidden(X2,k2_zfmisc_1(X0,X1)) ) ),
    inference(superposition,[],[f3568,f96])).

fof(f3568,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(k4_tarski(sK14(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0)),sK15(X8,sK4,k4_tarski(X7,X6))),sK0)
      | ~ r2_hidden(X7,X8)
      | ~ r2_hidden(X6,sK4) ) ),
    inference(subsumption_resolution,[],[f3567,f1754])).

fof(f3567,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X6,sK4)
      | ~ r2_hidden(X7,X8)
      | r2_hidden(k4_tarski(sK14(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0)),sK15(X8,sK4,k4_tarski(X7,X6))),sK0)
      | ~ r2_hidden(sK14(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0)),k3_zfmisc_1(sK1,sK2,sK3)) ) ),
    inference(subsumption_resolution,[],[f3566,f1762])).

fof(f1762,plain,(
    r2_hidden(sK17(sK14(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0)),sK1,sK2,sK3),sK2) ),
    inference(resolution,[],[f1754,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3))
      | r2_hidden(sK17(X0,X1,X2,X3),X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k3_mcart_1(sK16(X0,X1,X2,X3),sK17(X0,X1,X2,X3),sK18(X0,X1,X2,X3)) = X0
        & r2_hidden(sK18(X0,X1,X2,X3),X3)
        & r2_hidden(sK17(X0,X1,X2,X3),X2)
        & r2_hidden(sK16(X0,X1,X2,X3),X1) )
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16,sK17,sK18])],[f34,f51])).

fof(f51,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4,X5,X6] :
          ( k3_mcart_1(X4,X5,X6) = X0
          & r2_hidden(X6,X3)
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
     => ( k3_mcart_1(sK16(X0,X1,X2,X3),sK17(X0,X1,X2,X3),sK18(X0,X1,X2,X3)) = X0
        & r2_hidden(sK18(X0,X1,X2,X3),X3)
        & r2_hidden(sK17(X0,X1,X2,X3),X2)
        & r2_hidden(sK16(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5,X6] :
          ( k3_mcart_1(X4,X5,X6) = X0
          & r2_hidden(X6,X3)
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5,X6] :
            ~ ( k3_mcart_1(X4,X5,X6) = X0
              & r2_hidden(X6,X3)
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t85_mcart_1.p',t72_mcart_1)).

fof(f3566,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X6,sK4)
      | ~ r2_hidden(X7,X8)
      | ~ r2_hidden(sK17(sK14(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0)),sK1,sK2,sK3),sK2)
      | r2_hidden(k4_tarski(sK14(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0)),sK15(X8,sK4,k4_tarski(X7,X6))),sK0)
      | ~ r2_hidden(sK14(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0)),k3_zfmisc_1(sK1,sK2,sK3)) ) ),
    inference(subsumption_resolution,[],[f3546,f1761])).

fof(f1761,plain,(
    r2_hidden(sK18(sK14(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0)),sK1,sK2,sK3),sK3) ),
    inference(resolution,[],[f1754,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3))
      | r2_hidden(sK18(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f3546,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X6,sK4)
      | ~ r2_hidden(X7,X8)
      | ~ r2_hidden(sK18(sK14(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0)),sK1,sK2,sK3),sK3)
      | ~ r2_hidden(sK17(sK14(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0)),sK1,sK2,sK3),sK2)
      | r2_hidden(k4_tarski(sK14(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0)),sK15(X8,sK4,k4_tarski(X7,X6))),sK0)
      | ~ r2_hidden(sK14(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0)),k3_zfmisc_1(sK1,sK2,sK3)) ) ),
    inference(resolution,[],[f1342,f1763])).

fof(f1763,plain,(
    r2_hidden(sK16(sK14(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK10(k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4),sK0)),sK1,sK2,sK3),sK1) ),
    inference(resolution,[],[f1754,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3))
      | r2_hidden(sK16(X0,X1,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f1342,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(sK16(X0,X1,X2,X3),sK1)
      | ~ r2_hidden(X6,sK4)
      | ~ r2_hidden(X5,X4)
      | ~ r2_hidden(sK18(X0,X1,X2,X3),sK3)
      | ~ r2_hidden(sK17(X0,X1,X2,X3),sK2)
      | r2_hidden(k4_tarski(X0,sK15(X4,sK4,k4_tarski(X5,X6))),sK0)
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(superposition,[],[f347,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(sK16(X0,X1,X2,X3),sK17(X0,X1,X2,X3),sK18(X0,X1,X2,X3)) = X0
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f347,plain,(
    ! [X39,X43,X41,X38,X42,X40] :
      ( r2_hidden(k4_tarski(k3_mcart_1(X41,X42,X43),sK15(X39,sK4,k4_tarski(X38,X40))),sK0)
      | ~ r2_hidden(X40,sK4)
      | ~ r2_hidden(X38,X39)
      | ~ r2_hidden(X43,sK3)
      | ~ r2_hidden(X42,sK2)
      | ~ r2_hidden(X41,sK1) ) ),
    inference(resolution,[],[f285,f93])).

fof(f93,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r2_hidden(X9,sK4)
      | r2_hidden(k4_tarski(k3_mcart_1(X6,X7,X8),X9),sK0)
      | ~ r2_hidden(X8,sK3)
      | ~ r2_hidden(X7,sK2)
      | ~ r2_hidden(X6,sK1) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( r2_hidden(X5,sK0)
      | k4_tarski(k3_mcart_1(X6,X7,X8),X9) != X5
      | ~ r2_hidden(X9,sK4)
      | ~ r2_hidden(X8,sK3)
      | ~ r2_hidden(X7,sK2)
      | ~ r2_hidden(X6,sK1) ) ),
    inference(definition_unfolding,[],[f60,f81])).

fof(f60,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( r2_hidden(X5,sK0)
      | k4_mcart_1(X6,X7,X8,X9) != X5
      | ~ r2_hidden(X9,sK4)
      | ~ r2_hidden(X8,sK3)
      | ~ r2_hidden(X7,sK2)
      | ~ r2_hidden(X6,sK1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f285,plain,(
    ! [X6,X4,X7,X5] :
      ( r2_hidden(sK15(X7,X5,k4_tarski(X6,X4)),X5)
      | ~ r2_hidden(X6,X7)
      | ~ r2_hidden(X4,X5) ) ),
    inference(resolution,[],[f95,f97])).
%------------------------------------------------------------------------------
