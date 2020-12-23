%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : setfam_1__t25_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:17 EDT 2019

% Result     : Theorem 44.00s
% Output     : Refutation 44.00s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 118 expanded)
%              Number of leaves         :   10 (  39 expanded)
%              Depth                    :   21
%              Number of atoms          :  226 ( 533 expanded)
%              Number of equality atoms :   54 (  85 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1288,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1287,f62])).

fof(f62,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ~ r1_tarski(sK3,sK1)
    & ~ r1_tarski(sK3,sK0)
    & r2_hidden(sK3,sK2)
    & r1_setfam_1(sK2,k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f45,f44])).

fof(f44,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(X3,X1)
            & ~ r1_tarski(X3,X0)
            & r2_hidden(X3,X2) )
        & r1_setfam_1(X2,k2_tarski(X0,X1)) )
   => ( ? [X3] :
          ( ~ r1_tarski(X3,sK1)
          & ~ r1_tarski(X3,sK0)
          & r2_hidden(X3,sK2) )
      & r1_setfam_1(sK2,k2_tarski(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X1)
          & ~ r1_tarski(X3,X0)
          & r2_hidden(X3,X2) )
     => ( ~ r1_tarski(sK3,X1)
        & ~ r1_tarski(sK3,X0)
        & r2_hidden(sK3,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X1)
          & ~ r1_tarski(X3,X0)
          & r2_hidden(X3,X2) )
      & r1_setfam_1(X2,k2_tarski(X0,X1)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_setfam_1(X2,k2_tarski(X0,X1))
       => ! [X3] :
            ~ ( ~ r1_tarski(X3,X1)
              & ~ r1_tarski(X3,X0)
              & r2_hidden(X3,X2) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( r1_setfam_1(X2,k2_tarski(X0,X1))
     => ! [X3] :
          ~ ( ~ r1_tarski(X3,X1)
            & ~ r1_tarski(X3,X0)
            & r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t25_setfam_1.p',t25_setfam_1)).

fof(f1287,plain,(
    ~ r2_hidden(sK3,sK2) ),
    inference(resolution,[],[f1258,f61])).

fof(f61,plain,(
    r1_setfam_1(sK2,k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f1258,plain,(
    ! [X19] :
      ( ~ r1_setfam_1(X19,k2_tarski(sK0,sK1))
      | ~ r2_hidden(sK3,X19) ) ),
    inference(subsumption_resolution,[],[f1237,f63])).

fof(f63,plain,(
    ~ r1_tarski(sK3,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f1237,plain,(
    ! [X19] :
      ( r1_tarski(sK3,sK0)
      | ~ r2_hidden(sK3,X19)
      | ~ r1_setfam_1(X19,k2_tarski(sK0,sK1)) ) ),
    inference(superposition,[],[f68,f1202])).

fof(f1202,plain,(
    sK0 = sK4(k2_tarski(sK0,sK1),sK3) ),
    inference(subsumption_resolution,[],[f1201,f62])).

fof(f1201,plain,
    ( ~ r2_hidden(sK3,sK2)
    | sK0 = sK4(k2_tarski(sK0,sK1),sK3) ),
    inference(resolution,[],[f1132,f61])).

fof(f1132,plain,(
    ! [X19] :
      ( ~ r1_setfam_1(X19,k2_tarski(sK0,sK1))
      | ~ r2_hidden(sK3,X19)
      | sK0 = sK4(k2_tarski(sK0,sK1),sK3) ) ),
    inference(subsumption_resolution,[],[f1114,f64])).

fof(f64,plain,(
    ~ r1_tarski(sK3,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f1114,plain,(
    ! [X19] :
      ( r1_tarski(sK3,sK1)
      | ~ r2_hidden(sK3,X19)
      | ~ r1_setfam_1(X19,k2_tarski(sK0,sK1))
      | sK0 = sK4(k2_tarski(sK0,sK1),sK3) ) ),
    inference(superposition,[],[f68,f1092])).

fof(f1092,plain,
    ( sK1 = sK4(k2_tarski(sK0,sK1),sK3)
    | sK0 = sK4(k2_tarski(sK0,sK1),sK3) ),
    inference(resolution,[],[f384,f61])).

fof(f384,plain,(
    ! [X12,X13] :
      ( ~ r1_setfam_1(sK2,k2_tarski(X12,X13))
      | sK4(k2_tarski(X12,X13),sK3) = X13
      | sK4(k2_tarski(X12,X13),sK3) = X12 ) ),
    inference(forward_demodulation,[],[f383,f86])).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t25_setfam_1.p',t41_enumset1)).

fof(f383,plain,(
    ! [X12,X13] :
      ( sK4(k2_tarski(X12,X13),sK3) = X13
      | ~ r1_setfam_1(sK2,k2_tarski(X12,X13))
      | sK4(k2_xboole_0(k1_tarski(X12),k1_tarski(X13)),sK3) = X12 ) ),
    inference(forward_demodulation,[],[f382,f86])).

fof(f382,plain,(
    ! [X12,X13] :
      ( ~ r1_setfam_1(sK2,k2_tarski(X12,X13))
      | sK4(k2_xboole_0(k1_tarski(X12),k1_tarski(X13)),sK3) = X13
      | sK4(k2_xboole_0(k1_tarski(X12),k1_tarski(X13)),sK3) = X12 ) ),
    inference(forward_demodulation,[],[f375,f86])).

fof(f375,plain,(
    ! [X12,X13] :
      ( ~ r1_setfam_1(sK2,k2_xboole_0(k1_tarski(X12),k1_tarski(X13)))
      | sK4(k2_xboole_0(k1_tarski(X12),k1_tarski(X13)),sK3) = X13
      | sK4(k2_xboole_0(k1_tarski(X12),k1_tarski(X13)),sK3) = X12 ) ),
    inference(resolution,[],[f130,f99])).

fof(f99,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f56,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t25_setfam_1.p',d1_tarski)).

fof(f130,plain,(
    ! [X12,X13] :
      ( r2_hidden(sK4(k2_xboole_0(X12,k1_tarski(X13)),sK3),X12)
      | ~ r1_setfam_1(sK2,k2_xboole_0(X12,k1_tarski(X13)))
      | sK4(k2_xboole_0(X12,k1_tarski(X13)),sK3) = X13 ) ),
    inference(resolution,[],[f109,f99])).

fof(f109,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK4(k2_xboole_0(X5,X6),sK3),X6)
      | r2_hidden(sK4(k2_xboole_0(X5,X6),sK3),X5)
      | ~ r1_setfam_1(sK2,k2_xboole_0(X5,X6)) ) ),
    inference(resolution,[],[f103,f96])).

fof(f96,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & ~ r2_hidden(sK5(X0,X1,X2),X0) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( r2_hidden(sK5(X0,X1,X2),X1)
            | r2_hidden(sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f52,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & ~ r2_hidden(sK5(X0,X1,X2),X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( r2_hidden(sK5(X0,X1,X2),X1)
          | r2_hidden(sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t25_setfam_1.p',d3_xboole_0)).

fof(f103,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0,sK3),X0)
      | ~ r1_setfam_1(sK2,X0) ) ),
    inference(resolution,[],[f62,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(sK4(X1,X2),X1)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X2,sK4(X1,X2))
            & r2_hidden(sK4(X1,X2),X1) )
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f48])).

fof(f48,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( r1_tarski(X2,X3)
          & r2_hidden(X3,X1) )
     => ( r1_tarski(X2,sK4(X1,X2))
        & r2_hidden(sK4(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t25_setfam_1.p',d2_setfam_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,sK4(X1,X2))
      | ~ r2_hidden(X2,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
