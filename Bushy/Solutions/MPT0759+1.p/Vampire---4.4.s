%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : ordinal1__t52_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:28 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 189 expanded)
%              Number of leaves         :    9 (  48 expanded)
%              Depth                    :   17
%              Number of atoms          :  198 ( 904 expanded)
%              Number of equality atoms :   66 ( 270 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1834,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1833,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t52_ordinal1.p',antisymmetry_r2_hidden)).

fof(f1833,plain,(
    r2_hidden(sK0,sK0) ),
    inference(forward_demodulation,[],[f1832,f1757])).

fof(f1757,plain,(
    sK0 = sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0) ),
    inference(subsumption_resolution,[],[f1756,f90])).

fof(f90,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox/benchmark/ordinal1__t52_ordinal1.p',d1_tarski)).

fof(f1756,plain,
    ( sK0 = sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0)
    | r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0),k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f1755,f179])).

fof(f179,plain,(
    r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0),k1_ordinal1(sK0)) ),
    inference(subsumption_resolution,[],[f178,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t52_ordinal1.p',t13_ordinal1)).

fof(f178,plain,
    ( r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0),k1_ordinal1(sK0))
    | r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0),sK0) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X0] :
      ( sK0 != X0
      | r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),X0),k1_ordinal1(sK0))
      | r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),X0),X0) ) ),
    inference(superposition,[],[f86,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f54,f55])).

fof(f55,plain,(
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

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t52_ordinal1.p',d5_xboole_0)).

fof(f86,plain,(
    k4_xboole_0(k1_ordinal1(sK0),k1_tarski(sK0)) != sK0 ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f60,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t52_ordinal1.p',redefinition_k6_subset_1)).

fof(f59,plain,(
    k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0)) != sK0 ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0)) != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f44])).

fof(f44,plain,
    ( ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0
   => k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0)) != sK0 ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/ordinal1__t52_ordinal1.p',t52_ordinal1)).

fof(f1755,plain,
    ( sK0 = sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0)
    | r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0),k1_tarski(sK0))
    | ~ r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0),k1_ordinal1(sK0)) ),
    inference(subsumption_resolution,[],[f1743,f86])).

fof(f1743,plain,
    ( sK0 = sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0)
    | k4_xboole_0(k1_ordinal1(sK0),k1_tarski(sK0)) = sK0
    | r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0),k1_tarski(sK0))
    | ~ r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0),k1_ordinal1(sK0)) ),
    inference(resolution,[],[f181,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f181,plain,
    ( r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0),sK0)
    | sK0 = sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0) ),
    inference(resolution,[],[f179,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1832,plain,(
    r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0),sK0) ),
    inference(subsumption_resolution,[],[f1767,f89])).

fof(f89,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1767,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0),sK0) ),
    inference(backward_demodulation,[],[f1757,f246])).

fof(f246,plain,
    ( ~ r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0),k1_tarski(sK0))
    | r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),sK0),sK0) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X1] :
      ( sK0 != X1
      | ~ r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),X1),k1_tarski(sK0))
      | r2_hidden(sK2(k1_ordinal1(sK0),k1_tarski(sK0),X1),X1) ) ),
    inference(superposition,[],[f86,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f56])).
%------------------------------------------------------------------------------
