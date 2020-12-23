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
% DateTime   : Thu Dec  3 12:56:04 EST 2020

% Result     : Theorem 34.88s
% Output     : Refutation 34.88s
% Verified   : 
% Statistics : Number of formulae       :  170 (2722 expanded)
%              Number of leaves         :   20 ( 558 expanded)
%              Depth                    :   32
%              Number of atoms          :  765 (18572 expanded)
%              Number of equality atoms :  113 (1628 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f36426,plain,(
    $false ),
    inference(subsumption_resolution,[],[f34962,f1352])).

fof(f1352,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f1351,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f1351,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(subsumption_resolution,[],[f1343,f116])).

fof(f116,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1343,plain,(
    ! [X7] :
      ( r1_tarski(k1_xboole_0,X7)
      | ~ r1_tarski(k3_relat_1(sK2),k3_relat_1(sK2)) ) ),
    inference(resolution,[],[f1200,f108])).

fof(f1200,plain,(
    ! [X4] :
      ( r1_tarski(k1_xboole_0,X4)
      | r2_hidden(k3_relat_1(sK2),k3_relat_1(sK2)) ) ),
    inference(superposition,[],[f423,f1188])).

fof(f1188,plain,(
    k1_xboole_0 = k1_wellord1(sK2,k3_relat_1(sK2)) ),
    inference(resolution,[],[f1161,f116])).

fof(f1161,plain,(
    ! [X6] :
      ( ~ r1_tarski(k3_relat_1(sK2),X6)
      | k1_xboole_0 = k1_wellord1(sK2,X6) ) ),
    inference(resolution,[],[f1157,f108])).

fof(f1157,plain,(
    ! [X2] :
      ( r2_hidden(X2,k3_relat_1(sK2))
      | k1_xboole_0 = k1_wellord1(sK2,X2) ) ),
    inference(subsumption_resolution,[],[f1156,f369])).

fof(f369,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X7,k1_wellord1(sK2,X6))
      | r2_hidden(X6,k3_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f362,f65])).

fof(f65,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
      | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) )
    & ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
      | r2_hidden(k4_tarski(sK0,sK1),sK2) )
    & r2_hidden(sK1,k3_relat_1(sK2))
    & r2_hidden(sK0,k3_relat_1(sK2))
    & v2_wellord1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) )
        & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | r2_hidden(k4_tarski(X0,X1),X2) )
        & r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
        | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) )
      & ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
        | r2_hidden(k4_tarski(sK0,sK1),sK2) )
      & r2_hidden(sK1,k3_relat_1(sK2))
      & r2_hidden(sK0,k3_relat_1(sK2))
      & v2_wellord1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => ( r2_hidden(k4_tarski(X0,X1),X2)
          <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).

fof(f362,plain,(
    ! [X6,X7] :
      ( r2_hidden(X6,k3_relat_1(sK2))
      | ~ r2_hidden(X7,k1_wellord1(sK2,X6))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f143,f112])).

fof(f112,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK11(X0,X1,X2),X1),X0)
                | sK11(X0,X1,X2) = X1
                | ~ r2_hidden(sK11(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK11(X0,X1,X2),X1),X0)
                  & sK11(X0,X1,X2) != X1 )
                | r2_hidden(sK11(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f52,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK11(X0,X1,X2),X1),X0)
          | sK11(X0,X1,X2) = X1
          | ~ r2_hidden(sK11(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK11(X0,X1,X2),X1),X0)
            & sK11(X0,X1,X2) != X1 )
          | r2_hidden(sK11(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(f143,plain,(
    ! [X24,X25] :
      ( ~ r2_hidden(k4_tarski(X25,X24),sK2)
      | r2_hidden(X24,k3_relat_1(sK2)) ) ),
    inference(resolution,[],[f65,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(f1156,plain,(
    ! [X2] :
      ( k1_xboole_0 = k1_wellord1(sK2,X2)
      | r2_hidden(sK3(sK2,k1_wellord1(sK2,X2)),k1_wellord1(sK2,X2))
      | r2_hidden(X2,k3_relat_1(sK2)) ) ),
    inference(resolution,[],[f147,f423])).

fof(f147,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k3_relat_1(sK2))
      | k1_xboole_0 = X0
      | r2_hidden(sK3(sK2,X0),X0) ) ),
    inference(subsumption_resolution,[],[f117,f66])).

fof(f66,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f117,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK2,X0),X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_relat_1(sK2))
      | ~ v2_wellord1(sK2) ) ),
    inference(resolution,[],[f65,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X3] :
                ( r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(sK3(X0,X1),X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK3(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(k4_tarski(X2,X3),X0)
                  | ~ r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(k4_tarski(X2,X3),X0)
                  | ~ r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( ! [X2] :
                  ~ ( ! [X3] :
                        ( r2_hidden(X3,X1)
                       => r2_hidden(k4_tarski(X2,X3),X0) )
                    & r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord1)).

fof(f423,plain,(
    ! [X39,X40] :
      ( r1_tarski(k1_wellord1(sK2,X39),X40)
      | r2_hidden(X39,k3_relat_1(sK2)) ) ),
    inference(resolution,[],[f369,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK13(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK13(X0,X1),X1)
          & r2_hidden(sK13(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f62,f63])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK13(X0,X1),X1)
        & r2_hidden(sK13(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f34962,plain,(
    r2_hidden(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f27668,f34725])).

fof(f34725,plain,(
    k1_xboole_0 = sK12(sK2,sK0) ),
    inference(resolution,[],[f34704,f27668])).

fof(f34704,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK12(sK2,X0))
      | k1_xboole_0 = sK12(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f34703,f5273])).

fof(f5273,plain,(
    ! [X0] : r1_tarski(sK12(sK2,X0),k3_relat_1(sK2)) ),
    inference(duplicate_literal_removal,[],[f5260])).

fof(f5260,plain,(
    ! [X0] :
      ( r1_tarski(sK12(sK2,X0),k3_relat_1(sK2))
      | r1_tarski(sK12(sK2,X0),k3_relat_1(sK2)) ) ),
    inference(resolution,[],[f330,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK13(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f330,plain,(
    ! [X39,X40] :
      ( r2_hidden(sK13(sK12(sK2,X39),X40),k3_relat_1(sK2))
      | r1_tarski(sK12(sK2,X39),X40) ) ),
    inference(resolution,[],[f139,f106])).

fof(f139,plain,(
    ! [X17,X16] :
      ( ~ r2_hidden(X16,sK12(sK2,X17))
      | r2_hidden(X16,k3_relat_1(sK2)) ) ),
    inference(resolution,[],[f65,f99])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_relat_1(X0))
      | ~ r2_hidden(X3,sK12(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( ( r2_hidden(X3,sK12(X0,X1))
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,sK12(X0,X1)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f56,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
     => ! [X3] :
          ( ( r2_hidden(X3,sK12(X0,X1))
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,sK12(X0,X1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            & r2_hidden(X3,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => ? [X2] :
        ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s1_xboole_0__e7_18__wellord1)).

fof(f34703,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK12(sK2,X0)
      | ~ r2_hidden(X0,sK12(sK2,X0))
      | ~ r1_tarski(sK12(sK2,X0),k3_relat_1(sK2)) ) ),
    inference(duplicate_literal_removal,[],[f34689])).

fof(f34689,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK12(sK2,X0)
      | ~ r2_hidden(X0,sK12(sK2,X0))
      | k1_xboole_0 = sK12(sK2,X0)
      | ~ r1_tarski(sK12(sK2,X0),k3_relat_1(sK2)) ) ),
    inference(resolution,[],[f23687,f148])).

fof(f148,plain,(
    ! [X2,X1] :
      ( r2_hidden(k4_tarski(sK3(sK2,X1),X2),sK2)
      | ~ r2_hidden(X2,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f118,f66])).

fof(f118,plain,(
    ! [X2,X1] :
      ( r2_hidden(k4_tarski(sK3(sK2,X1),X2),sK2)
      | ~ r2_hidden(X2,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(sK2))
      | ~ v2_wellord1(sK2) ) ),
    inference(resolution,[],[f65,f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
      | ~ r2_hidden(X3,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f23687,plain,(
    ! [X8] :
      ( ~ r2_hidden(k4_tarski(sK3(sK2,sK12(sK2,X8)),X8),sK2)
      | k1_xboole_0 = sK12(sK2,X8) ) ),
    inference(subsumption_resolution,[],[f23668,f65])).

fof(f23668,plain,(
    ! [X8] :
      ( k1_xboole_0 = sK12(sK2,X8)
      | ~ r2_hidden(k4_tarski(sK3(sK2,sK12(sK2,X8)),X8),sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f5280,f100])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,sK12(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f5280,plain,(
    ! [X2] :
      ( r2_hidden(sK3(sK2,sK12(sK2,X2)),sK12(sK2,X2))
      | k1_xboole_0 = sK12(sK2,X2) ) ),
    inference(resolution,[],[f5273,f147])).

fof(f27668,plain,(
    r2_hidden(sK0,sK12(sK2,sK0)) ),
    inference(resolution,[],[f26178,f169])).

fof(f169,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK0,X0),sK2)
      | r2_hidden(sK0,sK12(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f163,f65])).

fof(f163,plain,(
    ! [X0] :
      ( r2_hidden(sK0,sK12(sK2,X0))
      | r2_hidden(k4_tarski(sK0,X0),sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f67,f101])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,sK12(X0,X1))
      | r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f67,plain,(
    r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f26178,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK0),sK2) ),
    inference(forward_demodulation,[],[f26177,f23803])).

fof(f23803,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f23802,f811])).

fof(f811,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f810,f65])).

fof(f810,plain,
    ( sK0 = sK1
    | r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f809,f151])).

fof(f151,plain,(
    v6_relat_2(sK2) ),
    inference(subsumption_resolution,[],[f135,f66])).

fof(f135,plain,
    ( v6_relat_2(sK2)
    | ~ v2_wellord1(sK2) ),
    inference(resolution,[],[f65,f90])).

fof(f90,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(f809,plain,
    ( sK0 = sK1
    | r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ v6_relat_2(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f808,f68])).

fof(f68,plain,(
    r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f808,plain,
    ( sK0 = sK1
    | r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK1,k3_relat_1(sK2))
    | ~ v6_relat_2(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f805,f67])).

fof(f805,plain,
    ( sK0 = sK1
    | r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ r2_hidden(sK1,k3_relat_1(sK2))
    | ~ v6_relat_2(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f801])).

fof(f801,plain,
    ( sK0 = sK1
    | r2_hidden(k4_tarski(sK0,sK1),sK2)
    | sK0 = sK1
    | ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ r2_hidden(sK1,k3_relat_1(sK2))
    | ~ v6_relat_2(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f790,f77])).

fof(f77,plain,(
    ! [X4,X0,X3] :
      ( r2_hidden(k4_tarski(X4,X3),X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0)
            & ~ r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
            & sK6(X0) != sK7(X0)
            & r2_hidden(sK7(X0),k3_relat_1(X0))
            & r2_hidden(sK6(X0),k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f41,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(k4_tarski(X2,X1),X0)
          & ~ r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0))
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
        & sK6(X0) != sK7(X0)
        & r2_hidden(sK7(X0),k3_relat_1(X0))
        & r2_hidden(sK6(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( r2_hidden(k4_tarski(X2,X1),X0)
              | r2_hidden(k4_tarski(X1,X2),X0)
              | X1 = X2
              | ~ r2_hidden(X2,k3_relat_1(X0))
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).

fof(f790,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK0),sK2)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f789,f144])).

fof(f144,plain,(
    ! [X26,X27] :
      ( ~ r2_hidden(k4_tarski(X26,X27),sK2)
      | r2_hidden(X26,k1_wellord1(sK2,X27))
      | X26 = X27 ) ),
    inference(resolution,[],[f65,f111])).

fof(f111,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_wellord1(X0,X1))
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f789,plain,
    ( ~ r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | sK0 = sK1
    | ~ r2_hidden(k4_tarski(sK1,sK0),sK2) ),
    inference(subsumption_resolution,[],[f788,f65])).

fof(f788,plain,
    ( ~ r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | sK0 = sK1
    | ~ r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f777,f150])).

fof(f150,plain,(
    v4_relat_2(sK2) ),
    inference(subsumption_resolution,[],[f134,f66])).

fof(f134,plain,
    ( v4_relat_2(sK2)
    | ~ v2_wellord1(sK2) ),
    inference(resolution,[],[f65,f89])).

fof(f89,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f777,plain,
    ( ~ r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | sK0 = sK1
    | ~ r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ v4_relat_2(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f515,f73])).

fof(f73,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ( sK4(X0) != sK5(X0)
            & r2_hidden(k4_tarski(sK5(X0),sK4(X0)),X0)
            & r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | ~ r2_hidden(k4_tarski(X4,X3),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f37,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & r2_hidden(k4_tarski(X2,X1),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( sK4(X0) != sK5(X0)
        & r2_hidden(k4_tarski(sK5(X0),sK4(X0)),X0)
        & r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | ~ r2_hidden(k4_tarski(X4,X3),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | ~ r2_hidden(k4_tarski(X2,X1),X0)
              | ~ r2_hidden(k4_tarski(X1,X2),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( ( r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_wellord1)).

fof(f515,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK1,k1_wellord1(sK2,sK0)) ),
    inference(resolution,[],[f69,f186])).

fof(f186,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,k1_wellord1(sK2,X1))
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f146,f105])).

fof(f105,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f146,plain,(
    ! [X30] : ~ r2_hidden(X30,k1_wellord1(sK2,X30)) ),
    inference(resolution,[],[f65,f114])).

fof(f114,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f69,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f23802,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f23774,f509])).

fof(f509,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(k4_tarski(X7,X6),sK2)
      | X6 = X7
      | ~ r2_hidden(X6,k1_wellord1(sK2,X7)) ) ),
    inference(subsumption_resolution,[],[f508,f65])).

fof(f508,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,k1_wellord1(sK2,X7))
      | X6 = X7
      | ~ r2_hidden(k4_tarski(X7,X6),sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f493,f150])).

fof(f493,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,k1_wellord1(sK2,X7))
      | X6 = X7
      | ~ r2_hidden(k4_tarski(X7,X6),sK2)
      | ~ v4_relat_2(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f145,f73])).

fof(f145,plain,(
    ! [X28,X29] :
      ( r2_hidden(k4_tarski(X28,X29),sK2)
      | ~ r2_hidden(X28,k1_wellord1(sK2,X29)) ) ),
    inference(resolution,[],[f65,f112])).

fof(f23774,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | sK0 = sK1 ),
    inference(superposition,[],[f912,f23743])).

fof(f23743,plain,
    ( sK1 = sK13(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | sK0 = sK1 ),
    inference(resolution,[],[f8200,f811])).

fof(f8200,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | sK1 = sK13(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f8178,f912])).

fof(f8178,plain,
    ( ~ r2_hidden(sK13(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))
    | sK1 = sK13(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(resolution,[],[f3775,f913])).

fof(f913,plain,
    ( ~ r2_hidden(sK13(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1))
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(resolution,[],[f70,f107])).

fof(f70,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f3775,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_wellord1(sK2,sK1))
      | ~ r2_hidden(X0,k1_wellord1(sK2,sK0))
      | sK1 = X0 ) ),
    inference(resolution,[],[f3771,f144])).

fof(f3771,plain,(
    ! [X3] :
      ( r2_hidden(k4_tarski(X3,sK1),sK2)
      | ~ r2_hidden(X3,k1_wellord1(sK2,sK0)) ) ),
    inference(subsumption_resolution,[],[f3770,f513])).

fof(f513,plain,(
    ! [X14,X15,X13] :
      ( ~ r2_hidden(X13,k1_wellord1(sK2,X14))
      | r2_hidden(k4_tarski(X13,X15),sK2)
      | ~ r2_hidden(k4_tarski(X14,X15),sK2) ) ),
    inference(subsumption_resolution,[],[f512,f65])).

fof(f512,plain,(
    ! [X14,X15,X13] :
      ( ~ r2_hidden(X13,k1_wellord1(sK2,X14))
      | r2_hidden(k4_tarski(X13,X15),sK2)
      | ~ r2_hidden(k4_tarski(X14,X15),sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f496,f149])).

fof(f149,plain,(
    v8_relat_2(sK2) ),
    inference(subsumption_resolution,[],[f133,f66])).

fof(f133,plain,
    ( v8_relat_2(sK2)
    | ~ v2_wellord1(sK2) ),
    inference(resolution,[],[f65,f88])).

fof(f88,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f496,plain,(
    ! [X14,X15,X13] :
      ( ~ r2_hidden(X13,k1_wellord1(sK2,X14))
      | r2_hidden(k4_tarski(X13,X15),sK2)
      | ~ r2_hidden(k4_tarski(X14,X15),sK2)
      | ~ v8_relat_2(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f145,f83])).

fof(f83,plain,(
    ! [X6,X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK8(X0),sK10(X0)),X0)
            & r2_hidden(k4_tarski(sK9(X0),sK10(X0)),X0)
            & r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f45,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_hidden(k4_tarski(X1,X3),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( ~ r2_hidden(k4_tarski(sK8(X0),sK10(X0)),X0)
        & r2_hidden(k4_tarski(sK9(X0),sK10(X0)),X0)
        & r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X1,X2,X3] :
              ( r2_hidden(k4_tarski(X1,X3),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(k4_tarski(X1,X2),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => r2_hidden(k4_tarski(X1,X3),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l2_wellord1)).

fof(f3770,plain,(
    ! [X3] :
      ( r2_hidden(k4_tarski(sK0,sK1),sK2)
      | ~ r2_hidden(X3,k1_wellord1(sK2,sK0))
      | r2_hidden(k4_tarski(X3,sK1),sK2) ) ),
    inference(subsumption_resolution,[],[f3717,f65])).

fof(f3717,plain,(
    ! [X3] :
      ( r2_hidden(k4_tarski(sK0,sK1),sK2)
      | ~ r2_hidden(X3,k1_wellord1(sK2,sK0))
      | r2_hidden(k4_tarski(X3,sK1),sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f517,f112])).

fof(f517,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK0,sK1),sK2)
      | r2_hidden(X0,k1_wellord1(sK2,sK1))
      | ~ r2_hidden(X0,k1_wellord1(sK2,sK0)) ) ),
    inference(resolution,[],[f69,f105])).

fof(f912,plain,
    ( r2_hidden(sK13(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(resolution,[],[f70,f106])).

fof(f26177,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f23806,f116])).

fof(f23806,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(backward_demodulation,[],[f70,f23803])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:52:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (22192)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.49  % (22178)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.50  % (22200)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.51  % (22175)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (22189)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (22184)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (22179)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (22201)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (22173)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (22198)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (22203)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (22176)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (22195)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (22193)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (22187)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (22196)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (22174)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (22190)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (22182)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (22177)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.56  % (22188)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.56  % (22186)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (22180)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (22202)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.57  % (22199)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.57  % (22194)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.57  % (22191)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.57  % (22185)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.65/0.58  % (22197)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.65/0.59  % (22183)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.81/0.59  % (22191)Refutation not found, incomplete strategy% (22191)------------------------------
% 1.81/0.59  % (22191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.59  % (22191)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.59  
% 1.81/0.59  % (22191)Memory used [KB]: 10746
% 1.81/0.59  % (22191)Time elapsed: 0.171 s
% 1.81/0.59  % (22191)------------------------------
% 1.81/0.59  % (22191)------------------------------
% 2.60/0.71  % (22223)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.00/0.83  % (22178)Time limit reached!
% 3.00/0.83  % (22178)------------------------------
% 3.00/0.83  % (22178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.00/0.83  % (22178)Termination reason: Time limit
% 3.00/0.83  
% 3.00/0.83  % (22178)Memory used [KB]: 8955
% 3.00/0.83  % (22178)Time elapsed: 0.426 s
% 3.00/0.83  % (22178)------------------------------
% 3.00/0.83  % (22178)------------------------------
% 4.02/0.91  % (22184)Time limit reached!
% 4.02/0.91  % (22184)------------------------------
% 4.02/0.91  % (22184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.02/0.91  % (22184)Termination reason: Time limit
% 4.02/0.91  
% 4.02/0.91  % (22184)Memory used [KB]: 13176
% 4.02/0.91  % (22184)Time elapsed: 0.506 s
% 4.02/0.91  % (22184)------------------------------
% 4.02/0.91  % (22184)------------------------------
% 4.02/0.92  % (22186)Time limit reached!
% 4.02/0.92  % (22186)------------------------------
% 4.02/0.92  % (22186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.02/0.92  % (22186)Termination reason: Time limit
% 4.02/0.92  
% 4.02/0.92  % (22186)Memory used [KB]: 8315
% 4.02/0.92  % (22186)Time elapsed: 0.518 s
% 4.02/0.92  % (22186)------------------------------
% 4.02/0.92  % (22186)------------------------------
% 4.02/0.92  % (22173)Time limit reached!
% 4.02/0.92  % (22173)------------------------------
% 4.02/0.92  % (22173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.02/0.92  % (22173)Termination reason: Time limit
% 4.02/0.92  
% 4.02/0.92  % (22173)Memory used [KB]: 3582
% 4.02/0.92  % (22173)Time elapsed: 0.514 s
% 4.02/0.92  % (22173)------------------------------
% 4.02/0.92  % (22173)------------------------------
% 4.02/0.94  % (22174)Time limit reached!
% 4.02/0.94  % (22174)------------------------------
% 4.02/0.94  % (22174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.02/0.94  % (22174)Termination reason: Time limit
% 4.02/0.94  
% 4.02/0.94  % (22174)Memory used [KB]: 7803
% 4.02/0.94  % (22174)Time elapsed: 0.525 s
% 4.02/0.94  % (22174)------------------------------
% 4.02/0.94  % (22174)------------------------------
% 4.82/1.01  % (22224)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 4.82/1.01  % (22190)Time limit reached!
% 4.82/1.01  % (22190)------------------------------
% 4.82/1.01  % (22190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.82/1.01  % (22190)Termination reason: Time limit
% 4.82/1.01  
% 4.82/1.01  % (22190)Memory used [KB]: 14583
% 4.82/1.01  % (22190)Time elapsed: 0.608 s
% 4.82/1.01  % (22190)------------------------------
% 4.82/1.01  % (22190)------------------------------
% 4.82/1.05  % (22226)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.82/1.05  % (22202)Time limit reached!
% 4.82/1.05  % (22202)------------------------------
% 4.82/1.05  % (22202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.82/1.05  % (22202)Termination reason: Time limit
% 4.82/1.05  
% 4.82/1.05  % (22202)Memory used [KB]: 7164
% 4.82/1.05  % (22202)Time elapsed: 0.638 s
% 4.82/1.05  % (22202)------------------------------
% 4.82/1.05  % (22202)------------------------------
% 4.82/1.05  % (22225)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.82/1.05  % (22227)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.49/1.11  % (22228)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.49/1.11  % (22180)Time limit reached!
% 5.49/1.11  % (22180)------------------------------
% 5.49/1.11  % (22180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.49/1.11  % (22180)Termination reason: Time limit
% 5.49/1.11  % (22180)Termination phase: Saturation
% 5.49/1.11  
% 5.49/1.11  % (22180)Memory used [KB]: 9850
% 5.49/1.11  % (22180)Time elapsed: 0.600 s
% 5.49/1.11  % (22180)------------------------------
% 5.49/1.11  % (22180)------------------------------
% 6.22/1.17  % (22229)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 6.22/1.18  % (22230)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.54/1.22  % (22195)Time limit reached!
% 6.54/1.22  % (22195)------------------------------
% 6.54/1.22  % (22195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.54/1.22  % (22195)Termination reason: Time limit
% 6.54/1.22  
% 6.54/1.22  % (22195)Memory used [KB]: 3709
% 6.54/1.22  % (22195)Time elapsed: 0.817 s
% 6.54/1.22  % (22195)------------------------------
% 6.54/1.22  % (22195)------------------------------
% 6.54/1.23  % (22231)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.85/1.31  % (22232)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 7.48/1.34  % (22227)Time limit reached!
% 7.48/1.34  % (22227)------------------------------
% 7.48/1.34  % (22227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.48/1.34  % (22227)Termination reason: Time limit
% 7.48/1.34  % (22227)Termination phase: Saturation
% 7.48/1.34  
% 7.48/1.34  % (22227)Memory used [KB]: 12281
% 7.48/1.34  % (22227)Time elapsed: 0.400 s
% 7.48/1.34  % (22227)------------------------------
% 7.48/1.34  % (22227)------------------------------
% 7.48/1.37  % (22226)Time limit reached!
% 7.48/1.37  % (22226)------------------------------
% 7.48/1.37  % (22226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.48/1.37  % (22226)Termination reason: Time limit
% 7.48/1.37  
% 7.48/1.37  % (22226)Memory used [KB]: 6780
% 7.48/1.37  % (22226)Time elapsed: 0.406 s
% 7.48/1.37  % (22226)------------------------------
% 7.48/1.37  % (22226)------------------------------
% 7.90/1.42  % (22175)Time limit reached!
% 7.90/1.42  % (22175)------------------------------
% 7.90/1.42  % (22175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.90/1.42  % (22175)Termination reason: Time limit
% 7.90/1.42  
% 7.90/1.42  % (22175)Memory used [KB]: 15479
% 7.90/1.42  % (22175)Time elapsed: 1.010 s
% 7.90/1.42  % (22175)------------------------------
% 7.90/1.42  % (22175)------------------------------
% 8.33/1.48  % (22233)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 8.57/1.54  % (22235)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 8.81/1.55  % (22234)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 8.81/1.61  % (22200)Time limit reached!
% 8.81/1.61  % (22200)------------------------------
% 8.81/1.61  % (22200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.81/1.61  % (22200)Termination reason: Time limit
% 8.81/1.61  
% 8.81/1.61  % (22200)Memory used [KB]: 15479
% 8.81/1.61  % (22200)Time elapsed: 1.204 s
% 8.81/1.61  % (22200)------------------------------
% 8.81/1.61  % (22200)------------------------------
% 9.32/1.67  % (22196)Time limit reached!
% 9.32/1.67  % (22196)------------------------------
% 9.32/1.67  % (22196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.32/1.67  % (22196)Termination reason: Time limit
% 9.32/1.67  % (22196)Termination phase: Saturation
% 9.32/1.67  
% 9.32/1.67  % (22196)Memory used [KB]: 16119
% 9.32/1.67  % (22196)Time elapsed: 1.200 s
% 9.32/1.67  % (22196)------------------------------
% 9.32/1.67  % (22196)------------------------------
% 10.58/1.70  % (22198)Time limit reached!
% 10.58/1.70  % (22198)------------------------------
% 10.58/1.70  % (22198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.58/1.70  % (22198)Termination reason: Time limit
% 10.58/1.70  % (22198)Termination phase: Saturation
% 10.58/1.70  
% 10.58/1.70  % (22198)Memory used [KB]: 16119
% 10.58/1.70  % (22198)Time elapsed: 1.300 s
% 10.58/1.70  % (22198)------------------------------
% 10.58/1.70  % (22198)------------------------------
% 10.58/1.70  % (22189)Time limit reached!
% 10.58/1.70  % (22189)------------------------------
% 10.58/1.70  % (22189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.58/1.70  % (22189)Termination reason: Time limit
% 10.58/1.70  % (22189)Termination phase: Saturation
% 10.58/1.70  
% 10.58/1.70  % (22189)Memory used [KB]: 16630
% 10.58/1.70  % (22189)Time elapsed: 1.300 s
% 10.58/1.70  % (22189)------------------------------
% 10.58/1.70  % (22189)------------------------------
% 11.06/1.78  % (22236)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 11.37/1.83  % (22238)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 11.59/1.83  % (22237)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 11.59/1.91  % (22239)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 11.59/1.93  % (22177)Time limit reached!
% 11.59/1.93  % (22177)------------------------------
% 11.59/1.93  % (22177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.59/1.93  % (22177)Termination reason: Time limit
% 11.59/1.93  
% 11.59/1.93  % (22177)Memory used [KB]: 12409
% 11.59/1.93  % (22177)Time elapsed: 1.517 s
% 11.59/1.93  % (22177)------------------------------
% 11.59/1.93  % (22177)------------------------------
% 12.26/1.93  % (22201)Time limit reached!
% 12.26/1.93  % (22201)------------------------------
% 12.26/1.93  % (22201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.26/1.93  % (22201)Termination reason: Time limit
% 12.26/1.93  
% 12.26/1.93  % (22201)Memory used [KB]: 13304
% 12.26/1.93  % (22201)Time elapsed: 1.528 s
% 12.26/1.93  % (22201)------------------------------
% 12.26/1.93  % (22201)------------------------------
% 12.26/1.96  % (22235)Time limit reached!
% 12.26/1.96  % (22235)------------------------------
% 12.26/1.96  % (22235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.26/1.96  % (22235)Termination reason: Time limit
% 12.26/1.96  
% 12.26/1.96  % (22235)Memory used [KB]: 3454
% 12.26/1.96  % (22235)Time elapsed: 0.521 s
% 12.26/1.96  % (22235)------------------------------
% 12.26/1.96  % (22235)------------------------------
% 12.73/2.03  % (22185)Time limit reached!
% 12.73/2.03  % (22185)------------------------------
% 12.73/2.03  % (22185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.73/2.03  % (22185)Termination reason: Time limit
% 12.73/2.03  % (22185)Termination phase: Saturation
% 12.73/2.03  
% 12.73/2.03  % (22185)Memory used [KB]: 14839
% 12.73/2.03  % (22185)Time elapsed: 1.629 s
% 12.73/2.03  % (22185)------------------------------
% 12.73/2.03  % (22185)------------------------------
% 12.73/2.06  % (22242)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 13.23/2.07  % (22243)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 13.23/2.10  % (22254)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 13.64/2.14  % (22239)Time limit reached!
% 13.64/2.14  % (22239)------------------------------
% 13.64/2.14  % (22239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.64/2.16  % (22285)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 13.64/2.17  % (22239)Termination reason: Time limit
% 13.64/2.17  % (22239)Termination phase: Saturation
% 13.64/2.17  
% 13.64/2.17  % (22239)Memory used [KB]: 3198
% 13.64/2.17  % (22239)Time elapsed: 0.400 s
% 13.64/2.17  % (22239)------------------------------
% 13.64/2.17  % (22239)------------------------------
% 14.81/2.25  % (22229)Time limit reached!
% 14.81/2.25  % (22229)------------------------------
% 14.81/2.25  % (22229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.81/2.26  % (22229)Termination reason: Time limit
% 14.81/2.26  
% 14.81/2.26  % (22229)Memory used [KB]: 7291
% 14.81/2.26  % (22229)Time elapsed: 1.220 s
% 14.81/2.26  % (22229)------------------------------
% 14.81/2.26  % (22229)------------------------------
% 14.81/2.29  % (22366)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 15.31/2.31  % (22188)Time limit reached!
% 15.31/2.31  % (22188)------------------------------
% 15.31/2.31  % (22188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.31/2.31  % (22188)Termination reason: Time limit
% 15.31/2.31  
% 15.31/2.31  % (22188)Memory used [KB]: 4861
% 15.31/2.31  % (22188)Time elapsed: 1.816 s
% 15.31/2.31  % (22188)------------------------------
% 15.31/2.31  % (22188)------------------------------
% 15.85/2.40  % (22402)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 15.85/2.41  % (22254)Time limit reached!
% 15.85/2.41  % (22254)------------------------------
% 15.85/2.41  % (22254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.85/2.41  % (22254)Termination reason: Time limit
% 15.85/2.41  
% 15.85/2.41  % (22254)Memory used [KB]: 2174
% 15.85/2.41  % (22254)Time elapsed: 0.412 s
% 15.85/2.41  % (22254)------------------------------
% 15.85/2.41  % (22254)------------------------------
% 15.85/2.41  % (22192)Time limit reached!
% 15.85/2.41  % (22192)------------------------------
% 15.85/2.41  % (22192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.85/2.42  % (22179)Time limit reached!
% 15.85/2.42  % (22179)------------------------------
% 15.85/2.42  % (22179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.85/2.43  % (22192)Termination reason: Time limit
% 15.85/2.43  
% 15.85/2.43  % (22192)Memory used [KB]: 14967
% 15.85/2.43  % (22192)Time elapsed: 2.020 s
% 15.85/2.43  % (22192)------------------------------
% 15.85/2.43  % (22192)------------------------------
% 15.85/2.43  % (22179)Termination reason: Time limit
% 15.85/2.43  % (22179)Termination phase: Saturation
% 15.85/2.43  
% 15.85/2.43  % (22179)Memory used [KB]: 15479
% 15.85/2.43  % (22179)Time elapsed: 2.0000 s
% 15.85/2.43  % (22179)------------------------------
% 15.85/2.43  % (22179)------------------------------
% 15.85/2.46  % (22419)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 16.95/2.52  % (22469)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 16.95/2.52  % (22470)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 16.98/2.55  % (22451)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 17.46/2.65  % (22225)Time limit reached!
% 17.46/2.65  % (22225)------------------------------
% 17.46/2.65  % (22225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.46/2.65  % (22225)Termination reason: Time limit
% 17.46/2.65  
% 17.46/2.65  % (22225)Memory used [KB]: 15223
% 17.46/2.65  % (22225)Time elapsed: 1.704 s
% 17.46/2.65  % (22225)------------------------------
% 17.46/2.65  % (22225)------------------------------
% 18.55/2.78  % (22482)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 19.66/2.85  % (22231)Time limit reached!
% 19.66/2.85  % (22231)------------------------------
% 19.66/2.85  % (22231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.66/2.85  % (22231)Termination reason: Time limit
% 19.66/2.85  
% 19.66/2.85  % (22231)Memory used [KB]: 8955
% 19.66/2.85  % (22231)Time elapsed: 1.715 s
% 19.66/2.85  % (22231)------------------------------
% 19.66/2.85  % (22231)------------------------------
% 19.66/2.85  % (22451)Time limit reached!
% 19.66/2.85  % (22451)------------------------------
% 19.66/2.85  % (22451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.66/2.85  % (22451)Termination reason: Time limit
% 19.66/2.85  
% 19.66/2.85  % (22451)Memory used [KB]: 9850
% 19.66/2.85  % (22451)Time elapsed: 0.412 s
% 19.66/2.85  % (22451)------------------------------
% 19.66/2.85  % (22451)------------------------------
% 20.26/2.92  % (22470)Time limit reached!
% 20.26/2.92  % (22470)------------------------------
% 20.26/2.92  % (22470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.26/2.92  % (22470)Termination reason: Time limit
% 20.26/2.92  
% 20.26/2.92  % (22470)Memory used [KB]: 9594
% 20.26/2.92  % (22470)Time elapsed: 0.427 s
% 20.26/2.92  % (22470)------------------------------
% 20.26/2.92  % (22470)------------------------------
% 20.26/2.94  % (22182)Time limit reached!
% 20.26/2.94  % (22182)------------------------------
% 20.26/2.94  % (22182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.26/2.94  % (22182)Termination reason: Time limit
% 20.26/2.94  
% 20.26/2.94  % (22182)Memory used [KB]: 21236
% 20.26/2.94  % (22182)Time elapsed: 2.531 s
% 20.26/2.94  % (22182)------------------------------
% 20.26/2.94  % (22182)------------------------------
% 20.72/3.01  % (22238)Time limit reached!
% 20.72/3.01  % (22238)------------------------------
% 20.72/3.01  % (22238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.72/3.02  % (22238)Termination reason: Time limit
% 20.72/3.02  % (22238)Termination phase: Saturation
% 20.72/3.02  
% 20.72/3.02  % (22238)Memory used [KB]: 16886
% 20.72/3.02  % (22238)Time elapsed: 1.200 s
% 20.72/3.02  % (22238)------------------------------
% 20.72/3.02  % (22238)------------------------------
% 21.36/3.08  % (22193)Time limit reached!
% 21.36/3.08  % (22193)------------------------------
% 21.36/3.08  % (22193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.57/3.08  % (22193)Termination reason: Time limit
% 21.57/3.08  
% 21.57/3.08  % (22193)Memory used [KB]: 23283
% 21.57/3.08  % (22193)Time elapsed: 2.652 s
% 21.57/3.08  % (22193)------------------------------
% 21.57/3.08  % (22193)------------------------------
% 23.10/3.30  % (22243)Time limit reached!
% 23.10/3.30  % (22243)------------------------------
% 23.10/3.30  % (22243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.10/3.30  % (22243)Termination reason: Time limit
% 23.10/3.30  % (22243)Termination phase: Saturation
% 23.10/3.30  
% 23.10/3.30  % (22243)Memory used [KB]: 9466
% 23.10/3.30  % (22243)Time elapsed: 1.300 s
% 23.10/3.30  % (22243)------------------------------
% 23.10/3.30  % (22243)------------------------------
% 24.02/3.40  % (22187)Time limit reached!
% 24.02/3.40  % (22187)------------------------------
% 24.02/3.40  % (22187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.02/3.40  % (22187)Termination reason: Time limit
% 24.02/3.40  % (22187)Termination phase: Saturation
% 24.02/3.40  
% 24.02/3.40  % (22187)Memory used [KB]: 17142
% 24.02/3.40  % (22187)Time elapsed: 3.0000 s
% 24.02/3.40  % (22187)------------------------------
% 24.02/3.40  % (22187)------------------------------
% 26.41/3.70  % (22224)Time limit reached!
% 26.41/3.70  % (22224)------------------------------
% 26.41/3.70  % (22224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 26.41/3.70  % (22224)Termination reason: Time limit
% 26.41/3.70  % (22224)Termination phase: Saturation
% 26.41/3.70  
% 26.41/3.70  % (22224)Memory used [KB]: 14456
% 26.41/3.70  % (22224)Time elapsed: 2.800 s
% 26.41/3.70  % (22224)------------------------------
% 26.41/3.70  % (22224)------------------------------
% 31.24/4.32  % (22203)Time limit reached!
% 31.24/4.32  % (22203)------------------------------
% 31.24/4.32  % (22203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.67/4.34  % (22203)Termination reason: Time limit
% 31.67/4.34  
% 31.67/4.34  % (22203)Memory used [KB]: 18038
% 31.67/4.34  % (22203)Time elapsed: 3.921 s
% 31.67/4.34  % (22203)------------------------------
% 31.67/4.34  % (22203)------------------------------
% 34.88/4.77  % (22197)Refutation found. Thanks to Tanya!
% 34.88/4.77  % SZS status Theorem for theBenchmark
% 34.88/4.77  % SZS output start Proof for theBenchmark
% 34.88/4.77  fof(f36426,plain,(
% 34.88/4.77    $false),
% 34.88/4.77    inference(subsumption_resolution,[],[f34962,f1352])).
% 34.88/4.77  fof(f1352,plain,(
% 34.88/4.77    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 34.88/4.77    inference(resolution,[],[f1351,f108])).
% 34.88/4.77  fof(f108,plain,(
% 34.88/4.77    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 34.88/4.77    inference(cnf_transformation,[],[f27])).
% 34.88/4.77  fof(f27,plain,(
% 34.88/4.77    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 34.88/4.77    inference(ennf_transformation,[],[f4])).
% 34.88/4.77  fof(f4,axiom,(
% 34.88/4.77    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 34.88/4.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 34.88/4.78  fof(f1351,plain,(
% 34.88/4.78    ( ! [X7] : (r1_tarski(k1_xboole_0,X7)) )),
% 34.88/4.78    inference(subsumption_resolution,[],[f1343,f116])).
% 34.88/4.78  fof(f116,plain,(
% 34.88/4.78    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 34.88/4.78    inference(equality_resolution,[],[f102])).
% 34.88/4.78  fof(f102,plain,(
% 34.88/4.78    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 34.88/4.78    inference(cnf_transformation,[],[f60])).
% 34.88/4.78  fof(f60,plain,(
% 34.88/4.78    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 34.88/4.78    inference(flattening,[],[f59])).
% 34.88/4.78  fof(f59,plain,(
% 34.88/4.78    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 34.88/4.78    inference(nnf_transformation,[],[f2])).
% 34.88/4.78  fof(f2,axiom,(
% 34.88/4.78    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 34.88/4.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 34.88/4.78  fof(f1343,plain,(
% 34.88/4.78    ( ! [X7] : (r1_tarski(k1_xboole_0,X7) | ~r1_tarski(k3_relat_1(sK2),k3_relat_1(sK2))) )),
% 34.88/4.78    inference(resolution,[],[f1200,f108])).
% 34.88/4.78  fof(f1200,plain,(
% 34.88/4.78    ( ! [X4] : (r1_tarski(k1_xboole_0,X4) | r2_hidden(k3_relat_1(sK2),k3_relat_1(sK2))) )),
% 34.88/4.78    inference(superposition,[],[f423,f1188])).
% 34.88/4.78  fof(f1188,plain,(
% 34.88/4.78    k1_xboole_0 = k1_wellord1(sK2,k3_relat_1(sK2))),
% 34.88/4.78    inference(resolution,[],[f1161,f116])).
% 34.88/4.78  fof(f1161,plain,(
% 34.88/4.78    ( ! [X6] : (~r1_tarski(k3_relat_1(sK2),X6) | k1_xboole_0 = k1_wellord1(sK2,X6)) )),
% 34.88/4.78    inference(resolution,[],[f1157,f108])).
% 34.88/4.78  fof(f1157,plain,(
% 34.88/4.78    ( ! [X2] : (r2_hidden(X2,k3_relat_1(sK2)) | k1_xboole_0 = k1_wellord1(sK2,X2)) )),
% 34.88/4.78    inference(subsumption_resolution,[],[f1156,f369])).
% 34.88/4.78  fof(f369,plain,(
% 34.88/4.78    ( ! [X6,X7] : (~r2_hidden(X7,k1_wellord1(sK2,X6)) | r2_hidden(X6,k3_relat_1(sK2))) )),
% 34.88/4.78    inference(subsumption_resolution,[],[f362,f65])).
% 34.88/4.78  fof(f65,plain,(
% 34.88/4.78    v1_relat_1(sK2)),
% 34.88/4.78    inference(cnf_transformation,[],[f33])).
% 34.88/4.78  fof(f33,plain,(
% 34.88/4.78    (~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)) & (r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | r2_hidden(k4_tarski(sK0,sK1),sK2)) & r2_hidden(sK1,k3_relat_1(sK2)) & r2_hidden(sK0,k3_relat_1(sK2)) & v2_wellord1(sK2) & v1_relat_1(sK2)),
% 34.88/4.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f32])).
% 34.88/4.78  fof(f32,plain,(
% 34.88/4.78    ? [X0,X1,X2] : ((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2)) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2)) => ((~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)) & (r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | r2_hidden(k4_tarski(sK0,sK1),sK2)) & r2_hidden(sK1,k3_relat_1(sK2)) & r2_hidden(sK0,k3_relat_1(sK2)) & v2_wellord1(sK2) & v1_relat_1(sK2))),
% 34.88/4.78    introduced(choice_axiom,[])).
% 34.88/4.78  fof(f31,plain,(
% 34.88/4.78    ? [X0,X1,X2] : ((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2)) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 34.88/4.78    inference(flattening,[],[f30])).
% 34.88/4.78  fof(f30,plain,(
% 34.88/4.78    ? [X0,X1,X2] : (((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 34.88/4.78    inference(nnf_transformation,[],[f15])).
% 34.88/4.78  fof(f15,plain,(
% 34.88/4.78    ? [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 34.88/4.78    inference(flattening,[],[f14])).
% 34.88/4.78  fof(f14,plain,(
% 34.88/4.78    ? [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2))) & v1_relat_1(X2))),
% 34.88/4.78    inference(ennf_transformation,[],[f13])).
% 34.88/4.78  fof(f13,negated_conjecture,(
% 34.88/4.78    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 34.88/4.78    inference(negated_conjecture,[],[f12])).
% 34.88/4.78  fof(f12,conjecture,(
% 34.88/4.78    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 34.88/4.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).
% 34.88/4.78  fof(f362,plain,(
% 34.88/4.78    ( ! [X6,X7] : (r2_hidden(X6,k3_relat_1(sK2)) | ~r2_hidden(X7,k1_wellord1(sK2,X6)) | ~v1_relat_1(sK2)) )),
% 34.88/4.78    inference(resolution,[],[f143,f112])).
% 34.88/4.78  fof(f112,plain,(
% 34.88/4.78    ( ! [X4,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,k1_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 34.88/4.78    inference(equality_resolution,[],[f94])).
% 34.88/4.78  fof(f94,plain,(
% 34.88/4.78    ( ! [X4,X2,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 34.88/4.78    inference(cnf_transformation,[],[f54])).
% 34.88/4.78  fof(f54,plain,(
% 34.88/4.78    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK11(X0,X1,X2),X1),X0) | sK11(X0,X1,X2) = X1 | ~r2_hidden(sK11(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK11(X0,X1,X2),X1),X0) & sK11(X0,X1,X2) != X1) | r2_hidden(sK11(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f52,f53])).
% 34.88/4.78  fof(f53,plain,(
% 34.88/4.78    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK11(X0,X1,X2),X1),X0) | sK11(X0,X1,X2) = X1 | ~r2_hidden(sK11(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK11(X0,X1,X2),X1),X0) & sK11(X0,X1,X2) != X1) | r2_hidden(sK11(X0,X1,X2),X2))))),
% 34.88/4.78    introduced(choice_axiom,[])).
% 34.88/4.78  fof(f52,plain,(
% 34.88/4.78    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(rectify,[],[f51])).
% 34.88/4.78  fof(f51,plain,(
% 34.88/4.78    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(flattening,[],[f50])).
% 34.88/4.78  fof(f50,plain,(
% 34.88/4.78    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(nnf_transformation,[],[f24])).
% 34.88/4.78  fof(f24,plain,(
% 34.88/4.78    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(ennf_transformation,[],[f5])).
% 34.88/4.78  fof(f5,axiom,(
% 34.88/4.78    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 34.88/4.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).
% 34.88/4.78  fof(f143,plain,(
% 34.88/4.78    ( ! [X24,X25] : (~r2_hidden(k4_tarski(X25,X24),sK2) | r2_hidden(X24,k3_relat_1(sK2))) )),
% 34.88/4.78    inference(resolution,[],[f65,f110])).
% 34.88/4.78  fof(f110,plain,(
% 34.88/4.78    ( ! [X2,X0,X1] : (r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 34.88/4.78    inference(cnf_transformation,[],[f29])).
% 34.88/4.78  fof(f29,plain,(
% 34.88/4.78    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 34.88/4.78    inference(flattening,[],[f28])).
% 34.88/4.78  fof(f28,plain,(
% 34.88/4.78    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 34.88/4.78    inference(ennf_transformation,[],[f3])).
% 34.88/4.78  fof(f3,axiom,(
% 34.88/4.78    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 34.88/4.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).
% 34.88/4.78  fof(f1156,plain,(
% 34.88/4.78    ( ! [X2] : (k1_xboole_0 = k1_wellord1(sK2,X2) | r2_hidden(sK3(sK2,k1_wellord1(sK2,X2)),k1_wellord1(sK2,X2)) | r2_hidden(X2,k3_relat_1(sK2))) )),
% 34.88/4.78    inference(resolution,[],[f147,f423])).
% 34.88/4.78  fof(f147,plain,(
% 34.88/4.78    ( ! [X0] : (~r1_tarski(X0,k3_relat_1(sK2)) | k1_xboole_0 = X0 | r2_hidden(sK3(sK2,X0),X0)) )),
% 34.88/4.78    inference(subsumption_resolution,[],[f117,f66])).
% 34.88/4.78  fof(f66,plain,(
% 34.88/4.78    v2_wellord1(sK2)),
% 34.88/4.78    inference(cnf_transformation,[],[f33])).
% 34.88/4.78  fof(f117,plain,(
% 34.88/4.78    ( ! [X0] : (r2_hidden(sK3(sK2,X0),X0) | k1_xboole_0 = X0 | ~r1_tarski(X0,k3_relat_1(sK2)) | ~v2_wellord1(sK2)) )),
% 34.88/4.78    inference(resolution,[],[f65,f71])).
% 34.88/4.78  fof(f71,plain,(
% 34.88/4.78    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 34.88/4.78    inference(cnf_transformation,[],[f35])).
% 34.88/4.78  fof(f35,plain,(
% 34.88/4.78    ! [X0] : (! [X1] : ((! [X3] : (r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(sK3(X0,X1),X1)) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f34])).
% 34.88/4.78  fof(f34,plain,(
% 34.88/4.78    ! [X1,X0] : (? [X2] : (! [X3] : (r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(sK3(X0,X1),X1)))),
% 34.88/4.78    introduced(choice_axiom,[])).
% 34.88/4.78  fof(f17,plain,(
% 34.88/4.78    ! [X0] : (! [X1] : (? [X2] : (! [X3] : (r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(flattening,[],[f16])).
% 34.88/4.78  fof(f16,plain,(
% 34.88/4.78    ! [X0] : ((! [X1] : (? [X2] : (! [X3] : (r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(ennf_transformation,[],[f11])).
% 34.88/4.78  fof(f11,axiom,(
% 34.88/4.78    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(! [X2] : ~(! [X3] : (r2_hidden(X3,X1) => r2_hidden(k4_tarski(X2,X3),X0)) & r2_hidden(X2,X1)) & k1_xboole_0 != X1 & r1_tarski(X1,k3_relat_1(X0)))))),
% 34.88/4.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord1)).
% 34.88/4.78  fof(f423,plain,(
% 34.88/4.78    ( ! [X39,X40] : (r1_tarski(k1_wellord1(sK2,X39),X40) | r2_hidden(X39,k3_relat_1(sK2))) )),
% 34.88/4.78    inference(resolution,[],[f369,f106])).
% 34.88/4.78  fof(f106,plain,(
% 34.88/4.78    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK13(X0,X1),X0)) )),
% 34.88/4.78    inference(cnf_transformation,[],[f64])).
% 34.88/4.78  fof(f64,plain,(
% 34.88/4.78    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK13(X0,X1),X1) & r2_hidden(sK13(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 34.88/4.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f62,f63])).
% 34.88/4.78  fof(f63,plain,(
% 34.88/4.78    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK13(X0,X1),X1) & r2_hidden(sK13(X0,X1),X0)))),
% 34.88/4.78    introduced(choice_axiom,[])).
% 34.88/4.78  fof(f62,plain,(
% 34.88/4.78    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 34.88/4.78    inference(rectify,[],[f61])).
% 34.88/4.78  fof(f61,plain,(
% 34.88/4.78    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 34.88/4.78    inference(nnf_transformation,[],[f26])).
% 34.88/4.78  fof(f26,plain,(
% 34.88/4.78    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 34.88/4.78    inference(ennf_transformation,[],[f1])).
% 34.88/4.78  fof(f1,axiom,(
% 34.88/4.78    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 34.88/4.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 34.88/4.78  fof(f34962,plain,(
% 34.88/4.78    r2_hidden(sK0,k1_xboole_0)),
% 34.88/4.78    inference(backward_demodulation,[],[f27668,f34725])).
% 34.88/4.78  fof(f34725,plain,(
% 34.88/4.78    k1_xboole_0 = sK12(sK2,sK0)),
% 34.88/4.78    inference(resolution,[],[f34704,f27668])).
% 34.88/4.78  fof(f34704,plain,(
% 34.88/4.78    ( ! [X0] : (~r2_hidden(X0,sK12(sK2,X0)) | k1_xboole_0 = sK12(sK2,X0)) )),
% 34.88/4.78    inference(subsumption_resolution,[],[f34703,f5273])).
% 34.88/4.78  fof(f5273,plain,(
% 34.88/4.78    ( ! [X0] : (r1_tarski(sK12(sK2,X0),k3_relat_1(sK2))) )),
% 34.88/4.78    inference(duplicate_literal_removal,[],[f5260])).
% 34.88/4.78  fof(f5260,plain,(
% 34.88/4.78    ( ! [X0] : (r1_tarski(sK12(sK2,X0),k3_relat_1(sK2)) | r1_tarski(sK12(sK2,X0),k3_relat_1(sK2))) )),
% 34.88/4.78    inference(resolution,[],[f330,f107])).
% 34.88/4.78  fof(f107,plain,(
% 34.88/4.78    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK13(X0,X1),X1)) )),
% 34.88/4.78    inference(cnf_transformation,[],[f64])).
% 34.88/4.78  fof(f330,plain,(
% 34.88/4.78    ( ! [X39,X40] : (r2_hidden(sK13(sK12(sK2,X39),X40),k3_relat_1(sK2)) | r1_tarski(sK12(sK2,X39),X40)) )),
% 34.88/4.78    inference(resolution,[],[f139,f106])).
% 34.88/4.78  fof(f139,plain,(
% 34.88/4.78    ( ! [X17,X16] : (~r2_hidden(X16,sK12(sK2,X17)) | r2_hidden(X16,k3_relat_1(sK2))) )),
% 34.88/4.78    inference(resolution,[],[f65,f99])).
% 34.88/4.78  fof(f99,plain,(
% 34.88/4.78    ( ! [X0,X3,X1] : (r2_hidden(X3,k3_relat_1(X0)) | ~r2_hidden(X3,sK12(X0,X1)) | ~v1_relat_1(X0)) )),
% 34.88/4.78    inference(cnf_transformation,[],[f58])).
% 34.88/4.78  fof(f58,plain,(
% 34.88/4.78    ! [X0,X1] : (! [X3] : ((r2_hidden(X3,sK12(X0,X1)) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0))) & ((~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(X3,sK12(X0,X1)))) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f56,f57])).
% 34.88/4.78  fof(f57,plain,(
% 34.88/4.78    ! [X1,X0] : (? [X2] : ! [X3] : ((r2_hidden(X3,X2) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0))) & ((~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(X3,X2))) => ! [X3] : ((r2_hidden(X3,sK12(X0,X1)) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0))) & ((~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(X3,sK12(X0,X1)))))),
% 34.88/4.78    introduced(choice_axiom,[])).
% 34.88/4.78  fof(f56,plain,(
% 34.88/4.78    ! [X0,X1] : (? [X2] : ! [X3] : ((r2_hidden(X3,X2) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0))) & ((~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(X3,X2))) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(flattening,[],[f55])).
% 34.88/4.78  fof(f55,plain,(
% 34.88/4.78    ! [X0,X1] : (? [X2] : ! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0)))) & ((~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(X3,X2))) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(nnf_transformation,[],[f25])).
% 34.88/4.78  fof(f25,plain,(
% 34.88/4.78    ! [X0,X1] : (? [X2] : ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(ennf_transformation,[],[f10])).
% 34.88/4.78  fof(f10,axiom,(
% 34.88/4.78    ! [X0,X1] : (v1_relat_1(X0) => ? [X2] : ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0)))))),
% 34.88/4.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s1_xboole_0__e7_18__wellord1)).
% 34.88/4.78  fof(f34703,plain,(
% 34.88/4.78    ( ! [X0] : (k1_xboole_0 = sK12(sK2,X0) | ~r2_hidden(X0,sK12(sK2,X0)) | ~r1_tarski(sK12(sK2,X0),k3_relat_1(sK2))) )),
% 34.88/4.78    inference(duplicate_literal_removal,[],[f34689])).
% 34.88/4.78  fof(f34689,plain,(
% 34.88/4.78    ( ! [X0] : (k1_xboole_0 = sK12(sK2,X0) | ~r2_hidden(X0,sK12(sK2,X0)) | k1_xboole_0 = sK12(sK2,X0) | ~r1_tarski(sK12(sK2,X0),k3_relat_1(sK2))) )),
% 34.88/4.78    inference(resolution,[],[f23687,f148])).
% 34.88/4.78  fof(f148,plain,(
% 34.88/4.78    ( ! [X2,X1] : (r2_hidden(k4_tarski(sK3(sK2,X1),X2),sK2) | ~r2_hidden(X2,X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(sK2))) )),
% 34.88/4.78    inference(subsumption_resolution,[],[f118,f66])).
% 34.88/4.78  fof(f118,plain,(
% 34.88/4.78    ( ! [X2,X1] : (r2_hidden(k4_tarski(sK3(sK2,X1),X2),sK2) | ~r2_hidden(X2,X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(sK2)) | ~v2_wellord1(sK2)) )),
% 34.88/4.78    inference(resolution,[],[f65,f72])).
% 34.88/4.78  fof(f72,plain,(
% 34.88/4.78    ( ! [X0,X3,X1] : (r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(X3,X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 34.88/4.78    inference(cnf_transformation,[],[f35])).
% 34.88/4.78  fof(f23687,plain,(
% 34.88/4.78    ( ! [X8] : (~r2_hidden(k4_tarski(sK3(sK2,sK12(sK2,X8)),X8),sK2) | k1_xboole_0 = sK12(sK2,X8)) )),
% 34.88/4.78    inference(subsumption_resolution,[],[f23668,f65])).
% 34.88/4.78  fof(f23668,plain,(
% 34.88/4.78    ( ! [X8] : (k1_xboole_0 = sK12(sK2,X8) | ~r2_hidden(k4_tarski(sK3(sK2,sK12(sK2,X8)),X8),sK2) | ~v1_relat_1(sK2)) )),
% 34.88/4.78    inference(resolution,[],[f5280,f100])).
% 34.88/4.78  fof(f100,plain,(
% 34.88/4.78    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,sK12(X0,X1)) | ~v1_relat_1(X0)) )),
% 34.88/4.78    inference(cnf_transformation,[],[f58])).
% 34.88/4.78  fof(f5280,plain,(
% 34.88/4.78    ( ! [X2] : (r2_hidden(sK3(sK2,sK12(sK2,X2)),sK12(sK2,X2)) | k1_xboole_0 = sK12(sK2,X2)) )),
% 34.88/4.78    inference(resolution,[],[f5273,f147])).
% 34.88/4.78  fof(f27668,plain,(
% 34.88/4.78    r2_hidden(sK0,sK12(sK2,sK0))),
% 34.88/4.78    inference(resolution,[],[f26178,f169])).
% 34.88/4.78  fof(f169,plain,(
% 34.88/4.78    ( ! [X0] : (r2_hidden(k4_tarski(sK0,X0),sK2) | r2_hidden(sK0,sK12(sK2,X0))) )),
% 34.88/4.78    inference(subsumption_resolution,[],[f163,f65])).
% 34.88/4.78  fof(f163,plain,(
% 34.88/4.78    ( ! [X0] : (r2_hidden(sK0,sK12(sK2,X0)) | r2_hidden(k4_tarski(sK0,X0),sK2) | ~v1_relat_1(sK2)) )),
% 34.88/4.78    inference(resolution,[],[f67,f101])).
% 34.88/4.78  fof(f101,plain,(
% 34.88/4.78    ( ! [X0,X3,X1] : (r2_hidden(X3,sK12(X0,X1)) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 34.88/4.78    inference(cnf_transformation,[],[f58])).
% 34.88/4.78  fof(f67,plain,(
% 34.88/4.78    r2_hidden(sK0,k3_relat_1(sK2))),
% 34.88/4.78    inference(cnf_transformation,[],[f33])).
% 34.88/4.78  fof(f26178,plain,(
% 34.88/4.78    ~r2_hidden(k4_tarski(sK0,sK0),sK2)),
% 34.88/4.78    inference(forward_demodulation,[],[f26177,f23803])).
% 34.88/4.78  fof(f23803,plain,(
% 34.88/4.78    sK0 = sK1),
% 34.88/4.78    inference(subsumption_resolution,[],[f23802,f811])).
% 34.88/4.78  fof(f811,plain,(
% 34.88/4.78    r2_hidden(k4_tarski(sK0,sK1),sK2) | sK0 = sK1),
% 34.88/4.78    inference(subsumption_resolution,[],[f810,f65])).
% 34.88/4.78  fof(f810,plain,(
% 34.88/4.78    sK0 = sK1 | r2_hidden(k4_tarski(sK0,sK1),sK2) | ~v1_relat_1(sK2)),
% 34.88/4.78    inference(subsumption_resolution,[],[f809,f151])).
% 34.88/4.78  fof(f151,plain,(
% 34.88/4.78    v6_relat_2(sK2)),
% 34.88/4.78    inference(subsumption_resolution,[],[f135,f66])).
% 34.88/4.78  fof(f135,plain,(
% 34.88/4.78    v6_relat_2(sK2) | ~v2_wellord1(sK2)),
% 34.88/4.78    inference(resolution,[],[f65,f90])).
% 34.88/4.78  fof(f90,plain,(
% 34.88/4.78    ( ! [X0] : (v6_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 34.88/4.78    inference(cnf_transformation,[],[f49])).
% 34.88/4.78  fof(f49,plain,(
% 34.88/4.78    ! [X0] : (((v2_wellord1(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0)) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(flattening,[],[f48])).
% 34.88/4.78  fof(f48,plain,(
% 34.88/4.78    ! [X0] : (((v2_wellord1(X0) | (~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0))) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(nnf_transformation,[],[f23])).
% 34.88/4.78  fof(f23,plain,(
% 34.88/4.78    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(ennf_transformation,[],[f6])).
% 34.88/4.78  fof(f6,axiom,(
% 34.88/4.78    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 34.88/4.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).
% 34.88/4.78  fof(f809,plain,(
% 34.88/4.78    sK0 = sK1 | r2_hidden(k4_tarski(sK0,sK1),sK2) | ~v6_relat_2(sK2) | ~v1_relat_1(sK2)),
% 34.88/4.78    inference(subsumption_resolution,[],[f808,f68])).
% 34.88/4.78  fof(f68,plain,(
% 34.88/4.78    r2_hidden(sK1,k3_relat_1(sK2))),
% 34.88/4.78    inference(cnf_transformation,[],[f33])).
% 34.88/4.78  fof(f808,plain,(
% 34.88/4.78    sK0 = sK1 | r2_hidden(k4_tarski(sK0,sK1),sK2) | ~r2_hidden(sK1,k3_relat_1(sK2)) | ~v6_relat_2(sK2) | ~v1_relat_1(sK2)),
% 34.88/4.78    inference(subsumption_resolution,[],[f805,f67])).
% 34.88/4.78  fof(f805,plain,(
% 34.88/4.78    sK0 = sK1 | r2_hidden(k4_tarski(sK0,sK1),sK2) | ~r2_hidden(sK0,k3_relat_1(sK2)) | ~r2_hidden(sK1,k3_relat_1(sK2)) | ~v6_relat_2(sK2) | ~v1_relat_1(sK2)),
% 34.88/4.78    inference(duplicate_literal_removal,[],[f801])).
% 34.88/4.78  fof(f801,plain,(
% 34.88/4.78    sK0 = sK1 | r2_hidden(k4_tarski(sK0,sK1),sK2) | sK0 = sK1 | ~r2_hidden(sK0,k3_relat_1(sK2)) | ~r2_hidden(sK1,k3_relat_1(sK2)) | ~v6_relat_2(sK2) | ~v1_relat_1(sK2)),
% 34.88/4.78    inference(resolution,[],[f790,f77])).
% 34.88/4.78  fof(f77,plain,(
% 34.88/4.78    ( ! [X4,X0,X3] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~v6_relat_2(X0) | ~v1_relat_1(X0)) )),
% 34.88/4.78    inference(cnf_transformation,[],[f43])).
% 34.88/4.78  fof(f43,plain,(
% 34.88/4.78    ! [X0] : (((v6_relat_2(X0) | (~r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0) & ~r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) & sK6(X0) != sK7(X0) & r2_hidden(sK7(X0),k3_relat_1(X0)) & r2_hidden(sK6(X0),k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f41,f42])).
% 34.88/4.78  fof(f42,plain,(
% 34.88/4.78    ! [X0] : (? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0) & ~r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) & sK6(X0) != sK7(X0) & r2_hidden(sK7(X0),k3_relat_1(X0)) & r2_hidden(sK6(X0),k3_relat_1(X0))))),
% 34.88/4.78    introduced(choice_axiom,[])).
% 34.88/4.78  fof(f41,plain,(
% 34.88/4.78    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(rectify,[],[f40])).
% 34.88/4.78  fof(f40,plain,(
% 34.88/4.78    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(nnf_transformation,[],[f20])).
% 34.88/4.78  fof(f20,plain,(
% 34.88/4.78    ! [X0] : ((v6_relat_2(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(ennf_transformation,[],[f9])).
% 34.88/4.78  fof(f9,axiom,(
% 34.88/4.78    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> ! [X1,X2] : ~(~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))))),
% 34.88/4.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).
% 34.88/4.78  fof(f790,plain,(
% 34.88/4.78    ~r2_hidden(k4_tarski(sK1,sK0),sK2) | sK0 = sK1),
% 34.88/4.78    inference(subsumption_resolution,[],[f789,f144])).
% 34.88/4.78  fof(f144,plain,(
% 34.88/4.78    ( ! [X26,X27] : (~r2_hidden(k4_tarski(X26,X27),sK2) | r2_hidden(X26,k1_wellord1(sK2,X27)) | X26 = X27) )),
% 34.88/4.78    inference(resolution,[],[f65,f111])).
% 34.88/4.78  fof(f111,plain,(
% 34.88/4.78    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_wellord1(X0,X1)) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | ~v1_relat_1(X0)) )),
% 34.88/4.78    inference(equality_resolution,[],[f95])).
% 34.88/4.78  fof(f95,plain,(
% 34.88/4.78    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 34.88/4.78    inference(cnf_transformation,[],[f54])).
% 34.88/4.78  fof(f789,plain,(
% 34.88/4.78    ~r2_hidden(sK1,k1_wellord1(sK2,sK0)) | sK0 = sK1 | ~r2_hidden(k4_tarski(sK1,sK0),sK2)),
% 34.88/4.78    inference(subsumption_resolution,[],[f788,f65])).
% 34.88/4.78  fof(f788,plain,(
% 34.88/4.78    ~r2_hidden(sK1,k1_wellord1(sK2,sK0)) | sK0 = sK1 | ~r2_hidden(k4_tarski(sK1,sK0),sK2) | ~v1_relat_1(sK2)),
% 34.88/4.78    inference(subsumption_resolution,[],[f777,f150])).
% 34.88/4.78  fof(f150,plain,(
% 34.88/4.78    v4_relat_2(sK2)),
% 34.88/4.78    inference(subsumption_resolution,[],[f134,f66])).
% 34.88/4.78  fof(f134,plain,(
% 34.88/4.78    v4_relat_2(sK2) | ~v2_wellord1(sK2)),
% 34.88/4.78    inference(resolution,[],[f65,f89])).
% 34.88/4.78  fof(f89,plain,(
% 34.88/4.78    ( ! [X0] : (v4_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 34.88/4.78    inference(cnf_transformation,[],[f49])).
% 34.88/4.78  fof(f777,plain,(
% 34.88/4.78    ~r2_hidden(sK1,k1_wellord1(sK2,sK0)) | sK0 = sK1 | ~r2_hidden(k4_tarski(sK1,sK0),sK2) | ~v4_relat_2(sK2) | ~v1_relat_1(sK2)),
% 34.88/4.78    inference(resolution,[],[f515,f73])).
% 34.88/4.78  fof(f73,plain,(
% 34.88/4.78    ( ! [X4,X0,X3] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~v4_relat_2(X0) | ~v1_relat_1(X0)) )),
% 34.88/4.78    inference(cnf_transformation,[],[f39])).
% 34.88/4.78  fof(f39,plain,(
% 34.88/4.78    ! [X0] : (((v4_relat_2(X0) | (sK4(X0) != sK5(X0) & r2_hidden(k4_tarski(sK5(X0),sK4(X0)),X0) & r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f37,f38])).
% 34.88/4.78  fof(f38,plain,(
% 34.88/4.78    ! [X0] : (? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (sK4(X0) != sK5(X0) & r2_hidden(k4_tarski(sK5(X0),sK4(X0)),X0) & r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)))),
% 34.88/4.78    introduced(choice_axiom,[])).
% 34.88/4.78  fof(f37,plain,(
% 34.88/4.78    ! [X0] : (((v4_relat_2(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(rectify,[],[f36])).
% 34.88/4.78  fof(f36,plain,(
% 34.88/4.78    ! [X0] : (((v4_relat_2(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(nnf_transformation,[],[f19])).
% 34.88/4.78  fof(f19,plain,(
% 34.88/4.78    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(flattening,[],[f18])).
% 34.88/4.78  fof(f18,plain,(
% 34.88/4.78    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | (~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(ennf_transformation,[],[f8])).
% 34.88/4.78  fof(f8,axiom,(
% 34.88/4.78    ! [X0] : (v1_relat_1(X0) => (v4_relat_2(X0) <=> ! [X1,X2] : ((r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => X1 = X2)))),
% 34.88/4.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_wellord1)).
% 34.88/4.78  fof(f515,plain,(
% 34.88/4.78    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~r2_hidden(sK1,k1_wellord1(sK2,sK0))),
% 34.88/4.78    inference(resolution,[],[f69,f186])).
% 34.88/4.78  fof(f186,plain,(
% 34.88/4.78    ( ! [X2,X1] : (~r1_tarski(X2,k1_wellord1(sK2,X1)) | ~r2_hidden(X1,X2)) )),
% 34.88/4.78    inference(resolution,[],[f146,f105])).
% 34.88/4.78  fof(f105,plain,(
% 34.88/4.78    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 34.88/4.78    inference(cnf_transformation,[],[f64])).
% 34.88/4.78  fof(f146,plain,(
% 34.88/4.78    ( ! [X30] : (~r2_hidden(X30,k1_wellord1(sK2,X30))) )),
% 34.88/4.78    inference(resolution,[],[f65,f114])).
% 34.88/4.78  fof(f114,plain,(
% 34.88/4.78    ( ! [X4,X0] : (~r2_hidden(X4,k1_wellord1(X0,X4)) | ~v1_relat_1(X0)) )),
% 34.88/4.78    inference(equality_resolution,[],[f113])).
% 34.88/4.78  fof(f113,plain,(
% 34.88/4.78    ( ! [X4,X2,X0] : (~r2_hidden(X4,X2) | k1_wellord1(X0,X4) != X2 | ~v1_relat_1(X0)) )),
% 34.88/4.78    inference(equality_resolution,[],[f93])).
% 34.88/4.78  fof(f93,plain,(
% 34.88/4.78    ( ! [X4,X2,X0,X1] : (X1 != X4 | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 34.88/4.78    inference(cnf_transformation,[],[f54])).
% 34.88/4.78  fof(f69,plain,(
% 34.88/4.78    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 34.88/4.78    inference(cnf_transformation,[],[f33])).
% 34.88/4.78  fof(f23802,plain,(
% 34.88/4.78    ~r2_hidden(k4_tarski(sK0,sK1),sK2) | sK0 = sK1),
% 34.88/4.78    inference(subsumption_resolution,[],[f23774,f509])).
% 34.88/4.78  fof(f509,plain,(
% 34.88/4.78    ( ! [X6,X7] : (~r2_hidden(k4_tarski(X7,X6),sK2) | X6 = X7 | ~r2_hidden(X6,k1_wellord1(sK2,X7))) )),
% 34.88/4.78    inference(subsumption_resolution,[],[f508,f65])).
% 34.88/4.78  fof(f508,plain,(
% 34.88/4.78    ( ! [X6,X7] : (~r2_hidden(X6,k1_wellord1(sK2,X7)) | X6 = X7 | ~r2_hidden(k4_tarski(X7,X6),sK2) | ~v1_relat_1(sK2)) )),
% 34.88/4.78    inference(subsumption_resolution,[],[f493,f150])).
% 34.88/4.78  fof(f493,plain,(
% 34.88/4.78    ( ! [X6,X7] : (~r2_hidden(X6,k1_wellord1(sK2,X7)) | X6 = X7 | ~r2_hidden(k4_tarski(X7,X6),sK2) | ~v4_relat_2(sK2) | ~v1_relat_1(sK2)) )),
% 34.88/4.78    inference(resolution,[],[f145,f73])).
% 34.88/4.78  fof(f145,plain,(
% 34.88/4.78    ( ! [X28,X29] : (r2_hidden(k4_tarski(X28,X29),sK2) | ~r2_hidden(X28,k1_wellord1(sK2,X29))) )),
% 34.88/4.78    inference(resolution,[],[f65,f112])).
% 34.88/4.78  fof(f23774,plain,(
% 34.88/4.78    r2_hidden(sK1,k1_wellord1(sK2,sK0)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2) | sK0 = sK1),
% 34.88/4.78    inference(superposition,[],[f912,f23743])).
% 34.88/4.78  fof(f23743,plain,(
% 34.88/4.78    sK1 = sK13(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | sK0 = sK1),
% 34.88/4.78    inference(resolution,[],[f8200,f811])).
% 34.88/4.78  fof(f8200,plain,(
% 34.88/4.78    ~r2_hidden(k4_tarski(sK0,sK1),sK2) | sK1 = sK13(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 34.88/4.78    inference(subsumption_resolution,[],[f8178,f912])).
% 34.88/4.78  fof(f8178,plain,(
% 34.88/4.78    ~r2_hidden(sK13(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)) | sK1 = sK13(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 34.88/4.78    inference(resolution,[],[f3775,f913])).
% 34.88/4.78  fof(f913,plain,(
% 34.88/4.78    ~r2_hidden(sK13(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 34.88/4.78    inference(resolution,[],[f70,f107])).
% 34.88/4.78  fof(f70,plain,(
% 34.88/4.78    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 34.88/4.78    inference(cnf_transformation,[],[f33])).
% 34.88/4.78  fof(f3775,plain,(
% 34.88/4.78    ( ! [X0] : (r2_hidden(X0,k1_wellord1(sK2,sK1)) | ~r2_hidden(X0,k1_wellord1(sK2,sK0)) | sK1 = X0) )),
% 34.88/4.78    inference(resolution,[],[f3771,f144])).
% 34.88/4.78  fof(f3771,plain,(
% 34.88/4.78    ( ! [X3] : (r2_hidden(k4_tarski(X3,sK1),sK2) | ~r2_hidden(X3,k1_wellord1(sK2,sK0))) )),
% 34.88/4.78    inference(subsumption_resolution,[],[f3770,f513])).
% 34.88/4.78  fof(f513,plain,(
% 34.88/4.78    ( ! [X14,X15,X13] : (~r2_hidden(X13,k1_wellord1(sK2,X14)) | r2_hidden(k4_tarski(X13,X15),sK2) | ~r2_hidden(k4_tarski(X14,X15),sK2)) )),
% 34.88/4.78    inference(subsumption_resolution,[],[f512,f65])).
% 34.88/4.78  fof(f512,plain,(
% 34.88/4.78    ( ! [X14,X15,X13] : (~r2_hidden(X13,k1_wellord1(sK2,X14)) | r2_hidden(k4_tarski(X13,X15),sK2) | ~r2_hidden(k4_tarski(X14,X15),sK2) | ~v1_relat_1(sK2)) )),
% 34.88/4.78    inference(subsumption_resolution,[],[f496,f149])).
% 34.88/4.78  fof(f149,plain,(
% 34.88/4.78    v8_relat_2(sK2)),
% 34.88/4.78    inference(subsumption_resolution,[],[f133,f66])).
% 34.88/4.78  fof(f133,plain,(
% 34.88/4.78    v8_relat_2(sK2) | ~v2_wellord1(sK2)),
% 34.88/4.78    inference(resolution,[],[f65,f88])).
% 34.88/4.78  fof(f88,plain,(
% 34.88/4.78    ( ! [X0] : (v8_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 34.88/4.78    inference(cnf_transformation,[],[f49])).
% 34.88/4.78  fof(f496,plain,(
% 34.88/4.78    ( ! [X14,X15,X13] : (~r2_hidden(X13,k1_wellord1(sK2,X14)) | r2_hidden(k4_tarski(X13,X15),sK2) | ~r2_hidden(k4_tarski(X14,X15),sK2) | ~v8_relat_2(sK2) | ~v1_relat_1(sK2)) )),
% 34.88/4.78    inference(resolution,[],[f145,f83])).
% 34.88/4.78  fof(f83,plain,(
% 34.88/4.78    ( ! [X6,X4,X0,X5] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~v8_relat_2(X0) | ~v1_relat_1(X0)) )),
% 34.88/4.78    inference(cnf_transformation,[],[f47])).
% 34.88/4.78  fof(f47,plain,(
% 34.88/4.78    ! [X0] : (((v8_relat_2(X0) | (~r2_hidden(k4_tarski(sK8(X0),sK10(X0)),X0) & r2_hidden(k4_tarski(sK9(X0),sK10(X0)),X0) & r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0))) & (! [X4,X5,X6] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f45,f46])).
% 34.88/4.78  fof(f46,plain,(
% 34.88/4.78    ! [X0] : (? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (~r2_hidden(k4_tarski(sK8(X0),sK10(X0)),X0) & r2_hidden(k4_tarski(sK9(X0),sK10(X0)),X0) & r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0)))),
% 34.88/4.78    introduced(choice_axiom,[])).
% 34.88/4.78  fof(f45,plain,(
% 34.88/4.78    ! [X0] : (((v8_relat_2(X0) | ? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X4,X5,X6] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(rectify,[],[f44])).
% 34.88/4.78  fof(f44,plain,(
% 34.88/4.78    ! [X0] : (((v8_relat_2(X0) | ? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(nnf_transformation,[],[f22])).
% 34.88/4.78  fof(f22,plain,(
% 34.88/4.78    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(flattening,[],[f21])).
% 34.88/4.78  fof(f21,plain,(
% 34.88/4.78    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | (~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 34.88/4.78    inference(ennf_transformation,[],[f7])).
% 34.88/4.78  fof(f7,axiom,(
% 34.88/4.78    ! [X0] : (v1_relat_1(X0) => (v8_relat_2(X0) <=> ! [X1,X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => r2_hidden(k4_tarski(X1,X3),X0))))),
% 34.88/4.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l2_wellord1)).
% 34.88/4.78  fof(f3770,plain,(
% 34.88/4.78    ( ! [X3] : (r2_hidden(k4_tarski(sK0,sK1),sK2) | ~r2_hidden(X3,k1_wellord1(sK2,sK0)) | r2_hidden(k4_tarski(X3,sK1),sK2)) )),
% 34.88/4.78    inference(subsumption_resolution,[],[f3717,f65])).
% 34.88/4.78  fof(f3717,plain,(
% 34.88/4.78    ( ! [X3] : (r2_hidden(k4_tarski(sK0,sK1),sK2) | ~r2_hidden(X3,k1_wellord1(sK2,sK0)) | r2_hidden(k4_tarski(X3,sK1),sK2) | ~v1_relat_1(sK2)) )),
% 34.88/4.78    inference(resolution,[],[f517,f112])).
% 34.88/4.78  fof(f517,plain,(
% 34.88/4.78    ( ! [X0] : (r2_hidden(k4_tarski(sK0,sK1),sK2) | r2_hidden(X0,k1_wellord1(sK2,sK1)) | ~r2_hidden(X0,k1_wellord1(sK2,sK0))) )),
% 34.88/4.78    inference(resolution,[],[f69,f105])).
% 34.88/4.78  fof(f912,plain,(
% 34.88/4.78    r2_hidden(sK13(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 34.88/4.78    inference(resolution,[],[f70,f106])).
% 34.88/4.78  fof(f26177,plain,(
% 34.88/4.78    ~r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 34.88/4.78    inference(subsumption_resolution,[],[f23806,f116])).
% 34.88/4.78  fof(f23806,plain,(
% 34.88/4.78    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 34.88/4.78    inference(backward_demodulation,[],[f70,f23803])).
% 34.88/4.78  % SZS output end Proof for theBenchmark
% 34.88/4.78  % (22197)------------------------------
% 34.88/4.78  % (22197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 34.88/4.78  % (22197)Termination reason: Refutation
% 34.88/4.78  
% 34.88/4.78  % (22197)Memory used [KB]: 14583
% 34.88/4.78  % (22197)Time elapsed: 4.329 s
% 34.88/4.78  % (22197)------------------------------
% 34.88/4.78  % (22197)------------------------------
% 34.88/4.78  % (22171)Success in time 4.428 s
%------------------------------------------------------------------------------
