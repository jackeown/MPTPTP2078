%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:05 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   86 (1509 expanded)
%              Number of leaves         :   12 ( 451 expanded)
%              Depth                    :   27
%              Number of atoms          :  320 (7700 expanded)
%              Number of equality atoms :   99 (2671 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f340,plain,(
    $false ),
    inference(resolution,[],[f329,f41])).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f329,plain,(
    ! [X1] : ~ r1_tarski(X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f328,f191])).

fof(f191,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f152,f41])).

fof(f152,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK0)
      | sK0 = X2 ) ),
    inference(resolution,[],[f150,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f150,plain,(
    ! [X4] : r1_tarski(sK0,X4) ),
    inference(resolution,[],[f131,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f131,plain,(
    ! [X1] : ~ r2_hidden(X1,sK0) ),
    inference(backward_demodulation,[],[f61,f129])).

fof(f129,plain,(
    ! [X1] : sK6(k2_relat_1(sK5(sK1,X1)),sK0) = X1 ),
    inference(backward_demodulation,[],[f99,f124])).

fof(f124,plain,(
    ! [X2,X3] : k1_funct_1(sK5(sK1,X2),sK4(sK5(sK1,X3),sK6(k2_relat_1(sK5(sK1,X3)),sK0))) = X2 ),
    inference(resolution,[],[f97,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK5(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK5(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK5(X0,X1)) = X0
      & v1_funct_1(sK5(X0,X1))
      & v1_relat_1(sK5(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK5(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK5(X0,X1)) = X0
        & v1_funct_1(sK5(X0,X1))
        & v1_relat_1(sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f97,plain,(
    ! [X0] : r2_hidden(sK4(sK5(sK1,X0),sK6(k2_relat_1(sK5(sK1,X0)),sK0)),sK1) ),
    inference(forward_demodulation,[],[f96,f44])).

fof(f44,plain,(
    ! [X0,X1] : k1_relat_1(sK5(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f96,plain,(
    ! [X0] : r2_hidden(sK4(sK5(sK1,X0),sK6(k2_relat_1(sK5(sK1,X0)),sK0)),k1_relat_1(sK5(sK1,X0))) ),
    inference(subsumption_resolution,[],[f95,f42])).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f95,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK5(sK1,X0),sK6(k2_relat_1(sK5(sK1,X0)),sK0)),k1_relat_1(sK5(sK1,X0)))
      | ~ v1_relat_1(sK5(sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f87,f43])).

fof(f43,plain,(
    ! [X0,X1] : v1_funct_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f87,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK5(sK1,X0),sK6(k2_relat_1(sK5(sK1,X0)),sK0)),k1_relat_1(sK5(sK1,X0)))
      | ~ v1_funct_1(sK5(sK1,X0))
      | ~ v1_relat_1(sK5(sK1,X0)) ) ),
    inference(resolution,[],[f60,f54])).

fof(f54,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK2(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ( sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
                  & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X5)) = X5
                    & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f22,f21,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK2(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK2(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK2(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f60,plain,(
    ! [X0] : r2_hidden(sK6(k2_relat_1(sK5(sK1,X0)),sK0),k2_relat_1(sK5(sK1,X0))) ),
    inference(resolution,[],[f59,f47])).

fof(f59,plain,(
    ! [X0] : ~ r1_tarski(k2_relat_1(sK5(sK1,X0)),sK0) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r1_tarski(k2_relat_1(sK5(X0,X1)),sK0) ) ),
    inference(subsumption_resolution,[],[f56,f42])).

fof(f56,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r1_tarski(k2_relat_1(sK5(X0,X1)),sK0)
      | ~ v1_relat_1(sK5(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f55,f43])).

fof(f55,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r1_tarski(k2_relat_1(sK5(X0,X1)),sK0)
      | ~ v1_funct_1(sK5(X0,X1))
      | ~ v1_relat_1(sK5(X0,X1)) ) ),
    inference(superposition,[],[f31,f44])).

fof(f31,plain,(
    ! [X2] :
      ( k1_relat_1(X2) != sK1
      | ~ r1_tarski(k2_relat_1(X2),sK0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK0)
        | k1_relat_1(X2) != sK1
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK0)
          | k1_relat_1(X2) != sK1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK0 ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f99,plain,(
    ! [X1] : sK6(k2_relat_1(sK5(sK1,X1)),sK0) = k1_funct_1(sK5(sK1,X1),sK4(sK5(sK1,X1),sK6(k2_relat_1(sK5(sK1,X1)),sK0))) ),
    inference(subsumption_resolution,[],[f98,f42])).

fof(f98,plain,(
    ! [X1] :
      ( sK6(k2_relat_1(sK5(sK1,X1)),sK0) = k1_funct_1(sK5(sK1,X1),sK4(sK5(sK1,X1),sK6(k2_relat_1(sK5(sK1,X1)),sK0)))
      | ~ v1_relat_1(sK5(sK1,X1)) ) ),
    inference(subsumption_resolution,[],[f88,f43])).

fof(f88,plain,(
    ! [X1] :
      ( sK6(k2_relat_1(sK5(sK1,X1)),sK0) = k1_funct_1(sK5(sK1,X1),sK4(sK5(sK1,X1),sK6(k2_relat_1(sK5(sK1,X1)),sK0)))
      | ~ v1_funct_1(sK5(sK1,X1))
      | ~ v1_relat_1(sK5(sK1,X1)) ) ),
    inference(resolution,[],[f60,f53])).

fof(f53,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X1] : ~ r2_hidden(sK6(k2_relat_1(sK5(sK1,X1)),sK0),sK0) ),
    inference(resolution,[],[f59,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f328,plain,(
    ! [X1] : ~ r1_tarski(X1,sK0) ),
    inference(subsumption_resolution,[],[f239,f308])).

fof(f308,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f275,f304])).

fof(f304,plain,(
    ! [X1] : sK6(k2_relat_1(sK5(k1_xboole_0,X1)),k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f217,f247])).

fof(f247,plain,(
    k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f195])).

fof(f195,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f30,f191])).

fof(f30,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f217,plain,(
    ! [X1] : sK6(k2_relat_1(sK5(sK1,X1)),k1_xboole_0) = X1 ),
    inference(backward_demodulation,[],[f129,f191])).

fof(f275,plain,(
    ! [X0] : ~ r2_hidden(sK6(k2_relat_1(sK5(k1_xboole_0,X0)),k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f244,f191])).

fof(f244,plain,(
    ! [X0] : ~ r2_hidden(sK6(k2_relat_1(sK5(k1_xboole_0,X0)),sK0),sK0) ),
    inference(trivial_inequality_removal,[],[f204])).

fof(f204,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(sK6(k2_relat_1(sK5(k1_xboole_0,X0)),sK0),sK0) ) ),
    inference(backward_demodulation,[],[f75,f191])).

fof(f75,plain,(
    ! [X0] :
      ( k1_xboole_0 != sK0
      | ~ r2_hidden(sK6(k2_relat_1(sK5(k1_xboole_0,X0)),sK0),sK0) ) ),
    inference(superposition,[],[f61,f30])).

fof(f239,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK5(k1_xboole_0,X0),X1),k1_xboole_0)
      | ~ r1_tarski(X1,sK0) ) ),
    inference(trivial_inequality_removal,[],[f231])).

fof(f231,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r2_hidden(sK3(sK5(k1_xboole_0,X0),X1),k1_xboole_0)
      | ~ r1_tarski(X1,sK0) ) ),
    inference(backward_demodulation,[],[f178,f191])).

fof(f178,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK5(k1_xboole_0,X0),X1),k1_xboole_0)
      | ~ r1_tarski(X1,sK0)
      | k1_xboole_0 != sK0 ) ),
    inference(subsumption_resolution,[],[f175,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,sK0) ) ),
    inference(backward_demodulation,[],[f74,f129])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(k2_relat_1(sK5(sK1,X0)),sK0),X1)
      | ~ r1_tarski(X1,sK0) ) ),
    inference(resolution,[],[f61,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f175,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK5(k1_xboole_0,X0),X1),k1_xboole_0)
      | ~ r1_tarski(X1,sK0)
      | r2_hidden(sK2(sK5(k1_xboole_0,X0),X1),X1)
      | k1_xboole_0 != sK0 ) ),
    inference(superposition,[],[f68,f30])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK5(sK1,X0),X1),sK1)
      | ~ r1_tarski(X1,sK0)
      | r2_hidden(sK2(sK5(sK1,X0),X1),X1) ) ),
    inference(forward_demodulation,[],[f67,f44])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK0)
      | r2_hidden(sK3(sK5(sK1,X0),X1),k1_relat_1(sK5(sK1,X0)))
      | r2_hidden(sK2(sK5(sK1,X0),X1),X1) ) ),
    inference(subsumption_resolution,[],[f66,f42])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK0)
      | r2_hidden(sK3(sK5(sK1,X0),X1),k1_relat_1(sK5(sK1,X0)))
      | r2_hidden(sK2(sK5(sK1,X0),X1),X1)
      | ~ v1_relat_1(sK5(sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f63,f43])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK0)
      | r2_hidden(sK3(sK5(sK1,X0),X1),k1_relat_1(sK5(sK1,X0)))
      | r2_hidden(sK2(sK5(sK1,X0),X1),X1)
      | ~ v1_funct_1(sK5(sK1,X0))
      | ~ v1_relat_1(sK5(sK1,X0)) ) ),
    inference(superposition,[],[f59,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK2(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:26:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.20/0.53  % (21620)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.20/0.53  % (21614)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.20/0.54  % (21614)Refutation not found, incomplete strategy% (21614)------------------------------
% 1.20/0.54  % (21614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.54  % (21614)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.54  
% 1.20/0.54  % (21614)Memory used [KB]: 10618
% 1.20/0.54  % (21614)Time elapsed: 0.110 s
% 1.20/0.54  % (21614)------------------------------
% 1.20/0.54  % (21614)------------------------------
% 1.20/0.54  % (21604)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.20/0.54  % (21610)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.20/0.54  % (21627)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.20/0.54  % (21609)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.20/0.54  % (21619)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.20/0.54  % (21606)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.20/0.54  % (21612)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.54  % (21632)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.54  % (21606)Refutation not found, incomplete strategy% (21606)------------------------------
% 1.41/0.54  % (21606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (21606)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (21606)Memory used [KB]: 10618
% 1.41/0.54  % (21606)Time elapsed: 0.123 s
% 1.41/0.54  % (21606)------------------------------
% 1.41/0.54  % (21606)------------------------------
% 1.41/0.54  % (21611)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.55  % (21629)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.55  % (21631)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.55  % (21604)Refutation found. Thanks to Tanya!
% 1.41/0.55  % SZS status Theorem for theBenchmark
% 1.41/0.55  % SZS output start Proof for theBenchmark
% 1.41/0.55  fof(f340,plain,(
% 1.41/0.55    $false),
% 1.41/0.55    inference(resolution,[],[f329,f41])).
% 1.41/0.55  fof(f41,plain,(
% 1.41/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f3])).
% 1.41/0.55  fof(f3,axiom,(
% 1.41/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.41/0.55  fof(f329,plain,(
% 1.41/0.55    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0)) )),
% 1.41/0.55    inference(forward_demodulation,[],[f328,f191])).
% 1.41/0.55  fof(f191,plain,(
% 1.41/0.55    k1_xboole_0 = sK0),
% 1.41/0.55    inference(resolution,[],[f152,f41])).
% 1.41/0.55  fof(f152,plain,(
% 1.41/0.55    ( ! [X2] : (~r1_tarski(X2,sK0) | sK0 = X2) )),
% 1.41/0.55    inference(resolution,[],[f150,f34])).
% 1.41/0.55  fof(f34,plain,(
% 1.41/0.55    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f17])).
% 1.41/0.55  fof(f17,plain,(
% 1.41/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.41/0.55    inference(flattening,[],[f16])).
% 1.41/0.55  fof(f16,plain,(
% 1.41/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.41/0.55    inference(nnf_transformation,[],[f2])).
% 1.41/0.55  fof(f2,axiom,(
% 1.41/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.41/0.55  fof(f150,plain,(
% 1.41/0.55    ( ! [X4] : (r1_tarski(sK0,X4)) )),
% 1.41/0.55    inference(resolution,[],[f131,f47])).
% 1.41/0.55  fof(f47,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK6(X0,X1),X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f29])).
% 1.41/0.55  fof(f29,plain,(
% 1.41/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.41/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f27,f28])).
% 1.41/0.55  fof(f28,plain,(
% 1.41/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f27,plain,(
% 1.41/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.41/0.55    inference(rectify,[],[f26])).
% 1.41/0.55  fof(f26,plain,(
% 1.41/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.41/0.55    inference(nnf_transformation,[],[f13])).
% 1.41/0.55  fof(f13,plain,(
% 1.41/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.41/0.55    inference(ennf_transformation,[],[f1])).
% 1.41/0.55  fof(f1,axiom,(
% 1.41/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.41/0.55  fof(f131,plain,(
% 1.41/0.55    ( ! [X1] : (~r2_hidden(X1,sK0)) )),
% 1.41/0.55    inference(backward_demodulation,[],[f61,f129])).
% 1.41/0.55  fof(f129,plain,(
% 1.41/0.55    ( ! [X1] : (sK6(k2_relat_1(sK5(sK1,X1)),sK0) = X1) )),
% 1.41/0.55    inference(backward_demodulation,[],[f99,f124])).
% 1.41/0.55  fof(f124,plain,(
% 1.41/0.55    ( ! [X2,X3] : (k1_funct_1(sK5(sK1,X2),sK4(sK5(sK1,X3),sK6(k2_relat_1(sK5(sK1,X3)),sK0))) = X2) )),
% 1.41/0.55    inference(resolution,[],[f97,f45])).
% 1.41/0.55  fof(f45,plain,(
% 1.41/0.55    ( ! [X0,X3,X1] : (k1_funct_1(sK5(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f25])).
% 1.41/0.55  fof(f25,plain,(
% 1.41/0.55    ! [X0,X1] : (! [X3] : (k1_funct_1(sK5(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK5(X0,X1)) = X0 & v1_funct_1(sK5(X0,X1)) & v1_relat_1(sK5(X0,X1)))),
% 1.41/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f24])).
% 1.41/0.55  fof(f24,plain,(
% 1.41/0.55    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK5(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK5(X0,X1)) = X0 & v1_funct_1(sK5(X0,X1)) & v1_relat_1(sK5(X0,X1))))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f12,plain,(
% 1.41/0.55    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.41/0.55    inference(ennf_transformation,[],[f5])).
% 1.41/0.55  fof(f5,axiom,(
% 1.41/0.55    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 1.41/0.55  fof(f97,plain,(
% 1.41/0.55    ( ! [X0] : (r2_hidden(sK4(sK5(sK1,X0),sK6(k2_relat_1(sK5(sK1,X0)),sK0)),sK1)) )),
% 1.41/0.55    inference(forward_demodulation,[],[f96,f44])).
% 1.41/0.55  fof(f44,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k1_relat_1(sK5(X0,X1)) = X0) )),
% 1.41/0.55    inference(cnf_transformation,[],[f25])).
% 1.41/0.55  fof(f96,plain,(
% 1.41/0.55    ( ! [X0] : (r2_hidden(sK4(sK5(sK1,X0),sK6(k2_relat_1(sK5(sK1,X0)),sK0)),k1_relat_1(sK5(sK1,X0)))) )),
% 1.41/0.55    inference(subsumption_resolution,[],[f95,f42])).
% 1.41/0.55  fof(f42,plain,(
% 1.41/0.55    ( ! [X0,X1] : (v1_relat_1(sK5(X0,X1))) )),
% 1.41/0.55    inference(cnf_transformation,[],[f25])).
% 1.41/0.55  fof(f95,plain,(
% 1.41/0.55    ( ! [X0] : (r2_hidden(sK4(sK5(sK1,X0),sK6(k2_relat_1(sK5(sK1,X0)),sK0)),k1_relat_1(sK5(sK1,X0))) | ~v1_relat_1(sK5(sK1,X0))) )),
% 1.41/0.55    inference(subsumption_resolution,[],[f87,f43])).
% 1.41/0.55  fof(f43,plain,(
% 1.41/0.55    ( ! [X0,X1] : (v1_funct_1(sK5(X0,X1))) )),
% 1.41/0.55    inference(cnf_transformation,[],[f25])).
% 1.41/0.55  fof(f87,plain,(
% 1.41/0.55    ( ! [X0] : (r2_hidden(sK4(sK5(sK1,X0),sK6(k2_relat_1(sK5(sK1,X0)),sK0)),k1_relat_1(sK5(sK1,X0))) | ~v1_funct_1(sK5(sK1,X0)) | ~v1_relat_1(sK5(sK1,X0))) )),
% 1.41/0.55    inference(resolution,[],[f60,f54])).
% 1.41/0.55  fof(f54,plain,(
% 1.41/0.55    ( ! [X0,X5] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(equality_resolution,[],[f35])).
% 1.41/0.55  fof(f35,plain,(
% 1.41/0.55    ( ! [X0,X5,X1] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f23])).
% 1.41/0.55  fof(f23,plain,(
% 1.41/0.55    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f22,f21,f20])).
% 1.41/0.55  fof(f20,plain,(
% 1.41/0.55    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f21,plain,(
% 1.41/0.55    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f22,plain,(
% 1.41/0.55    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f19,plain,(
% 1.41/0.55    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.55    inference(rectify,[],[f18])).
% 1.41/0.55  fof(f18,plain,(
% 1.41/0.55    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.55    inference(nnf_transformation,[],[f11])).
% 1.41/0.55  fof(f11,plain,(
% 1.41/0.55    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.55    inference(flattening,[],[f10])).
% 1.41/0.55  fof(f10,plain,(
% 1.41/0.55    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.41/0.55    inference(ennf_transformation,[],[f4])).
% 1.41/0.55  fof(f4,axiom,(
% 1.41/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.41/0.55  fof(f60,plain,(
% 1.41/0.55    ( ! [X0] : (r2_hidden(sK6(k2_relat_1(sK5(sK1,X0)),sK0),k2_relat_1(sK5(sK1,X0)))) )),
% 1.41/0.55    inference(resolution,[],[f59,f47])).
% 1.41/0.55  fof(f59,plain,(
% 1.41/0.55    ( ! [X0] : (~r1_tarski(k2_relat_1(sK5(sK1,X0)),sK0)) )),
% 1.41/0.55    inference(equality_resolution,[],[f57])).
% 1.41/0.55  fof(f57,plain,(
% 1.41/0.55    ( ! [X0,X1] : (sK1 != X0 | ~r1_tarski(k2_relat_1(sK5(X0,X1)),sK0)) )),
% 1.41/0.55    inference(subsumption_resolution,[],[f56,f42])).
% 1.41/0.55  fof(f56,plain,(
% 1.41/0.55    ( ! [X0,X1] : (sK1 != X0 | ~r1_tarski(k2_relat_1(sK5(X0,X1)),sK0) | ~v1_relat_1(sK5(X0,X1))) )),
% 1.41/0.55    inference(subsumption_resolution,[],[f55,f43])).
% 1.41/0.55  fof(f55,plain,(
% 1.41/0.55    ( ! [X0,X1] : (sK1 != X0 | ~r1_tarski(k2_relat_1(sK5(X0,X1)),sK0) | ~v1_funct_1(sK5(X0,X1)) | ~v1_relat_1(sK5(X0,X1))) )),
% 1.41/0.55    inference(superposition,[],[f31,f44])).
% 1.41/0.55  fof(f31,plain,(
% 1.41/0.55    ( ! [X2] : (k1_relat_1(X2) != sK1 | ~r1_tarski(k2_relat_1(X2),sK0) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f15])).
% 1.41/0.55  fof(f15,plain,(
% 1.41/0.55    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0)),
% 1.41/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f14])).
% 1.41/0.55  fof(f14,plain,(
% 1.41/0.55    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f9,plain,(
% 1.41/0.55    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.41/0.55    inference(flattening,[],[f8])).
% 1.41/0.55  fof(f8,plain,(
% 1.41/0.55    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.41/0.55    inference(ennf_transformation,[],[f7])).
% 1.41/0.55  fof(f7,negated_conjecture,(
% 1.41/0.55    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.41/0.55    inference(negated_conjecture,[],[f6])).
% 1.41/0.55  fof(f6,conjecture,(
% 1.41/0.55    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).
% 1.41/0.55  fof(f99,plain,(
% 1.41/0.55    ( ! [X1] : (sK6(k2_relat_1(sK5(sK1,X1)),sK0) = k1_funct_1(sK5(sK1,X1),sK4(sK5(sK1,X1),sK6(k2_relat_1(sK5(sK1,X1)),sK0)))) )),
% 1.41/0.55    inference(subsumption_resolution,[],[f98,f42])).
% 1.41/0.55  fof(f98,plain,(
% 1.41/0.55    ( ! [X1] : (sK6(k2_relat_1(sK5(sK1,X1)),sK0) = k1_funct_1(sK5(sK1,X1),sK4(sK5(sK1,X1),sK6(k2_relat_1(sK5(sK1,X1)),sK0))) | ~v1_relat_1(sK5(sK1,X1))) )),
% 1.41/0.55    inference(subsumption_resolution,[],[f88,f43])).
% 1.41/0.55  fof(f88,plain,(
% 1.41/0.55    ( ! [X1] : (sK6(k2_relat_1(sK5(sK1,X1)),sK0) = k1_funct_1(sK5(sK1,X1),sK4(sK5(sK1,X1),sK6(k2_relat_1(sK5(sK1,X1)),sK0))) | ~v1_funct_1(sK5(sK1,X1)) | ~v1_relat_1(sK5(sK1,X1))) )),
% 1.41/0.55    inference(resolution,[],[f60,f53])).
% 1.41/0.55  fof(f53,plain,(
% 1.41/0.55    ( ! [X0,X5] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(equality_resolution,[],[f36])).
% 1.41/0.55  fof(f36,plain,(
% 1.41/0.55    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f23])).
% 1.41/0.55  fof(f61,plain,(
% 1.41/0.55    ( ! [X1] : (~r2_hidden(sK6(k2_relat_1(sK5(sK1,X1)),sK0),sK0)) )),
% 1.41/0.55    inference(resolution,[],[f59,f48])).
% 1.41/0.55  fof(f48,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK6(X0,X1),X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f29])).
% 1.41/0.55  fof(f328,plain,(
% 1.41/0.55    ( ! [X1] : (~r1_tarski(X1,sK0)) )),
% 1.41/0.55    inference(subsumption_resolution,[],[f239,f308])).
% 1.41/0.55  fof(f308,plain,(
% 1.41/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.41/0.55    inference(backward_demodulation,[],[f275,f304])).
% 1.41/0.55  fof(f304,plain,(
% 1.41/0.55    ( ! [X1] : (sK6(k2_relat_1(sK5(k1_xboole_0,X1)),k1_xboole_0) = X1) )),
% 1.41/0.55    inference(forward_demodulation,[],[f217,f247])).
% 1.41/0.55  fof(f247,plain,(
% 1.41/0.55    k1_xboole_0 = sK1),
% 1.41/0.55    inference(trivial_inequality_removal,[],[f195])).
% 1.41/0.55  fof(f195,plain,(
% 1.41/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1),
% 1.41/0.55    inference(backward_demodulation,[],[f30,f191])).
% 1.41/0.55  fof(f30,plain,(
% 1.41/0.55    k1_xboole_0 = sK1 | k1_xboole_0 != sK0),
% 1.41/0.55    inference(cnf_transformation,[],[f15])).
% 1.41/0.55  fof(f217,plain,(
% 1.41/0.55    ( ! [X1] : (sK6(k2_relat_1(sK5(sK1,X1)),k1_xboole_0) = X1) )),
% 1.41/0.55    inference(backward_demodulation,[],[f129,f191])).
% 1.41/0.55  fof(f275,plain,(
% 1.41/0.55    ( ! [X0] : (~r2_hidden(sK6(k2_relat_1(sK5(k1_xboole_0,X0)),k1_xboole_0),k1_xboole_0)) )),
% 1.41/0.55    inference(forward_demodulation,[],[f244,f191])).
% 1.41/0.55  fof(f244,plain,(
% 1.41/0.55    ( ! [X0] : (~r2_hidden(sK6(k2_relat_1(sK5(k1_xboole_0,X0)),sK0),sK0)) )),
% 1.41/0.55    inference(trivial_inequality_removal,[],[f204])).
% 1.41/0.55  fof(f204,plain,(
% 1.41/0.55    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK6(k2_relat_1(sK5(k1_xboole_0,X0)),sK0),sK0)) )),
% 1.41/0.55    inference(backward_demodulation,[],[f75,f191])).
% 1.41/0.55  fof(f75,plain,(
% 1.41/0.55    ( ! [X0] : (k1_xboole_0 != sK0 | ~r2_hidden(sK6(k2_relat_1(sK5(k1_xboole_0,X0)),sK0),sK0)) )),
% 1.41/0.55    inference(superposition,[],[f61,f30])).
% 1.41/0.55  fof(f239,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r2_hidden(sK3(sK5(k1_xboole_0,X0),X1),k1_xboole_0) | ~r1_tarski(X1,sK0)) )),
% 1.41/0.55    inference(trivial_inequality_removal,[],[f231])).
% 1.41/0.55  fof(f231,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | r2_hidden(sK3(sK5(k1_xboole_0,X0),X1),k1_xboole_0) | ~r1_tarski(X1,sK0)) )),
% 1.41/0.55    inference(backward_demodulation,[],[f178,f191])).
% 1.41/0.55  fof(f178,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r2_hidden(sK3(sK5(k1_xboole_0,X0),X1),k1_xboole_0) | ~r1_tarski(X1,sK0) | k1_xboole_0 != sK0) )),
% 1.41/0.55    inference(subsumption_resolution,[],[f175,f132])).
% 1.41/0.55  fof(f132,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,sK0)) )),
% 1.41/0.55    inference(backward_demodulation,[],[f74,f129])).
% 1.41/0.55  fof(f74,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~r2_hidden(sK6(k2_relat_1(sK5(sK1,X0)),sK0),X1) | ~r1_tarski(X1,sK0)) )),
% 1.41/0.55    inference(resolution,[],[f61,f46])).
% 1.41/0.55  fof(f46,plain,(
% 1.41/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f29])).
% 1.41/0.55  fof(f175,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r2_hidden(sK3(sK5(k1_xboole_0,X0),X1),k1_xboole_0) | ~r1_tarski(X1,sK0) | r2_hidden(sK2(sK5(k1_xboole_0,X0),X1),X1) | k1_xboole_0 != sK0) )),
% 1.41/0.55    inference(superposition,[],[f68,f30])).
% 1.41/0.55  fof(f68,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r2_hidden(sK3(sK5(sK1,X0),X1),sK1) | ~r1_tarski(X1,sK0) | r2_hidden(sK2(sK5(sK1,X0),X1),X1)) )),
% 1.41/0.55    inference(forward_demodulation,[],[f67,f44])).
% 1.41/0.55  fof(f67,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~r1_tarski(X1,sK0) | r2_hidden(sK3(sK5(sK1,X0),X1),k1_relat_1(sK5(sK1,X0))) | r2_hidden(sK2(sK5(sK1,X0),X1),X1)) )),
% 1.41/0.55    inference(subsumption_resolution,[],[f66,f42])).
% 1.41/0.55  fof(f66,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~r1_tarski(X1,sK0) | r2_hidden(sK3(sK5(sK1,X0),X1),k1_relat_1(sK5(sK1,X0))) | r2_hidden(sK2(sK5(sK1,X0),X1),X1) | ~v1_relat_1(sK5(sK1,X0))) )),
% 1.41/0.55    inference(subsumption_resolution,[],[f63,f43])).
% 1.41/0.55  fof(f63,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~r1_tarski(X1,sK0) | r2_hidden(sK3(sK5(sK1,X0),X1),k1_relat_1(sK5(sK1,X0))) | r2_hidden(sK2(sK5(sK1,X0),X1),X1) | ~v1_funct_1(sK5(sK1,X0)) | ~v1_relat_1(sK5(sK1,X0))) )),
% 1.41/0.55    inference(superposition,[],[f59,f38])).
% 1.41/0.55  fof(f38,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | r2_hidden(sK2(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f23])).
% 1.41/0.55  % SZS output end Proof for theBenchmark
% 1.41/0.55  % (21604)------------------------------
% 1.41/0.55  % (21604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (21604)Termination reason: Refutation
% 1.41/0.55  
% 1.41/0.55  % (21604)Memory used [KB]: 1791
% 1.41/0.55  % (21604)Time elapsed: 0.117 s
% 1.41/0.55  % (21604)------------------------------
% 1.41/0.55  % (21604)------------------------------
% 1.41/0.55  % (21603)Success in time 0.181 s
%------------------------------------------------------------------------------
