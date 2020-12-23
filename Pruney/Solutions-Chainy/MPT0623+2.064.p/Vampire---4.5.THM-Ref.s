%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 298 expanded)
%              Number of leaves         :   17 (  88 expanded)
%              Depth                    :   21
%              Number of atoms          :  287 (1393 expanded)
%              Number of equality atoms :  122 ( 645 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1443,plain,(
    $false ),
    inference(equality_resolution,[],[f1441])).

fof(f1441,plain,(
    ! [X0] : sK1 != X0 ),
    inference(resolution,[],[f1440,f42])).

fof(f42,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f1440,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_xboole_0,X1)
      | sK1 != X0 ) ),
    inference(subsumption_resolution,[],[f1439,f85])).

fof(f85,plain,(
    k1_xboole_0 != sK0 ),
    inference(condensation,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 != sK0 ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 != X0
      | k1_xboole_0 != sK0 ) ),
    inference(superposition,[],[f81,f37])).

fof(f37,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK0)
        | k1_relat_1(X2) != sK1
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f21])).

fof(f21,plain,
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

fof(f15,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f81,plain,(
    ! [X0] :
      ( sK1 != X0
      | k1_xboole_0 != X0 ) ),
    inference(subsumption_resolution,[],[f80,f49])).

fof(f49,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X2] :
          ( np__1 = k1_funct_1(sK3(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK3(X0)) = X0
      & v1_funct_1(sK3(X0))
      & v1_relat_1(sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = np__1
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( np__1 = k1_funct_1(sK3(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK3(X0)) = X0
        & v1_funct_1(sK3(X0))
        & v1_relat_1(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = np__1 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

fof(f80,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ v1_relat_1(sK3(X0))
      | k1_xboole_0 != X0 ) ),
    inference(subsumption_resolution,[],[f77,f50])).

fof(f50,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ v1_funct_1(sK3(X0))
      | ~ v1_relat_1(sK3(X0))
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f75,f51])).

fof(f51,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f74,f41])).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f74,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,sK0)
      | k1_relat_1(X0) != sK1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,sK0)
      | k1_relat_1(X0) != sK1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f38,f43])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f38,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK0)
      | k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1439,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | k1_xboole_0 = sK0
      | ~ r1_xboole_0(k1_xboole_0,X1) ) ),
    inference(condensation,[],[f1371])).

fof(f1371,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = sK0
      | sK1 != X0
      | ~ r1_xboole_0(k1_xboole_0,X1)
      | sK1 != X2 ) ),
    inference(superposition,[],[f1209,f1228])).

fof(f1228,plain,(
    ! [X0] :
      ( sK0 = k1_relat_1(sK0)
      | sK1 != X0 ) ),
    inference(condensation,[],[f1227])).

fof(f1227,plain,(
    ! [X39,X40] :
      ( sK0 = k1_relat_1(sK0)
      | sK1 != X39
      | sK1 != X40 ) ),
    inference(resolution,[],[f1205,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK0)
      | sK1 != X0 ) ),
    inference(resolution,[],[f122,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),sK0)
      | sK1 != X0 ) ),
    inference(subsumption_resolution,[],[f121,f81])).

fof(f121,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r1_tarski(k1_tarski(X1),sK0)
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r1_tarski(k1_tarski(X1),sK0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f118,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
          & k1_relat_1(sK2(X0,X1)) = X0
          & v1_funct_1(sK2(X0,X1))
          & v1_relat_1(sK2(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
        & k1_relat_1(sK2(X0,X1)) = X0
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

fof(f118,plain,(
    ! [X4,X5] :
      ( sK1 != k1_relat_1(sK2(X4,X5))
      | ~ r1_tarski(k1_tarski(X5),sK0)
      | k1_xboole_0 = X4 ) ),
    inference(subsumption_resolution,[],[f117,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f117,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k1_tarski(X5),sK0)
      | sK1 != k1_relat_1(sK2(X4,X5))
      | ~ v1_relat_1(sK2(X4,X5))
      | k1_xboole_0 = X4 ) ),
    inference(subsumption_resolution,[],[f115,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f115,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k1_tarski(X5),sK0)
      | sK1 != k1_relat_1(sK2(X4,X5))
      | ~ v1_funct_1(sK2(X4,X5))
      | ~ v1_relat_1(sK2(X4,X5))
      | k1_xboole_0 = X4 ) ),
    inference(superposition,[],[f38,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1205,plain,(
    ! [X43,X44] :
      ( r2_hidden(sK5(sK0,X43),X43)
      | k1_relat_1(sK0) = X43
      | sK1 != X44 ) ),
    inference(resolution,[],[f58,f123])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
      | k1_relat_1(X0) = X1
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f31,f34,f33,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f1209,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 = k1_relat_1(sK0)
      | sK1 != X3
      | ~ r1_xboole_0(k1_xboole_0,X4) ) ),
    inference(resolution,[],[f1205,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f70,f41])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f54,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (30649)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.42  % (30647)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.44  % (30649)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f1443,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(equality_resolution,[],[f1441])).
% 0.21/0.44  fof(f1441,plain,(
% 0.21/0.44    ( ! [X0] : (sK1 != X0) )),
% 0.21/0.44    inference(resolution,[],[f1440,f42])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.44  fof(f1440,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_xboole_0(k1_xboole_0,X1) | sK1 != X0) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f1439,f85])).
% 0.21/0.44  fof(f85,plain,(
% 0.21/0.44    k1_xboole_0 != sK0),
% 0.21/0.44    inference(condensation,[],[f84])).
% 0.21/0.44  fof(f84,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 != sK0) )),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f82])).
% 0.21/0.44  fof(f82,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 != sK0) )),
% 0.21/0.44    inference(superposition,[],[f81,f37])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    k1_xboole_0 = sK1 | k1_xboole_0 != sK0),
% 0.21/0.44    inference(cnf_transformation,[],[f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.21/0.44    inference(flattening,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.44    inference(negated_conjecture,[],[f11])).
% 0.21/0.44  fof(f11,conjecture,(
% 0.21/0.44    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).
% 0.21/0.44  fof(f81,plain,(
% 0.21/0.44    ( ! [X0] : (sK1 != X0 | k1_xboole_0 != X0) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f80,f49])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ! [X0] : (! [X2] : (np__1 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0)))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (np__1 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0))))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,axiom,(
% 0.21/0.44    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = np__1) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).
% 0.21/0.44  fof(f80,plain,(
% 0.21/0.44    ( ! [X0] : (sK1 != X0 | ~v1_relat_1(sK3(X0)) | k1_xboole_0 != X0) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f77,f50])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f27])).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    ( ! [X0] : (sK1 != X0 | ~v1_funct_1(sK3(X0)) | ~v1_relat_1(sK3(X0)) | k1_xboole_0 != X0) )),
% 0.21/0.44    inference(superposition,[],[f75,f51])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f27])).
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    ( ! [X0] : (k1_relat_1(X0) != sK1 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f74,f41])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tarski(k1_xboole_0,sK0) | k1_relat_1(X0) != sK1 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) )),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f73])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tarski(k1_xboole_0,sK0) | k1_relat_1(X0) != sK1 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(superposition,[],[f38,f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(nnf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f22])).
% 0.21/0.44  fof(f1439,plain,(
% 0.21/0.44    ( ! [X0,X1] : (sK1 != X0 | k1_xboole_0 = sK0 | ~r1_xboole_0(k1_xboole_0,X1)) )),
% 0.21/0.44    inference(condensation,[],[f1371])).
% 0.21/0.44  fof(f1371,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k1_xboole_0 = sK0 | sK1 != X0 | ~r1_xboole_0(k1_xboole_0,X1) | sK1 != X2) )),
% 0.21/0.44    inference(superposition,[],[f1209,f1228])).
% 0.21/0.44  fof(f1228,plain,(
% 0.21/0.44    ( ! [X0] : (sK0 = k1_relat_1(sK0) | sK1 != X0) )),
% 0.21/0.44    inference(condensation,[],[f1227])).
% 0.21/0.44  fof(f1227,plain,(
% 0.21/0.44    ( ! [X39,X40] : (sK0 = k1_relat_1(sK0) | sK1 != X39 | sK1 != X40) )),
% 0.21/0.44    inference(resolution,[],[f1205,f123])).
% 0.21/0.44  fof(f123,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r2_hidden(X1,sK0) | sK1 != X0) )),
% 0.21/0.44    inference(resolution,[],[f122,f61])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f36])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.44    inference(nnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.44  fof(f122,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),sK0) | sK1 != X0) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f121,f81])).
% 0.21/0.44  fof(f121,plain,(
% 0.21/0.44    ( ! [X0,X1] : (sK1 != X0 | ~r1_tarski(k1_tarski(X1),sK0) | k1_xboole_0 = X0) )),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f119])).
% 0.21/0.44  fof(f119,plain,(
% 0.21/0.44    ( ! [X0,X1] : (sK1 != X0 | ~r1_tarski(k1_tarski(X1),sK0) | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 0.21/0.44    inference(superposition,[],[f118,f47])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))) | k1_xboole_0 = X0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ! [X1,X0] : (? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 0.21/0.44    inference(ennf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,axiom,(
% 0.21/0.44    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).
% 0.21/0.44  fof(f118,plain,(
% 0.21/0.44    ( ! [X4,X5] : (sK1 != k1_relat_1(sK2(X4,X5)) | ~r1_tarski(k1_tarski(X5),sK0) | k1_xboole_0 = X4) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f117,f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f25])).
% 0.21/0.44  fof(f117,plain,(
% 0.21/0.44    ( ! [X4,X5] : (~r1_tarski(k1_tarski(X5),sK0) | sK1 != k1_relat_1(sK2(X4,X5)) | ~v1_relat_1(sK2(X4,X5)) | k1_xboole_0 = X4) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f115,f46])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f25])).
% 0.21/0.44  fof(f115,plain,(
% 0.21/0.44    ( ! [X4,X5] : (~r1_tarski(k1_tarski(X5),sK0) | sK1 != k1_relat_1(sK2(X4,X5)) | ~v1_funct_1(sK2(X4,X5)) | ~v1_relat_1(sK2(X4,X5)) | k1_xboole_0 = X4) )),
% 0.21/0.44    inference(superposition,[],[f38,f48])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f25])).
% 0.21/0.44  fof(f1205,plain,(
% 0.21/0.44    ( ! [X43,X44] : (r2_hidden(sK5(sK0,X43),X43) | k1_relat_1(sK0) = X43 | sK1 != X44) )),
% 0.21/0.44    inference(resolution,[],[f58,f123])).
% 0.21/0.44  fof(f58,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) | k1_relat_1(X0) = X1 | r2_hidden(sK5(X0,X1),X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f35])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f31,f34,f33,f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.44    inference(rectify,[],[f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.44    inference(nnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.44  fof(f1209,plain,(
% 0.21/0.44    ( ! [X4,X3] : (k1_xboole_0 = k1_relat_1(sK0) | sK1 != X3 | ~r1_xboole_0(k1_xboole_0,X4)) )),
% 0.21/0.44    inference(resolution,[],[f1205,f71])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.44    inference(resolution,[],[f70,f41])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.44    inference(superposition,[],[f54,f55])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(rectify,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (30649)------------------------------
% 0.21/0.44  % (30649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (30649)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (30649)Memory used [KB]: 1791
% 0.21/0.44  % (30649)Time elapsed: 0.019 s
% 0.21/0.44  % (30649)------------------------------
% 0.21/0.44  % (30649)------------------------------
% 0.21/0.44  % (30630)Success in time 0.079 s
%------------------------------------------------------------------------------
