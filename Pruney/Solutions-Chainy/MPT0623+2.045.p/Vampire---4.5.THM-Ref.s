%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:09 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 386 expanded)
%              Number of leaves         :   14 ( 109 expanded)
%              Depth                    :   25
%              Number of atoms          :  316 (1848 expanded)
%              Number of equality atoms :  151 ( 863 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f341,plain,(
    $false ),
    inference(subsumption_resolution,[],[f340,f80])).

fof(f80,plain,(
    k1_xboole_0 != sK1 ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X3] :
      ( sK1 != X3
      | k1_xboole_0 != X3 ) ),
    inference(subsumption_resolution,[],[f78,f58])).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK6(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK6(X0,X1)) = X0
      & v1_funct_1(sK6(X0,X1))
      & v1_relat_1(sK6(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f19,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK6(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK6(X0,X1)) = X0
        & v1_funct_1(sK6(X0,X1))
        & v1_relat_1(sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f78,plain,(
    ! [X4,X3] :
      ( sK1 != X3
      | ~ v1_relat_1(sK6(X3,X4))
      | k1_xboole_0 != X3 ) ),
    inference(subsumption_resolution,[],[f75,f59])).

fof(f59,plain,(
    ! [X0,X1] : v1_funct_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f75,plain,(
    ! [X4,X3] :
      ( sK1 != X3
      | ~ v1_funct_1(sK6(X3,X4))
      | ~ v1_relat_1(sK6(X3,X4))
      | k1_xboole_0 != X3 ) ),
    inference(superposition,[],[f70,f60])).

fof(f60,plain,(
    ! [X0,X1] : k1_relat_1(sK6(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f69,f40])).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f69,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,sK0)
      | k1_relat_1(X0) != sK1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,sK0)
      | k1_relat_1(X0) != sK1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f39,f43])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f39,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK0)
      | k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK0)
        | k1_relat_1(X2) != sK1
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f20])).

fof(f20,plain,
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

fof(f12,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f340,plain,(
    k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f292])).

fof(f292,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f38,f291])).

fof(f291,plain,(
    k1_xboole_0 = sK0 ),
    inference(equality_resolution,[],[f285])).

fof(f285,plain,(
    ! [X15] :
      ( sK1 != X15
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f272,f144])).

fof(f144,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,k1_xboole_0)
      | sK1 != X7 ) ),
    inference(resolution,[],[f136,f40])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,sK0)
      | ~ r2_hidden(X1,X2)
      | sK1 != X0 ) ),
    inference(resolution,[],[f135,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK0)
      | sK1 != X0 ) ),
    inference(subsumption_resolution,[],[f134,f79])).

fof(f134,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | k1_xboole_0 = X0
      | ~ r2_hidden(X1,sK0) ) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | k1_xboole_0 = X0
      | ~ r2_hidden(X1,sK0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f115,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
          & k1_relat_1(sK2(X0,X1)) = X0
          & v1_funct_1(sK2(X0,X1))
          & v1_relat_1(sK2(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f23])).

fof(f23,plain,(
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

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f115,plain,(
    ! [X2,X3] :
      ( sK1 != k1_relat_1(sK2(X2,X3))
      | k1_xboole_0 = X2
      | ~ r2_hidden(X3,sK0) ) ),
    inference(backward_demodulation,[],[f82,f113])).

fof(f113,plain,(
    ! [X0] : sK4(k1_tarski(X0),sK0) = X0 ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK4(k1_tarski(X1),sK0) = X1 ) ),
    inference(subsumption_resolution,[],[f111,f79])).

fof(f111,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | k1_xboole_0 = X0
      | sK4(k1_tarski(X1),sK0) = X1 ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | k1_xboole_0 = X0
      | sK4(k1_tarski(X1),sK0) = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f104,f47])).

fof(f104,plain,(
    ! [X0,X1] :
      ( sK1 != k1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0
      | sK4(k1_tarski(X1),sK0) = X1 ) ),
    inference(resolution,[],[f81,f64])).

fof(f64,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k1_tarski(X1),sK0),k1_tarski(X1))
      | k1_xboole_0 = X0
      | sK1 != k1_relat_1(sK2(X0,X1)) ) ),
    inference(resolution,[],[f72,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f72,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_tarski(X2),sK0)
      | sK1 != k1_relat_1(sK2(X1,X2))
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f71,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_tarski(X2),sK0)
      | sK1 != k1_relat_1(sK2(X1,X2))
      | ~ v1_relat_1(sK2(X1,X2))
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f68,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f68,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_tarski(X2),sK0)
      | sK1 != k1_relat_1(sK2(X1,X2))
      | ~ v1_funct_1(sK2(X1,X2))
      | ~ v1_relat_1(sK2(X1,X2))
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f39,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f82,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK4(k1_tarski(X3),sK0),sK0)
      | k1_xboole_0 = X2
      | sK1 != k1_relat_1(sK2(X2,X3)) ) ),
    inference(resolution,[],[f72,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f272,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0,sK0),X0)
      | sK0 = X0 ) ),
    inference(equality_resolution,[],[f137])).

fof(f137,plain,(
    ! [X4,X3] :
      ( sK1 != X3
      | sK0 = X4
      | r2_hidden(sK3(X4,sK0),X4) ) ),
    inference(resolution,[],[f135,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f38,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n015.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:43:53 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.37  ipcrm: permission denied for id (798752768)
% 0.15/0.37  ipcrm: permission denied for id (805404673)
% 0.15/0.37  ipcrm: permission denied for id (803995650)
% 0.15/0.37  ipcrm: permission denied for id (800489475)
% 0.15/0.37  ipcrm: permission denied for id (800555013)
% 0.15/0.38  ipcrm: permission denied for id (800620551)
% 0.15/0.38  ipcrm: permission denied for id (800686089)
% 0.15/0.38  ipcrm: permission denied for id (798851082)
% 0.15/0.38  ipcrm: permission denied for id (800718859)
% 0.15/0.38  ipcrm: permission denied for id (800751628)
% 0.15/0.38  ipcrm: permission denied for id (798916621)
% 0.15/0.38  ipcrm: permission denied for id (800784398)
% 0.15/0.39  ipcrm: permission denied for id (800817167)
% 0.15/0.39  ipcrm: permission denied for id (800849936)
% 0.15/0.39  ipcrm: permission denied for id (805568530)
% 0.15/0.39  ipcrm: permission denied for id (800948243)
% 0.15/0.39  ipcrm: permission denied for id (799014932)
% 0.15/0.39  ipcrm: permission denied for id (799047701)
% 0.15/0.39  ipcrm: permission denied for id (800981014)
% 0.15/0.39  ipcrm: permission denied for id (801013783)
% 0.15/0.40  ipcrm: permission denied for id (804192280)
% 0.15/0.40  ipcrm: permission denied for id (801079321)
% 0.15/0.40  ipcrm: permission denied for id (801112090)
% 0.15/0.40  ipcrm: permission denied for id (799113243)
% 0.15/0.40  ipcrm: permission denied for id (799146012)
% 0.15/0.40  ipcrm: permission denied for id (804225053)
% 0.15/0.40  ipcrm: permission denied for id (801177630)
% 0.15/0.40  ipcrm: permission denied for id (804257823)
% 0.15/0.41  ipcrm: permission denied for id (804290592)
% 0.15/0.41  ipcrm: permission denied for id (801275937)
% 0.15/0.41  ipcrm: permission denied for id (801308706)
% 0.15/0.41  ipcrm: permission denied for id (804323363)
% 0.15/0.41  ipcrm: permission denied for id (801374244)
% 0.15/0.41  ipcrm: permission denied for id (801407013)
% 0.15/0.41  ipcrm: permission denied for id (805601318)
% 0.15/0.41  ipcrm: permission denied for id (799277095)
% 0.15/0.42  ipcrm: permission denied for id (801472552)
% 0.15/0.42  ipcrm: permission denied for id (804388905)
% 0.15/0.42  ipcrm: permission denied for id (799375402)
% 0.15/0.42  ipcrm: permission denied for id (804421675)
% 0.15/0.42  ipcrm: permission denied for id (799440940)
% 0.15/0.42  ipcrm: permission denied for id (801570861)
% 0.22/0.42  ipcrm: permission denied for id (799473710)
% 0.22/0.42  ipcrm: permission denied for id (801603631)
% 0.22/0.43  ipcrm: permission denied for id (804454448)
% 0.22/0.43  ipcrm: permission denied for id (799539249)
% 0.22/0.43  ipcrm: permission denied for id (799572018)
% 0.22/0.43  ipcrm: permission denied for id (806354995)
% 0.22/0.43  ipcrm: permission denied for id (804519988)
% 0.22/0.43  ipcrm: permission denied for id (804552757)
% 0.22/0.43  ipcrm: permission denied for id (801767478)
% 0.22/0.44  ipcrm: permission denied for id (801833016)
% 0.22/0.44  ipcrm: permission denied for id (801865785)
% 0.22/0.44  ipcrm: permission denied for id (799637562)
% 0.22/0.44  ipcrm: permission denied for id (801898555)
% 0.22/0.44  ipcrm: permission denied for id (801931324)
% 0.22/0.44  ipcrm: permission denied for id (799670333)
% 0.22/0.44  ipcrm: permission denied for id (799703102)
% 0.22/0.44  ipcrm: permission denied for id (804618303)
% 0.22/0.45  ipcrm: permission denied for id (799735872)
% 0.22/0.45  ipcrm: permission denied for id (801996865)
% 0.22/0.45  ipcrm: permission denied for id (804651074)
% 0.22/0.45  ipcrm: permission denied for id (802062403)
% 0.22/0.45  ipcrm: permission denied for id (806420548)
% 0.22/0.45  ipcrm: permission denied for id (802127941)
% 0.22/0.45  ipcrm: permission denied for id (802160710)
% 0.22/0.45  ipcrm: permission denied for id (802193479)
% 0.22/0.46  ipcrm: permission denied for id (802226248)
% 0.22/0.46  ipcrm: permission denied for id (804716617)
% 0.22/0.46  ipcrm: permission denied for id (805797964)
% 0.22/0.46  ipcrm: permission denied for id (802422861)
% 0.22/0.46  ipcrm: permission denied for id (802455630)
% 0.22/0.46  ipcrm: permission denied for id (805830735)
% 0.22/0.47  ipcrm: permission denied for id (802553937)
% 0.22/0.47  ipcrm: permission denied for id (799866962)
% 0.22/0.47  ipcrm: permission denied for id (802586707)
% 0.22/0.47  ipcrm: permission denied for id (802619476)
% 0.22/0.47  ipcrm: permission denied for id (802652245)
% 0.22/0.47  ipcrm: permission denied for id (802685014)
% 0.22/0.47  ipcrm: permission denied for id (802717783)
% 0.22/0.47  ipcrm: permission denied for id (802750552)
% 0.22/0.48  ipcrm: permission denied for id (802783321)
% 0.22/0.48  ipcrm: permission denied for id (804913242)
% 0.22/0.48  ipcrm: permission denied for id (799965275)
% 0.22/0.48  ipcrm: permission denied for id (802848860)
% 0.22/0.48  ipcrm: permission denied for id (805896285)
% 0.22/0.48  ipcrm: permission denied for id (804978782)
% 0.22/0.48  ipcrm: permission denied for id (800030815)
% 0.22/0.48  ipcrm: permission denied for id (802947168)
% 0.22/0.49  ipcrm: permission denied for id (806551649)
% 0.22/0.49  ipcrm: permission denied for id (800096354)
% 0.22/0.49  ipcrm: permission denied for id (803012707)
% 0.22/0.49  ipcrm: permission denied for id (803078244)
% 0.22/0.49  ipcrm: permission denied for id (803111013)
% 0.22/0.49  ipcrm: permission denied for id (803143782)
% 0.22/0.49  ipcrm: permission denied for id (805044327)
% 0.22/0.50  ipcrm: permission denied for id (803242089)
% 0.22/0.50  ipcrm: permission denied for id (803274858)
% 0.22/0.50  ipcrm: permission denied for id (800227435)
% 0.22/0.50  ipcrm: permission denied for id (805994604)
% 0.22/0.50  ipcrm: permission denied for id (803340397)
% 0.22/0.50  ipcrm: permission denied for id (806617198)
% 0.22/0.50  ipcrm: permission denied for id (803405935)
% 0.22/0.50  ipcrm: permission denied for id (806649968)
% 0.22/0.51  ipcrm: permission denied for id (806092913)
% 0.22/0.51  ipcrm: permission denied for id (803537010)
% 0.22/0.51  ipcrm: permission denied for id (803569779)
% 0.22/0.51  ipcrm: permission denied for id (805240948)
% 0.22/0.51  ipcrm: permission denied for id (803635317)
% 0.22/0.51  ipcrm: permission denied for id (803700855)
% 0.22/0.51  ipcrm: permission denied for id (805306488)
% 0.22/0.51  ipcrm: permission denied for id (803766393)
% 0.22/0.52  ipcrm: permission denied for id (806158458)
% 0.22/0.52  ipcrm: permission denied for id (803831931)
% 0.22/0.52  ipcrm: permission denied for id (806191228)
% 0.22/0.52  ipcrm: permission denied for id (803897469)
% 0.22/0.52  ipcrm: permission denied for id (800391294)
% 0.22/0.52  ipcrm: permission denied for id (803930239)
% 0.78/0.64  % (7082)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.78/0.65  % (7073)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.15/0.66  % (7082)Refutation found. Thanks to Tanya!
% 1.15/0.66  % SZS status Theorem for theBenchmark
% 1.15/0.66  % SZS output start Proof for theBenchmark
% 1.15/0.66  fof(f341,plain,(
% 1.15/0.66    $false),
% 1.15/0.66    inference(subsumption_resolution,[],[f340,f80])).
% 1.15/0.66  fof(f80,plain,(
% 1.15/0.66    k1_xboole_0 != sK1),
% 1.15/0.66    inference(equality_resolution,[],[f79])).
% 1.15/0.66  fof(f79,plain,(
% 1.15/0.66    ( ! [X3] : (sK1 != X3 | k1_xboole_0 != X3) )),
% 1.15/0.66    inference(subsumption_resolution,[],[f78,f58])).
% 1.15/0.66  fof(f58,plain,(
% 1.15/0.66    ( ! [X0,X1] : (v1_relat_1(sK6(X0,X1))) )),
% 1.15/0.66    inference(cnf_transformation,[],[f37])).
% 1.15/0.66  fof(f37,plain,(
% 1.15/0.66    ! [X0,X1] : (! [X3] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK6(X0,X1)) = X0 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1)))),
% 1.15/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f19,f36])).
% 1.15/0.66  fof(f36,plain,(
% 1.15/0.66    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK6(X0,X1)) = X0 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1))))),
% 1.15/0.66    introduced(choice_axiom,[])).
% 1.15/0.66  fof(f19,plain,(
% 1.15/0.66    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.15/0.66    inference(ennf_transformation,[],[f7])).
% 1.15/0.66  fof(f7,axiom,(
% 1.15/0.66    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 1.15/0.66  fof(f78,plain,(
% 1.15/0.66    ( ! [X4,X3] : (sK1 != X3 | ~v1_relat_1(sK6(X3,X4)) | k1_xboole_0 != X3) )),
% 1.15/0.66    inference(subsumption_resolution,[],[f75,f59])).
% 1.15/0.66  fof(f59,plain,(
% 1.15/0.66    ( ! [X0,X1] : (v1_funct_1(sK6(X0,X1))) )),
% 1.15/0.66    inference(cnf_transformation,[],[f37])).
% 1.15/0.66  fof(f75,plain,(
% 1.15/0.66    ( ! [X4,X3] : (sK1 != X3 | ~v1_funct_1(sK6(X3,X4)) | ~v1_relat_1(sK6(X3,X4)) | k1_xboole_0 != X3) )),
% 1.15/0.66    inference(superposition,[],[f70,f60])).
% 1.15/0.66  fof(f60,plain,(
% 1.15/0.66    ( ! [X0,X1] : (k1_relat_1(sK6(X0,X1)) = X0) )),
% 1.15/0.66    inference(cnf_transformation,[],[f37])).
% 1.15/0.66  fof(f70,plain,(
% 1.15/0.66    ( ! [X0] : (k1_relat_1(X0) != sK1 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) )),
% 1.15/0.66    inference(subsumption_resolution,[],[f69,f40])).
% 1.15/0.66  fof(f40,plain,(
% 1.15/0.66    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.15/0.66    inference(cnf_transformation,[],[f3])).
% 1.15/0.66  fof(f3,axiom,(
% 1.15/0.66    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.15/0.66  fof(f69,plain,(
% 1.15/0.66    ( ! [X0] : (~r1_tarski(k1_xboole_0,sK0) | k1_relat_1(X0) != sK1 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) )),
% 1.15/0.66    inference(duplicate_literal_removal,[],[f67])).
% 1.15/0.66  fof(f67,plain,(
% 1.15/0.66    ( ! [X0] : (~r1_tarski(k1_xboole_0,sK0) | k1_relat_1(X0) != sK1 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.15/0.66    inference(superposition,[],[f39,f43])).
% 1.15/0.66  fof(f43,plain,(
% 1.15/0.66    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.15/0.66    inference(cnf_transformation,[],[f22])).
% 1.15/0.66  fof(f22,plain,(
% 1.15/0.66    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.15/0.66    inference(nnf_transformation,[],[f15])).
% 1.15/0.66  fof(f15,plain,(
% 1.15/0.66    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.15/0.66    inference(ennf_transformation,[],[f6])).
% 1.15/0.66  fof(f6,axiom,(
% 1.15/0.66    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.15/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 1.15/0.66  fof(f39,plain,(
% 1.15/0.66    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.15/0.66    inference(cnf_transformation,[],[f21])).
% 1.15/0.66  fof(f21,plain,(
% 1.15/0.66    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0)),
% 1.15/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f20])).
% 1.15/0.67  fof(f20,plain,(
% 1.15/0.67    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0))),
% 1.15/0.67    introduced(choice_axiom,[])).
% 1.15/0.67  fof(f12,plain,(
% 1.15/0.67    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.15/0.67    inference(flattening,[],[f11])).
% 1.15/0.67  fof(f11,plain,(
% 1.15/0.67    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.15/0.67    inference(ennf_transformation,[],[f10])).
% 1.15/0.67  fof(f10,negated_conjecture,(
% 1.15/0.67    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.15/0.67    inference(negated_conjecture,[],[f9])).
% 1.15/0.67  fof(f9,conjecture,(
% 1.15/0.67    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.15/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 1.15/0.67  fof(f340,plain,(
% 1.15/0.67    k1_xboole_0 = sK1),
% 1.15/0.67    inference(trivial_inequality_removal,[],[f292])).
% 1.15/0.67  fof(f292,plain,(
% 1.15/0.67    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1),
% 1.15/0.67    inference(backward_demodulation,[],[f38,f291])).
% 1.15/0.67  fof(f291,plain,(
% 1.15/0.67    k1_xboole_0 = sK0),
% 1.15/0.67    inference(equality_resolution,[],[f285])).
% 1.15/0.67  fof(f285,plain,(
% 1.15/0.67    ( ! [X15] : (sK1 != X15 | k1_xboole_0 = sK0) )),
% 1.15/0.67    inference(resolution,[],[f272,f144])).
% 1.15/0.67  fof(f144,plain,(
% 1.15/0.67    ( ! [X6,X7] : (~r2_hidden(X6,k1_xboole_0) | sK1 != X7) )),
% 1.15/0.67    inference(resolution,[],[f136,f40])).
% 1.15/0.67  fof(f136,plain,(
% 1.15/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X2,sK0) | ~r2_hidden(X1,X2) | sK1 != X0) )),
% 1.15/0.67    inference(resolution,[],[f135,f51])).
% 1.15/0.67  fof(f51,plain,(
% 1.15/0.67    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.15/0.67    inference(cnf_transformation,[],[f31])).
% 1.15/0.67  fof(f31,plain,(
% 1.15/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.15/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).
% 1.15/0.67  fof(f30,plain,(
% 1.15/0.67    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.15/0.67    introduced(choice_axiom,[])).
% 1.15/0.67  fof(f29,plain,(
% 1.15/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.15/0.67    inference(rectify,[],[f28])).
% 1.15/0.67  fof(f28,plain,(
% 1.15/0.67    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.15/0.67    inference(nnf_transformation,[],[f18])).
% 1.15/0.67  fof(f18,plain,(
% 1.15/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.15/0.67    inference(ennf_transformation,[],[f1])).
% 1.15/0.67  fof(f1,axiom,(
% 1.15/0.67    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.15/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.15/0.67  fof(f135,plain,(
% 1.15/0.67    ( ! [X0,X1] : (~r2_hidden(X1,sK0) | sK1 != X0) )),
% 1.15/0.67    inference(subsumption_resolution,[],[f134,f79])).
% 1.15/0.67  fof(f134,plain,(
% 1.15/0.67    ( ! [X0,X1] : (sK1 != X0 | k1_xboole_0 = X0 | ~r2_hidden(X1,sK0)) )),
% 1.15/0.67    inference(duplicate_literal_removal,[],[f132])).
% 1.15/0.67  fof(f132,plain,(
% 1.15/0.67    ( ! [X0,X1] : (sK1 != X0 | k1_xboole_0 = X0 | ~r2_hidden(X1,sK0) | k1_xboole_0 = X0) )),
% 1.15/0.67    inference(superposition,[],[f115,f47])).
% 1.15/0.67  fof(f47,plain,(
% 1.15/0.67    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 1.15/0.67    inference(cnf_transformation,[],[f24])).
% 1.15/0.67  fof(f24,plain,(
% 1.15/0.67    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))) | k1_xboole_0 = X0)),
% 1.15/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f23])).
% 1.15/0.67  fof(f23,plain,(
% 1.15/0.67    ! [X1,X0] : (? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 1.15/0.67    introduced(choice_axiom,[])).
% 1.15/0.67  fof(f16,plain,(
% 1.15/0.67    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 1.15/0.67    inference(ennf_transformation,[],[f8])).
% 1.15/0.67  fof(f8,axiom,(
% 1.15/0.67    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.15/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 1.15/0.67  fof(f115,plain,(
% 1.15/0.67    ( ! [X2,X3] : (sK1 != k1_relat_1(sK2(X2,X3)) | k1_xboole_0 = X2 | ~r2_hidden(X3,sK0)) )),
% 1.15/0.67    inference(backward_demodulation,[],[f82,f113])).
% 1.15/0.67  fof(f113,plain,(
% 1.15/0.67    ( ! [X0] : (sK4(k1_tarski(X0),sK0) = X0) )),
% 1.15/0.67    inference(equality_resolution,[],[f112])).
% 1.15/0.67  fof(f112,plain,(
% 1.15/0.67    ( ! [X0,X1] : (sK1 != X0 | sK4(k1_tarski(X1),sK0) = X1) )),
% 1.15/0.67    inference(subsumption_resolution,[],[f111,f79])).
% 1.15/0.67  fof(f111,plain,(
% 1.15/0.67    ( ! [X0,X1] : (sK1 != X0 | k1_xboole_0 = X0 | sK4(k1_tarski(X1),sK0) = X1) )),
% 1.15/0.67    inference(duplicate_literal_removal,[],[f109])).
% 1.15/0.67  fof(f109,plain,(
% 1.15/0.67    ( ! [X0,X1] : (sK1 != X0 | k1_xboole_0 = X0 | sK4(k1_tarski(X1),sK0) = X1 | k1_xboole_0 = X0) )),
% 1.15/0.67    inference(superposition,[],[f104,f47])).
% 1.15/0.67  fof(f104,plain,(
% 1.15/0.67    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0 | sK4(k1_tarski(X1),sK0) = X1) )),
% 1.15/0.67    inference(resolution,[],[f81,f64])).
% 1.15/0.67  fof(f64,plain,(
% 1.15/0.67    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 1.15/0.67    inference(equality_resolution,[],[f54])).
% 1.15/0.67  fof(f54,plain,(
% 1.15/0.67    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.15/0.67    inference(cnf_transformation,[],[f35])).
% 1.15/0.67  fof(f35,plain,(
% 1.15/0.67    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.15/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f33,f34])).
% 1.15/0.67  fof(f34,plain,(
% 1.15/0.67    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.15/0.67    introduced(choice_axiom,[])).
% 1.15/0.67  fof(f33,plain,(
% 1.15/0.67    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.15/0.67    inference(rectify,[],[f32])).
% 1.15/0.67  fof(f32,plain,(
% 1.15/0.67    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.15/0.67    inference(nnf_transformation,[],[f4])).
% 1.15/0.67  fof(f4,axiom,(
% 1.15/0.67    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.15/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.15/0.67  fof(f81,plain,(
% 1.15/0.67    ( ! [X0,X1] : (r2_hidden(sK4(k1_tarski(X1),sK0),k1_tarski(X1)) | k1_xboole_0 = X0 | sK1 != k1_relat_1(sK2(X0,X1))) )),
% 1.15/0.67    inference(resolution,[],[f72,f52])).
% 1.15/0.67  fof(f52,plain,(
% 1.15/0.67    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 1.15/0.67    inference(cnf_transformation,[],[f31])).
% 1.15/0.67  fof(f72,plain,(
% 1.15/0.67    ( ! [X2,X1] : (~r1_tarski(k1_tarski(X2),sK0) | sK1 != k1_relat_1(sK2(X1,X2)) | k1_xboole_0 = X1) )),
% 1.15/0.67    inference(subsumption_resolution,[],[f71,f45])).
% 1.15/0.67  fof(f45,plain,(
% 1.15/0.67    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.15/0.67    inference(cnf_transformation,[],[f24])).
% 1.15/0.67  fof(f71,plain,(
% 1.15/0.67    ( ! [X2,X1] : (~r1_tarski(k1_tarski(X2),sK0) | sK1 != k1_relat_1(sK2(X1,X2)) | ~v1_relat_1(sK2(X1,X2)) | k1_xboole_0 = X1) )),
% 1.15/0.67    inference(subsumption_resolution,[],[f68,f46])).
% 1.15/0.67  fof(f46,plain,(
% 1.15/0.67    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.15/0.67    inference(cnf_transformation,[],[f24])).
% 1.15/0.67  fof(f68,plain,(
% 1.15/0.67    ( ! [X2,X1] : (~r1_tarski(k1_tarski(X2),sK0) | sK1 != k1_relat_1(sK2(X1,X2)) | ~v1_funct_1(sK2(X1,X2)) | ~v1_relat_1(sK2(X1,X2)) | k1_xboole_0 = X1) )),
% 1.15/0.67    inference(superposition,[],[f39,f48])).
% 1.15/0.67  fof(f48,plain,(
% 1.15/0.67    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.15/0.67    inference(cnf_transformation,[],[f24])).
% 1.15/0.67  fof(f82,plain,(
% 1.15/0.67    ( ! [X2,X3] : (~r2_hidden(sK4(k1_tarski(X3),sK0),sK0) | k1_xboole_0 = X2 | sK1 != k1_relat_1(sK2(X2,X3))) )),
% 1.15/0.67    inference(resolution,[],[f72,f53])).
% 1.15/0.67  fof(f53,plain,(
% 1.15/0.67    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 1.15/0.67    inference(cnf_transformation,[],[f31])).
% 1.15/0.67  fof(f272,plain,(
% 1.15/0.67    ( ! [X0] : (r2_hidden(sK3(X0,sK0),X0) | sK0 = X0) )),
% 1.15/0.67    inference(equality_resolution,[],[f137])).
% 1.15/0.67  fof(f137,plain,(
% 1.15/0.67    ( ! [X4,X3] : (sK1 != X3 | sK0 = X4 | r2_hidden(sK3(X4,sK0),X4)) )),
% 1.15/0.67    inference(resolution,[],[f135,f49])).
% 1.15/0.67  fof(f49,plain,(
% 1.15/0.67    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 1.15/0.67    inference(cnf_transformation,[],[f27])).
% 1.15/0.67  fof(f27,plain,(
% 1.15/0.67    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) & (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0))))),
% 1.15/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).
% 1.15/0.67  fof(f26,plain,(
% 1.15/0.67    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) & (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0))))),
% 1.15/0.67    introduced(choice_axiom,[])).
% 1.15/0.67  fof(f25,plain,(
% 1.15/0.67    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.15/0.67    inference(nnf_transformation,[],[f17])).
% 1.15/0.67  fof(f17,plain,(
% 1.15/0.67    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.15/0.67    inference(ennf_transformation,[],[f2])).
% 1.15/0.67  fof(f2,axiom,(
% 1.15/0.67    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.15/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 1.15/0.67  fof(f38,plain,(
% 1.15/0.67    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 1.15/0.67    inference(cnf_transformation,[],[f21])).
% 1.15/0.67  % SZS output end Proof for theBenchmark
% 1.15/0.67  % (7082)------------------------------
% 1.15/0.67  % (7082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.67  % (7082)Termination reason: Refutation
% 1.15/0.67  
% 1.15/0.67  % (7082)Memory used [KB]: 1918
% 1.15/0.67  % (7082)Time elapsed: 0.030 s
% 1.15/0.67  % (7082)------------------------------
% 1.15/0.67  % (7082)------------------------------
% 1.15/0.67  % (6921)Success in time 0.309 s
%------------------------------------------------------------------------------
