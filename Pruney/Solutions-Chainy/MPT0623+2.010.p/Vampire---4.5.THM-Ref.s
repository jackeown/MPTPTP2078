%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 232 expanded)
%              Number of leaves         :   17 (  72 expanded)
%              Depth                    :   35
%              Number of atoms          :  309 (1053 expanded)
%              Number of equality atoms :  127 ( 446 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f765,plain,(
    $false ),
    inference(equality_resolution,[],[f758])).

fof(f758,plain,(
    ! [X2] : k1_xboole_0 != X2 ),
    inference(subsumption_resolution,[],[f757,f58])).

fof(f58,plain,(
    ! [X0] : v1_funct_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK4(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK4(X0)) = X0
      & v1_funct_1(sK4(X0))
      & v1_relat_1(sK4(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK4(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK4(X0)) = X0
        & v1_funct_1(sK4(X0))
        & v1_relat_1(sK4(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f757,plain,(
    ! [X2] :
      ( k1_xboole_0 != X2
      | ~ v1_funct_1(sK4(X2)) ) ),
    inference(subsumption_resolution,[],[f755,f57])).

fof(f57,plain,(
    ! [X0] : v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f755,plain,(
    ! [X2] :
      ( k1_xboole_0 != X2
      | ~ v1_relat_1(sK4(X2))
      | ~ v1_funct_1(sK4(X2)) ) ),
    inference(superposition,[],[f740,f59])).

fof(f59,plain,(
    ! [X0] : k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f33])).

fof(f740,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f737])).

fof(f737,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f730,f49])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f730,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f601])).

fof(f601,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f75,f597])).

fof(f597,plain,(
    k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f596])).

fof(f596,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(equality_resolution,[],[f584])).

fof(f584,plain,(
    ! [X18] :
      ( sK1 != X18
      | k1_xboole_0 = X18
      | k1_xboole_0 = sK1 ) ),
    inference(subsumption_resolution,[],[f573,f41])).

fof(f41,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK0)
        | k1_relat_1(X2) != sK1
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f24])).

fof(f24,plain,
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

fof(f16,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f573,plain,(
    ! [X18] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = X18
      | sK1 != X18 ) ),
    inference(resolution,[],[f405,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK0)
      | k1_xboole_0 = X0
      | sK1 != X0 ) ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | k1_xboole_0 = X0
      | ~ r2_hidden(X1,sK0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f78,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
          & k1_relat_1(sK2(X0,X1)) = X0
          & v1_funct_1(sK2(X0,X1))
          & v1_relat_1(sK2(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f26])).

fof(f26,plain,(
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

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( sK1 != k1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f77,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),sK0)
      | sK1 != k1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f76,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),sK0)
      | sK1 != k1_relat_1(sK2(X0,X1))
      | ~ v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f71,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),sK0)
      | sK1 != k1_relat_1(sK2(X0,X1))
      | ~ v1_funct_1(sK2(X0,X1))
      | ~ v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f42,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK0)
      | k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f405,plain,(
    ! [X1] :
      ( r2_hidden(sK5(k1_xboole_0,X1),X1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = X1 ) ),
    inference(forward_demodulation,[],[f389,f45])).

fof(f45,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f389,plain,(
    ! [X1] :
      ( k1_xboole_0 = sK1
      | k2_relat_1(k1_xboole_0) = X1
      | r2_hidden(sK5(k1_xboole_0,X1),X1) ) ),
    inference(resolution,[],[f387,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f35,f38,f37,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f387,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | k1_xboole_0 = sK1 ) ),
    inference(forward_demodulation,[],[f378,f45])).

fof(f378,plain,(
    ! [X4] :
      ( k1_xboole_0 = sK1
      | ~ r2_hidden(X4,k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f354,f43])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f354,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = sK1
      | ~ r2_hidden(X1,k2_relat_1(X0)) ) ),
    inference(resolution,[],[f343,f55])).

fof(f55,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f343,plain,(
    ! [X5] :
      ( v1_xboole_0(k2_relat_1(X5))
      | k1_xboole_0 = sK1
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f326,f55])).

fof(f326,plain,(
    ! [X11] :
      ( r2_hidden(sK5(sK0,X11),X11)
      | k1_xboole_0 = sK1
      | v1_xboole_0(k2_relat_1(X11)) ) ),
    inference(resolution,[],[f308,f56])).

fof(f56,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f308,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X8,k2_relat_1(X7))
      | r2_hidden(sK5(sK0,X7),X7)
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f304,f69])).

fof(f69,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f304,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_xboole_0 = sK1
      | r2_hidden(sK5(sK0,X1),X1) ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( sK1 != X2
      | ~ r2_hidden(X1,X0)
      | k1_xboole_0 = X2
      | r2_hidden(sK5(sK0,X0),X0) ) ),
    inference(subsumption_resolution,[],[f100,f80])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | sK1 != X2
      | k1_xboole_0 = X2
      | r2_hidden(k4_tarski(sK6(sK0,X0),sK5(sK0,X0)),sK0)
      | r2_hidden(sK5(sK0,X0),X0) ) ),
    inference(superposition,[],[f83,f64])).

fof(f83,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(sK0))
      | sK1 != X4
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f80,f69])).

fof(f75,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f74,f44])).

fof(f44,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f74,plain,
    ( k1_relat_1(k1_xboole_0) != sK1
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f70,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f70,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | k1_relat_1(k1_xboole_0) != sK1
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f42,f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:59:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (25377)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.48  % (25369)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (25369)Refutation not found, incomplete strategy% (25369)------------------------------
% 0.21/0.50  % (25369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (25369)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (25369)Memory used [KB]: 6140
% 0.21/0.50  % (25369)Time elapsed: 0.005 s
% 0.21/0.50  % (25369)------------------------------
% 0.21/0.50  % (25369)------------------------------
% 0.21/0.51  % (25377)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f765,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(equality_resolution,[],[f758])).
% 0.21/0.51  fof(f758,plain,(
% 0.21/0.51    ( ! [X2] : (k1_xboole_0 != X2) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f757,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_1(sK4(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 1.17/0.51  fof(f33,plain,(
% 1.17/0.51    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0)))),
% 1.17/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f32])).
% 1.17/0.51  fof(f32,plain,(
% 1.17/0.51    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0))))),
% 1.17/0.51    introduced(choice_axiom,[])).
% 1.17/0.51  fof(f21,plain,(
% 1.17/0.51    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.17/0.51    inference(ennf_transformation,[],[f10])).
% 1.17/0.51  fof(f10,axiom,(
% 1.17/0.51    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.17/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 1.17/0.51  fof(f757,plain,(
% 1.17/0.51    ( ! [X2] : (k1_xboole_0 != X2 | ~v1_funct_1(sK4(X2))) )),
% 1.17/0.51    inference(subsumption_resolution,[],[f755,f57])).
% 1.17/0.51  fof(f57,plain,(
% 1.17/0.51    ( ! [X0] : (v1_relat_1(sK4(X0))) )),
% 1.17/0.51    inference(cnf_transformation,[],[f33])).
% 1.17/0.51  fof(f755,plain,(
% 1.17/0.51    ( ! [X2] : (k1_xboole_0 != X2 | ~v1_relat_1(sK4(X2)) | ~v1_funct_1(sK4(X2))) )),
% 1.17/0.51    inference(superposition,[],[f740,f59])).
% 1.17/0.51  fof(f59,plain,(
% 1.17/0.51    ( ! [X0] : (k1_relat_1(sK4(X0)) = X0) )),
% 1.17/0.51    inference(cnf_transformation,[],[f33])).
% 1.17/0.51  fof(f740,plain,(
% 1.17/0.51    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0)) )),
% 1.17/0.51    inference(duplicate_literal_removal,[],[f737])).
% 1.17/0.51  fof(f737,plain,(
% 1.17/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.17/0.51    inference(superposition,[],[f730,f49])).
% 1.17/0.51  fof(f49,plain,(
% 1.17/0.51    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.17/0.51    inference(cnf_transformation,[],[f19])).
% 1.17/0.51  fof(f19,plain,(
% 1.17/0.51    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.17/0.51    inference(flattening,[],[f18])).
% 1.17/0.51  fof(f18,plain,(
% 1.17/0.51    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.17/0.51    inference(ennf_transformation,[],[f9])).
% 1.17/0.51  fof(f9,axiom,(
% 1.17/0.51    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.17/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.17/0.51  fof(f730,plain,(
% 1.17/0.51    ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.17/0.51    inference(trivial_inequality_removal,[],[f601])).
% 1.17/0.51  fof(f601,plain,(
% 1.17/0.51    k1_xboole_0 != k1_xboole_0 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.17/0.51    inference(backward_demodulation,[],[f75,f597])).
% 1.17/0.51  fof(f597,plain,(
% 1.17/0.51    k1_xboole_0 = sK1),
% 1.17/0.51    inference(duplicate_literal_removal,[],[f596])).
% 1.17/0.51  fof(f596,plain,(
% 1.17/0.51    k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.17/0.51    inference(equality_resolution,[],[f584])).
% 1.17/0.51  fof(f584,plain,(
% 1.17/0.51    ( ! [X18] : (sK1 != X18 | k1_xboole_0 = X18 | k1_xboole_0 = sK1) )),
% 1.17/0.51    inference(subsumption_resolution,[],[f573,f41])).
% 1.17/0.51  fof(f41,plain,(
% 1.17/0.51    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 1.17/0.51    inference(cnf_transformation,[],[f25])).
% 1.17/0.51  fof(f25,plain,(
% 1.17/0.51    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0)),
% 1.17/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f24])).
% 1.17/0.51  fof(f24,plain,(
% 1.17/0.51    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0))),
% 1.17/0.51    introduced(choice_axiom,[])).
% 1.17/0.52  fof(f16,plain,(
% 1.17/0.52    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.17/0.52    inference(flattening,[],[f15])).
% 1.17/0.52  fof(f15,plain,(
% 1.17/0.52    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.17/0.52    inference(ennf_transformation,[],[f14])).
% 1.17/0.52  fof(f14,negated_conjecture,(
% 1.17/0.52    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.17/0.52    inference(negated_conjecture,[],[f13])).
% 1.17/0.52  fof(f13,conjecture,(
% 1.17/0.52    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 1.17/0.52  fof(f573,plain,(
% 1.17/0.52    ( ! [X18] : (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = X18 | sK1 != X18) )),
% 1.17/0.52    inference(resolution,[],[f405,f80])).
% 1.17/0.52  fof(f80,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~r2_hidden(X1,sK0) | k1_xboole_0 = X0 | sK1 != X0) )),
% 1.17/0.52    inference(duplicate_literal_removal,[],[f79])).
% 1.17/0.52  fof(f79,plain,(
% 1.17/0.52    ( ! [X0,X1] : (sK1 != X0 | k1_xboole_0 = X0 | ~r2_hidden(X1,sK0) | k1_xboole_0 = X0) )),
% 1.17/0.52    inference(superposition,[],[f78,f53])).
% 1.17/0.52  fof(f53,plain,(
% 1.17/0.52    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 1.17/0.52    inference(cnf_transformation,[],[f27])).
% 1.17/0.52  fof(f27,plain,(
% 1.17/0.52    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))) | k1_xboole_0 = X0)),
% 1.17/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f26])).
% 1.17/0.52  fof(f26,plain,(
% 1.17/0.52    ! [X1,X0] : (? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 1.17/0.52    introduced(choice_axiom,[])).
% 1.17/0.52  fof(f20,plain,(
% 1.17/0.52    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 1.17/0.52    inference(ennf_transformation,[],[f12])).
% 1.17/0.52  fof(f12,axiom,(
% 1.17/0.52    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 1.17/0.52  fof(f78,plain,(
% 1.17/0.52    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0 | ~r2_hidden(X1,sK0)) )),
% 1.17/0.52    inference(resolution,[],[f77,f67])).
% 1.17/0.52  fof(f67,plain,(
% 1.17/0.52    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f40])).
% 1.17/0.52  fof(f40,plain,(
% 1.17/0.52    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.17/0.52    inference(nnf_transformation,[],[f5])).
% 1.17/0.52  fof(f5,axiom,(
% 1.17/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.17/0.52  fof(f77,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),sK0) | sK1 != k1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.17/0.52    inference(subsumption_resolution,[],[f76,f51])).
% 1.17/0.52  fof(f51,plain,(
% 1.17/0.52    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.17/0.52    inference(cnf_transformation,[],[f27])).
% 1.17/0.52  fof(f76,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),sK0) | sK1 != k1_relat_1(sK2(X0,X1)) | ~v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.17/0.52    inference(subsumption_resolution,[],[f71,f52])).
% 1.17/0.52  fof(f52,plain,(
% 1.17/0.52    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.17/0.52    inference(cnf_transformation,[],[f27])).
% 1.17/0.52  fof(f71,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),sK0) | sK1 != k1_relat_1(sK2(X0,X1)) | ~v1_funct_1(sK2(X0,X1)) | ~v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.17/0.52    inference(superposition,[],[f42,f54])).
% 1.17/0.52  fof(f54,plain,(
% 1.17/0.52    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.17/0.52    inference(cnf_transformation,[],[f27])).
% 1.17/0.52  fof(f42,plain,(
% 1.17/0.52    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f25])).
% 1.17/0.52  fof(f405,plain,(
% 1.17/0.52    ( ! [X1] : (r2_hidden(sK5(k1_xboole_0,X1),X1) | k1_xboole_0 = sK1 | k1_xboole_0 = X1) )),
% 1.17/0.52    inference(forward_demodulation,[],[f389,f45])).
% 1.17/0.52  fof(f45,plain,(
% 1.17/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.17/0.52    inference(cnf_transformation,[],[f8])).
% 1.17/0.52  fof(f8,axiom,(
% 1.17/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.17/0.52  fof(f389,plain,(
% 1.17/0.52    ( ! [X1] : (k1_xboole_0 = sK1 | k2_relat_1(k1_xboole_0) = X1 | r2_hidden(sK5(k1_xboole_0,X1),X1)) )),
% 1.17/0.52    inference(resolution,[],[f387,f64])).
% 1.17/0.52  fof(f64,plain,(
% 1.17/0.52    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f39])).
% 1.17/0.52  fof(f39,plain,(
% 1.17/0.52    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.17/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f35,f38,f37,f36])).
% 1.17/0.52  fof(f36,plain,(
% 1.17/0.52    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 1.17/0.52    introduced(choice_axiom,[])).
% 1.17/0.52  fof(f37,plain,(
% 1.17/0.52    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0))),
% 1.17/0.52    introduced(choice_axiom,[])).
% 1.17/0.52  fof(f38,plain,(
% 1.17/0.52    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0))),
% 1.17/0.52    introduced(choice_axiom,[])).
% 1.17/0.52  fof(f35,plain,(
% 1.17/0.52    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.17/0.52    inference(rectify,[],[f34])).
% 1.17/0.52  fof(f34,plain,(
% 1.17/0.52    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.17/0.52    inference(nnf_transformation,[],[f7])).
% 1.17/0.52  fof(f7,axiom,(
% 1.17/0.52    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 1.17/0.52  fof(f387,plain,(
% 1.17/0.52    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0) | k1_xboole_0 = sK1) )),
% 1.17/0.52    inference(forward_demodulation,[],[f378,f45])).
% 1.17/0.52  fof(f378,plain,(
% 1.17/0.52    ( ! [X4] : (k1_xboole_0 = sK1 | ~r2_hidden(X4,k2_relat_1(k1_xboole_0))) )),
% 1.17/0.52    inference(resolution,[],[f354,f43])).
% 1.17/0.52  fof(f43,plain,(
% 1.17/0.52    v1_xboole_0(k1_xboole_0)),
% 1.17/0.52    inference(cnf_transformation,[],[f2])).
% 1.17/0.52  fof(f2,axiom,(
% 1.17/0.52    v1_xboole_0(k1_xboole_0)),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.17/0.52  fof(f354,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~v1_xboole_0(X0) | k1_xboole_0 = sK1 | ~r2_hidden(X1,k2_relat_1(X0))) )),
% 1.17/0.52    inference(resolution,[],[f343,f55])).
% 1.17/0.52  fof(f55,plain,(
% 1.17/0.52    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f31])).
% 1.17/0.52  fof(f31,plain,(
% 1.17/0.52    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.17/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 1.17/0.52  fof(f30,plain,(
% 1.17/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.17/0.52    introduced(choice_axiom,[])).
% 1.17/0.52  fof(f29,plain,(
% 1.17/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.17/0.52    inference(rectify,[],[f28])).
% 1.17/0.52  fof(f28,plain,(
% 1.17/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.17/0.52    inference(nnf_transformation,[],[f1])).
% 1.17/0.52  fof(f1,axiom,(
% 1.17/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.17/0.52  fof(f343,plain,(
% 1.17/0.52    ( ! [X5] : (v1_xboole_0(k2_relat_1(X5)) | k1_xboole_0 = sK1 | ~v1_xboole_0(X5)) )),
% 1.17/0.52    inference(resolution,[],[f326,f55])).
% 1.17/0.52  fof(f326,plain,(
% 1.17/0.52    ( ! [X11] : (r2_hidden(sK5(sK0,X11),X11) | k1_xboole_0 = sK1 | v1_xboole_0(k2_relat_1(X11))) )),
% 1.17/0.52    inference(resolution,[],[f308,f56])).
% 1.17/0.52  fof(f56,plain,(
% 1.17/0.52    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f31])).
% 1.17/0.52  fof(f308,plain,(
% 1.17/0.52    ( ! [X8,X7] : (~r2_hidden(X8,k2_relat_1(X7)) | r2_hidden(sK5(sK0,X7),X7) | k1_xboole_0 = sK1) )),
% 1.17/0.52    inference(resolution,[],[f304,f69])).
% 1.17/0.52  fof(f69,plain,(
% 1.17/0.52    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 1.17/0.52    inference(equality_resolution,[],[f62])).
% 1.17/0.52  fof(f62,plain,(
% 1.17/0.52    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 1.17/0.52    inference(cnf_transformation,[],[f39])).
% 1.17/0.52  fof(f304,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_xboole_0 = sK1 | r2_hidden(sK5(sK0,X1),X1)) )),
% 1.17/0.52    inference(equality_resolution,[],[f103])).
% 1.17/0.52  fof(f103,plain,(
% 1.17/0.52    ( ! [X2,X0,X1] : (sK1 != X2 | ~r2_hidden(X1,X0) | k1_xboole_0 = X2 | r2_hidden(sK5(sK0,X0),X0)) )),
% 1.17/0.52    inference(subsumption_resolution,[],[f100,f80])).
% 1.17/0.52  fof(f100,plain,(
% 1.17/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X1,X0) | sK1 != X2 | k1_xboole_0 = X2 | r2_hidden(k4_tarski(sK6(sK0,X0),sK5(sK0,X0)),sK0) | r2_hidden(sK5(sK0,X0),X0)) )),
% 1.17/0.52    inference(superposition,[],[f83,f64])).
% 1.17/0.52  fof(f83,plain,(
% 1.17/0.52    ( ! [X4,X5] : (~r2_hidden(X5,k2_relat_1(sK0)) | sK1 != X4 | k1_xboole_0 = X4) )),
% 1.17/0.52    inference(resolution,[],[f80,f69])).
% 1.17/0.52  fof(f75,plain,(
% 1.17/0.52    k1_xboole_0 != sK1 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.17/0.52    inference(forward_demodulation,[],[f74,f44])).
% 1.17/0.52  fof(f44,plain,(
% 1.17/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.17/0.52    inference(cnf_transformation,[],[f8])).
% 1.17/0.52  fof(f74,plain,(
% 1.17/0.52    k1_relat_1(k1_xboole_0) != sK1 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.17/0.52    inference(subsumption_resolution,[],[f70,f46])).
% 1.17/0.52  fof(f46,plain,(
% 1.17/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f3])).
% 1.17/0.52  fof(f3,axiom,(
% 1.17/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.17/0.52  fof(f70,plain,(
% 1.17/0.52    ~r1_tarski(k1_xboole_0,sK0) | k1_relat_1(k1_xboole_0) != sK1 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.17/0.52    inference(superposition,[],[f42,f45])).
% 1.17/0.52  % SZS output end Proof for theBenchmark
% 1.17/0.52  % (25377)------------------------------
% 1.17/0.52  % (25377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.52  % (25377)Termination reason: Refutation
% 1.17/0.52  
% 1.17/0.52  % (25377)Memory used [KB]: 2046
% 1.17/0.52  % (25377)Time elapsed: 0.092 s
% 1.17/0.52  % (25377)------------------------------
% 1.17/0.52  % (25377)------------------------------
% 1.17/0.52  % (25359)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.17/0.52  % (25353)Success in time 0.154 s
%------------------------------------------------------------------------------
