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
% DateTime   : Thu Dec  3 12:51:57 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 183 expanded)
%              Number of leaves         :   17 (  56 expanded)
%              Depth                    :   17
%              Number of atoms          :  334 ( 938 expanded)
%              Number of equality atoms :  165 ( 435 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f210,plain,(
    $false ),
    inference(global_subsumption,[],[f161,f166])).

fof(f166,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_funct_1(sK2(sK1),sK3(k1_xboole_0,sK1))) ),
    inference(superposition,[],[f45,f143])).

fof(f143,plain,(
    ! [X0] : k1_funct_1(sK2(sK1),sK3(k1_xboole_0,sK1)) = X0 ),
    inference(subsumption_resolution,[],[f142,f38])).

fof(f38,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_xboole_0 != sK1
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK1
            | k1_relat_1(X1) != sK1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k1_relat_1(X2) != X0
                | k1_relat_1(X1) != X0
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
   => ( k1_xboole_0 != sK1
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK1
              | k1_relat_1(X1) != sK1
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

fof(f142,plain,(
    ! [X0] :
      ( k1_funct_1(sK2(sK1),sK3(k1_xboole_0,sK1)) = X0
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f138,f126])).

fof(f126,plain,(
    ! [X0] : sK2(sK1) = sK6(sK1,X0) ),
    inference(equality_resolution,[],[f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK6(X0,X1) = sK2(sK1) ) ),
    inference(equality_resolution,[],[f121])).

fof(f121,plain,(
    ! [X4,X5,X3] :
      ( sK1 != X5
      | sK6(X3,X4) = sK2(X5)
      | sK1 != X3 ) ),
    inference(subsumption_resolution,[],[f120,f54])).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK6(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK6(X0,X1)) = X0
      & v1_funct_1(sK6(X0,X1))
      & v1_relat_1(sK6(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f14,f29])).

fof(f29,plain,(
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

fof(f14,plain,(
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

fof(f120,plain,(
    ! [X4,X5,X3] :
      ( sK1 != X3
      | sK6(X3,X4) = sK2(X5)
      | sK1 != X5
      | ~ v1_relat_1(sK6(X3,X4)) ) ),
    inference(subsumption_resolution,[],[f117,f55])).

fof(f55,plain,(
    ! [X0,X1] : v1_funct_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f117,plain,(
    ! [X4,X5,X3] :
      ( sK1 != X3
      | sK6(X3,X4) = sK2(X5)
      | sK1 != X5
      | ~ v1_funct_1(sK6(X3,X4))
      | ~ v1_relat_1(sK6(X3,X4)) ) ),
    inference(superposition,[],[f112,f56])).

fof(f56,plain,(
    ! [X0,X1] : k1_relat_1(sK6(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f30])).

fof(f112,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X2) != sK1
      | sK2(X1) = X2
      | sK1 != X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f111,f41])).

fof(f41,plain,(
    ! [X0] : v1_relat_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK2(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK2(X0)) = X0
      & v1_funct_1(sK2(X0))
      & v1_relat_1(sK2(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK2(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK2(X0)) = X0
        & v1_funct_1(sK2(X0))
        & v1_relat_1(sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f111,plain,(
    ! [X2,X1] :
      ( sK1 != X1
      | sK2(X1) = X2
      | k1_relat_1(X2) != sK1
      | ~ v1_relat_1(sK2(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f109,f42])).

fof(f42,plain,(
    ! [X0] : v1_funct_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f109,plain,(
    ! [X2,X1] :
      ( sK1 != X1
      | sK2(X1) = X2
      | k1_relat_1(X2) != sK1
      | ~ v1_funct_1(sK2(X1))
      | ~ v1_relat_1(sK2(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f37,f43])).

fof(f43,plain,(
    ! [X0] : k1_relat_1(sK2(X0)) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X2) != sK1
      | X1 = X2
      | k1_relat_1(X1) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f138,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK6(X0,X1),sK3(k1_xboole_0,X0)) = X1
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f137,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(sK6(X0,X1),X3) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f137,plain,(
    ! [X12] :
      ( r2_hidden(sK3(k1_xboole_0,X12),X12)
      | k1_xboole_0 = X12 ) ),
    inference(forward_demodulation,[],[f135,f40])).

fof(f40,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f135,plain,(
    ! [X12] :
      ( k2_relat_1(k1_xboole_0) = X12
      | r2_hidden(sK3(k1_xboole_0,X12),X12) ) ),
    inference(resolution,[],[f49,f77])).

fof(f77,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f45,f70])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
      | k2_relat_1(X0) = X1
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f25,f24,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f45,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f161,plain,(
    ! [X1] : r2_hidden(X1,k1_funct_1(sK2(sK1),sK3(k1_xboole_0,sK1))) ),
    inference(superposition,[],[f80,f143])).

fof(f80,plain,(
    ! [X2,X3] : r2_hidden(X2,k1_enumset1(X3,X3,X2)) ),
    inference(resolution,[],[f74,f72])).

fof(f72,plain,(
    ! [X4,X2,X1] :
      ( ~ sP0(X4,X1,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( sK7(X0,X1,X2) != X0
              & sK7(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( sK7(X0,X1,X2) = X0
            | sK7(X0,X1,X2) = X1
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK7(X0,X1,X2) != X0
            & sK7(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( sK7(X0,X1,X2) = X0
          | sK7(X0,X1,X2) = X1
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f74,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_enumset1(X0,X0,X1)) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f64,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f15])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
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
% 0.13/0.35  % DateTime   : Tue Dec  1 18:22:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.23/0.54  % (18272)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.23/0.55  % (18280)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.23/0.56  % (18279)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.23/0.56  % (18296)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.50/0.56  % (18296)Refutation not found, incomplete strategy% (18296)------------------------------
% 1.50/0.56  % (18296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (18296)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (18296)Memory used [KB]: 6268
% 1.50/0.57  % (18296)Time elapsed: 0.137 s
% 1.50/0.57  % (18296)------------------------------
% 1.50/0.57  % (18296)------------------------------
% 1.50/0.57  % (18297)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.50/0.57  % (18275)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.50/0.57  % (18273)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.50/0.57  % (18274)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.50/0.58  % (18289)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.50/0.58  % (18281)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.50/0.58  % (18271)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.50/0.58  % (18293)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.50/0.58  % (18283)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.50/0.58  % (18281)Refutation not found, incomplete strategy% (18281)------------------------------
% 1.50/0.58  % (18281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.58  % (18283)Refutation not found, incomplete strategy% (18283)------------------------------
% 1.50/0.58  % (18283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.58  % (18283)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.58  
% 1.50/0.58  % (18283)Memory used [KB]: 1791
% 1.50/0.58  % (18283)Time elapsed: 0.158 s
% 1.50/0.58  % (18283)------------------------------
% 1.50/0.58  % (18283)------------------------------
% 1.50/0.59  % (18291)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.50/0.59  % (18281)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.59  
% 1.50/0.59  % (18281)Memory used [KB]: 10618
% 1.50/0.59  % (18281)Time elapsed: 0.151 s
% 1.50/0.59  % (18281)------------------------------
% 1.50/0.59  % (18281)------------------------------
% 1.50/0.59  % (18284)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.50/0.59  % (18276)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.50/0.59  % (18269)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.50/0.59  % (18287)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.50/0.60  % (18285)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.50/0.60  % (18292)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.50/0.60  % (18298)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.50/0.60  % (18298)Refutation not found, incomplete strategy% (18298)------------------------------
% 1.50/0.60  % (18298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.60  % (18298)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.60  
% 1.50/0.60  % (18298)Memory used [KB]: 1663
% 1.50/0.60  % (18298)Time elapsed: 0.003 s
% 1.50/0.60  % (18298)------------------------------
% 1.50/0.60  % (18298)------------------------------
% 1.50/0.60  % (18275)Refutation found. Thanks to Tanya!
% 1.50/0.60  % SZS status Theorem for theBenchmark
% 1.50/0.60  % SZS output start Proof for theBenchmark
% 1.50/0.60  fof(f210,plain,(
% 1.50/0.60    $false),
% 1.50/0.60    inference(global_subsumption,[],[f161,f166])).
% 1.50/0.60  fof(f166,plain,(
% 1.50/0.60    ( ! [X0] : (~r2_hidden(X0,k1_funct_1(sK2(sK1),sK3(k1_xboole_0,sK1)))) )),
% 1.50/0.60    inference(superposition,[],[f45,f143])).
% 1.50/0.60  fof(f143,plain,(
% 1.50/0.60    ( ! [X0] : (k1_funct_1(sK2(sK1),sK3(k1_xboole_0,sK1)) = X0) )),
% 1.50/0.60    inference(subsumption_resolution,[],[f142,f38])).
% 1.50/0.60  fof(f38,plain,(
% 1.50/0.60    k1_xboole_0 != sK1),
% 1.50/0.60    inference(cnf_transformation,[],[f18])).
% 1.50/0.60  fof(f18,plain,(
% 1.50/0.60    k1_xboole_0 != sK1 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK1 | k1_relat_1(X1) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.50/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f17])).
% 1.50/0.60  fof(f17,plain,(
% 1.50/0.60    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK1 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK1 | k1_relat_1(X1) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.50/0.60    introduced(choice_axiom,[])).
% 1.50/0.60  fof(f12,plain,(
% 1.50/0.60    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.50/0.60    inference(flattening,[],[f11])).
% 1.50/0.60  fof(f11,plain,(
% 1.50/0.60    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 1.50/0.60    inference(ennf_transformation,[],[f10])).
% 1.50/0.60  fof(f10,negated_conjecture,(
% 1.50/0.60    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 1.50/0.60    inference(negated_conjecture,[],[f9])).
% 1.50/0.60  fof(f9,conjecture,(
% 1.50/0.60    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).
% 1.50/0.60  fof(f142,plain,(
% 1.50/0.60    ( ! [X0] : (k1_funct_1(sK2(sK1),sK3(k1_xboole_0,sK1)) = X0 | k1_xboole_0 = sK1) )),
% 1.50/0.60    inference(superposition,[],[f138,f126])).
% 1.50/0.60  fof(f126,plain,(
% 1.50/0.60    ( ! [X0] : (sK2(sK1) = sK6(sK1,X0)) )),
% 1.50/0.60    inference(equality_resolution,[],[f125])).
% 1.50/0.60  fof(f125,plain,(
% 1.50/0.60    ( ! [X0,X1] : (sK1 != X0 | sK6(X0,X1) = sK2(sK1)) )),
% 1.50/0.60    inference(equality_resolution,[],[f121])).
% 1.50/0.60  fof(f121,plain,(
% 1.50/0.60    ( ! [X4,X5,X3] : (sK1 != X5 | sK6(X3,X4) = sK2(X5) | sK1 != X3) )),
% 1.50/0.60    inference(subsumption_resolution,[],[f120,f54])).
% 1.50/0.60  fof(f54,plain,(
% 1.50/0.60    ( ! [X0,X1] : (v1_relat_1(sK6(X0,X1))) )),
% 1.50/0.60    inference(cnf_transformation,[],[f30])).
% 1.50/0.60  fof(f30,plain,(
% 1.50/0.60    ! [X0,X1] : (! [X3] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK6(X0,X1)) = X0 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1)))),
% 1.50/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f14,f29])).
% 1.50/0.60  fof(f29,plain,(
% 1.50/0.60    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK6(X0,X1)) = X0 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1))))),
% 1.50/0.60    introduced(choice_axiom,[])).
% 1.50/0.60  fof(f14,plain,(
% 1.50/0.60    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.50/0.60    inference(ennf_transformation,[],[f7])).
% 1.50/0.60  fof(f7,axiom,(
% 1.50/0.60    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 1.50/0.60  fof(f120,plain,(
% 1.50/0.60    ( ! [X4,X5,X3] : (sK1 != X3 | sK6(X3,X4) = sK2(X5) | sK1 != X5 | ~v1_relat_1(sK6(X3,X4))) )),
% 1.50/0.60    inference(subsumption_resolution,[],[f117,f55])).
% 1.50/0.60  fof(f55,plain,(
% 1.50/0.60    ( ! [X0,X1] : (v1_funct_1(sK6(X0,X1))) )),
% 1.50/0.60    inference(cnf_transformation,[],[f30])).
% 1.50/0.60  fof(f117,plain,(
% 1.50/0.60    ( ! [X4,X5,X3] : (sK1 != X3 | sK6(X3,X4) = sK2(X5) | sK1 != X5 | ~v1_funct_1(sK6(X3,X4)) | ~v1_relat_1(sK6(X3,X4))) )),
% 1.50/0.60    inference(superposition,[],[f112,f56])).
% 1.50/0.60  fof(f56,plain,(
% 1.50/0.60    ( ! [X0,X1] : (k1_relat_1(sK6(X0,X1)) = X0) )),
% 1.50/0.60    inference(cnf_transformation,[],[f30])).
% 1.50/0.60  fof(f112,plain,(
% 1.50/0.60    ( ! [X2,X1] : (k1_relat_1(X2) != sK1 | sK2(X1) = X2 | sK1 != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.50/0.60    inference(subsumption_resolution,[],[f111,f41])).
% 1.50/0.60  fof(f41,plain,(
% 1.50/0.60    ( ! [X0] : (v1_relat_1(sK2(X0))) )),
% 1.50/0.60    inference(cnf_transformation,[],[f20])).
% 1.50/0.60  fof(f20,plain,(
% 1.50/0.60    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK2(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK2(X0)) = X0 & v1_funct_1(sK2(X0)) & v1_relat_1(sK2(X0)))),
% 1.50/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f19])).
% 1.50/0.60  fof(f19,plain,(
% 1.50/0.60    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK2(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK2(X0)) = X0 & v1_funct_1(sK2(X0)) & v1_relat_1(sK2(X0))))),
% 1.50/0.60    introduced(choice_axiom,[])).
% 1.50/0.60  fof(f13,plain,(
% 1.50/0.60    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.50/0.60    inference(ennf_transformation,[],[f8])).
% 1.50/0.60  fof(f8,axiom,(
% 1.50/0.60    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 1.50/0.60  fof(f111,plain,(
% 1.50/0.60    ( ! [X2,X1] : (sK1 != X1 | sK2(X1) = X2 | k1_relat_1(X2) != sK1 | ~v1_relat_1(sK2(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.50/0.60    inference(subsumption_resolution,[],[f109,f42])).
% 1.50/0.60  fof(f42,plain,(
% 1.50/0.60    ( ! [X0] : (v1_funct_1(sK2(X0))) )),
% 1.50/0.60    inference(cnf_transformation,[],[f20])).
% 1.50/0.60  fof(f109,plain,(
% 1.50/0.60    ( ! [X2,X1] : (sK1 != X1 | sK2(X1) = X2 | k1_relat_1(X2) != sK1 | ~v1_funct_1(sK2(X1)) | ~v1_relat_1(sK2(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.50/0.60    inference(superposition,[],[f37,f43])).
% 1.50/0.60  fof(f43,plain,(
% 1.50/0.60    ( ! [X0] : (k1_relat_1(sK2(X0)) = X0) )),
% 1.50/0.60    inference(cnf_transformation,[],[f20])).
% 1.50/0.60  fof(f37,plain,(
% 1.50/0.60    ( ! [X2,X1] : (k1_relat_1(X2) != sK1 | X1 = X2 | k1_relat_1(X1) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f18])).
% 1.50/0.60  fof(f138,plain,(
% 1.50/0.60    ( ! [X0,X1] : (k1_funct_1(sK6(X0,X1),sK3(k1_xboole_0,X0)) = X1 | k1_xboole_0 = X0) )),
% 1.50/0.60    inference(resolution,[],[f137,f57])).
% 1.50/0.60  fof(f57,plain,(
% 1.50/0.60    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | k1_funct_1(sK6(X0,X1),X3) = X1) )),
% 1.50/0.60    inference(cnf_transformation,[],[f30])).
% 1.50/0.60  fof(f137,plain,(
% 1.50/0.60    ( ! [X12] : (r2_hidden(sK3(k1_xboole_0,X12),X12) | k1_xboole_0 = X12) )),
% 1.50/0.60    inference(forward_demodulation,[],[f135,f40])).
% 1.50/0.60  fof(f40,plain,(
% 1.50/0.60    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.50/0.60    inference(cnf_transformation,[],[f6])).
% 1.50/0.60  fof(f6,axiom,(
% 1.50/0.60    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.50/0.60  fof(f135,plain,(
% 1.50/0.60    ( ! [X12] : (k2_relat_1(k1_xboole_0) = X12 | r2_hidden(sK3(k1_xboole_0,X12),X12)) )),
% 1.50/0.60    inference(resolution,[],[f49,f77])).
% 1.50/0.60  fof(f77,plain,(
% 1.50/0.60    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.50/0.60    inference(superposition,[],[f45,f70])).
% 1.50/0.60  fof(f70,plain,(
% 1.50/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.50/0.60    inference(equality_resolution,[],[f53])).
% 1.50/0.60  fof(f53,plain,(
% 1.50/0.60    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.50/0.60    inference(cnf_transformation,[],[f28])).
% 1.50/0.60  fof(f28,plain,(
% 1.50/0.60    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.50/0.60    inference(flattening,[],[f27])).
% 1.50/0.60  fof(f27,plain,(
% 1.50/0.60    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.50/0.60    inference(nnf_transformation,[],[f3])).
% 1.50/0.60  fof(f3,axiom,(
% 1.50/0.60    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.50/0.60  fof(f49,plain,(
% 1.50/0.60    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | k2_relat_1(X0) = X1 | r2_hidden(sK3(X0,X1),X1)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f26])).
% 1.50/0.60  fof(f26,plain,(
% 1.50/0.60    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.50/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f25,f24,f23])).
% 1.50/0.60  fof(f23,plain,(
% 1.50/0.60    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.50/0.60    introduced(choice_axiom,[])).
% 1.50/0.60  fof(f24,plain,(
% 1.50/0.60    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0))),
% 1.50/0.60    introduced(choice_axiom,[])).
% 1.50/0.60  fof(f25,plain,(
% 1.50/0.60    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 1.50/0.60    introduced(choice_axiom,[])).
% 1.50/0.60  fof(f22,plain,(
% 1.50/0.60    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.50/0.60    inference(rectify,[],[f21])).
% 1.50/0.60  fof(f21,plain,(
% 1.50/0.60    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.50/0.60    inference(nnf_transformation,[],[f5])).
% 1.50/0.60  fof(f5,axiom,(
% 1.50/0.60    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 1.50/0.60  fof(f45,plain,(
% 1.50/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.50/0.60    inference(cnf_transformation,[],[f4])).
% 1.50/0.60  fof(f4,axiom,(
% 1.50/0.60    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.50/0.60  fof(f161,plain,(
% 1.50/0.60    ( ! [X1] : (r2_hidden(X1,k1_funct_1(sK2(sK1),sK3(k1_xboole_0,sK1)))) )),
% 1.50/0.60    inference(superposition,[],[f80,f143])).
% 1.50/0.60  fof(f80,plain,(
% 1.50/0.60    ( ! [X2,X3] : (r2_hidden(X2,k1_enumset1(X3,X3,X2))) )),
% 1.50/0.60    inference(resolution,[],[f74,f72])).
% 1.50/0.60  fof(f72,plain,(
% 1.50/0.60    ( ! [X4,X2,X1] : (~sP0(X4,X1,X2) | r2_hidden(X4,X2)) )),
% 1.50/0.60    inference(equality_resolution,[],[f60])).
% 1.50/0.60  fof(f60,plain,(
% 1.50/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | ~sP0(X0,X1,X2)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f35])).
% 1.50/0.60  fof(f35,plain,(
% 1.50/0.60    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK7(X0,X1,X2) != X0 & sK7(X0,X1,X2) != X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sK7(X0,X1,X2) = X0 | sK7(X0,X1,X2) = X1 | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.50/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f33,f34])).
% 1.50/0.60  fof(f34,plain,(
% 1.50/0.60    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK7(X0,X1,X2) != X0 & sK7(X0,X1,X2) != X1) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sK7(X0,X1,X2) = X0 | sK7(X0,X1,X2) = X1 | r2_hidden(sK7(X0,X1,X2),X2))))),
% 1.50/0.60    introduced(choice_axiom,[])).
% 1.50/0.60  fof(f33,plain,(
% 1.50/0.60    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.50/0.60    inference(rectify,[],[f32])).
% 1.50/0.60  fof(f32,plain,(
% 1.50/0.60    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.50/0.60    inference(flattening,[],[f31])).
% 1.50/0.60  fof(f31,plain,(
% 1.50/0.60    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.50/0.60    inference(nnf_transformation,[],[f15])).
% 1.50/0.60  fof(f15,plain,(
% 1.50/0.60    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.50/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.50/0.60  fof(f74,plain,(
% 1.50/0.60    ( ! [X0,X1] : (sP0(X1,X0,k1_enumset1(X0,X0,X1))) )),
% 1.50/0.60    inference(equality_resolution,[],[f67])).
% 1.50/0.60  fof(f67,plain,(
% 1.50/0.60    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 1.50/0.60    inference(definition_unfolding,[],[f64,f46])).
% 1.50/0.60  fof(f46,plain,(
% 1.50/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f2])).
% 1.50/0.60  fof(f2,axiom,(
% 1.50/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.50/0.60  fof(f64,plain,(
% 1.50/0.60    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 1.50/0.60    inference(cnf_transformation,[],[f36])).
% 1.50/0.60  fof(f36,plain,(
% 1.50/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 1.50/0.60    inference(nnf_transformation,[],[f16])).
% 1.50/0.60  fof(f16,plain,(
% 1.50/0.60    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.50/0.60    inference(definition_folding,[],[f1,f15])).
% 1.50/0.60  fof(f1,axiom,(
% 1.50/0.60    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.50/0.60  % SZS output end Proof for theBenchmark
% 1.50/0.60  % (18275)------------------------------
% 1.50/0.60  % (18275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.60  % (18275)Termination reason: Refutation
% 1.50/0.60  
% 1.50/0.60  % (18275)Memory used [KB]: 10874
% 1.50/0.60  % (18275)Time elapsed: 0.138 s
% 1.50/0.60  % (18275)------------------------------
% 1.50/0.60  % (18275)------------------------------
% 1.50/0.60  % (18270)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.50/0.60  % (18270)Refutation not found, incomplete strategy% (18270)------------------------------
% 1.50/0.60  % (18270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.60  % (18270)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.60  
% 1.50/0.60  % (18270)Memory used [KB]: 1663
% 1.50/0.60  % (18270)Time elapsed: 0.172 s
% 1.50/0.60  % (18270)------------------------------
% 1.50/0.60  % (18270)------------------------------
% 1.50/0.60  % (18268)Success in time 0.234 s
%------------------------------------------------------------------------------
