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
% DateTime   : Thu Dec  3 12:51:55 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   80 (1199 expanded)
%              Number of leaves         :   12 ( 370 expanded)
%              Depth                    :   30
%              Number of atoms          :  352 (6493 expanded)
%              Number of equality atoms :  163 (2832 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f450,plain,(
    $false ),
    inference(subsumption_resolution,[],[f430,f300])).

fof(f300,plain,(
    ! [X0,X1] : X0 = X1 ),
    inference(superposition,[],[f295,f295])).

fof(f295,plain,(
    ! [X0] : k1_funct_1(sK4(sK0),sK3(sK4(sK0),np__1)) = X0 ),
    inference(subsumption_resolution,[],[f293,f35])).

fof(f35,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k1_xboole_0 != sK0
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK0
            | k1_relat_1(X1) != sK0
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f20])).

fof(f20,plain,
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
   => ( k1_xboole_0 != sK0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK0
              | k1_relat_1(X1) != sK0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f293,plain,(
    ! [X0] :
      ( k1_funct_1(sK4(sK0),sK3(sK4(sK0),np__1)) = X0
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f238,f141])).

fof(f141,plain,(
    ! [X0] : sK4(sK0) = sK5(sK0,X0) ),
    inference(equality_resolution,[],[f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK5(X0,X1) = sK4(sK0) ) ),
    inference(equality_resolution,[],[f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X2
      | sK0 != X0
      | sK5(X0,X1) = sK4(X2) ) ),
    inference(superposition,[],[f133,f57])).

fof(f57,plain,(
    ! [X0,X1] : k1_relat_1(sK5(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK5(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK5(X0,X1)) = X0
      & v1_funct_1(sK5(X0,X1))
      & v1_relat_1(sK5(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f32])).

fof(f32,plain,(
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

fof(f19,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f133,plain,(
    ! [X6,X4,X5] :
      ( sK0 != k1_relat_1(sK5(X4,X5))
      | sK0 != X6
      | sK5(X4,X5) = sK4(X6) ) ),
    inference(subsumption_resolution,[],[f130,f55])).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f130,plain,(
    ! [X6,X4,X5] :
      ( sK0 != k1_relat_1(sK5(X4,X5))
      | sK0 != X6
      | ~ v1_relat_1(sK5(X4,X5))
      | sK5(X4,X5) = sK4(X6) ) ),
    inference(resolution,[],[f124,f56])).

fof(f56,plain,(
    ! [X0,X1] : v1_funct_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | k1_relat_1(X0) != sK0
      | sK0 != X1
      | ~ v1_relat_1(X0)
      | sK4(X1) = X0 ) ),
    inference(forward_demodulation,[],[f123,f49])).

fof(f49,plain,(
    ! [X0] : k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X2] :
          ( np__1 = k1_funct_1(sK4(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK4(X0)) = X0
      & v1_funct_1(sK4(X0))
      & v1_relat_1(sK4(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_funct_1(X1,X2) = np__1
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( np__1 = k1_funct_1(sK4(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK4(X0)) = X0
        & v1_funct_1(sK4(X0))
        & v1_relat_1(sK4(X0)) ) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

fof(f123,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != sK0
      | sK0 != k1_relat_1(sK4(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK4(X1) = X0 ) ),
    inference(subsumption_resolution,[],[f120,f47])).

fof(f47,plain,(
    ! [X0] : v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != sK0
      | sK0 != k1_relat_1(sK4(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK4(X1) = X0
      | ~ v1_relat_1(sK4(X1)) ) ),
    inference(resolution,[],[f34,f48])).

fof(f48,plain,(
    ! [X0] : v1_funct_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f34,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X1)
      | k1_relat_1(X2) != sK0
      | k1_relat_1(X1) != sK0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | X1 = X2
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f238,plain,(
    ! [X2,X1] :
      ( k1_funct_1(sK5(X1,X2),sK3(sK4(X1),np__1)) = X2
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f236,f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(sK5(X0,X1),X3) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f236,plain,(
    ! [X1] :
      ( r2_hidden(sK3(sK4(X1),np__1),X1)
      | k1_xboole_0 = X1 ) ),
    inference(forward_demodulation,[],[f235,f49])).

fof(f235,plain,(
    ! [X1] :
      ( k1_xboole_0 = X1
      | r2_hidden(sK3(sK4(X1),np__1),k1_relat_1(sK4(X1))) ) ),
    inference(subsumption_resolution,[],[f234,f47])).

fof(f234,plain,(
    ! [X1] :
      ( k1_xboole_0 = X1
      | r2_hidden(sK3(sK4(X1),np__1),k1_relat_1(sK4(X1)))
      | ~ v1_relat_1(sK4(X1)) ) ),
    inference(subsumption_resolution,[],[f222,f48])).

fof(f222,plain,(
    ! [X1] :
      ( k1_xboole_0 = X1
      | r2_hidden(sK3(sK4(X1),np__1),k1_relat_1(sK4(X1)))
      | ~ v1_funct_1(sK4(X1))
      | ~ v1_relat_1(sK4(X1)) ) ),
    inference(resolution,[],[f218,f62])).

fof(f62,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK1(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ( sK1(X0,X1) = k1_funct_1(X0,sK2(X0,X1))
                  & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X5)) = X5
                    & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f26,f25,f24])).

fof(f24,plain,(
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
              ( k1_funct_1(X0,X3) != sK1(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK1(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK1(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK1(X0,X1) = k1_funct_1(X0,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f218,plain,(
    ! [X0] :
      ( r2_hidden(np__1,k2_relat_1(sK4(X0)))
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(np__1,k2_relat_1(sK4(X0)))
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f216,f199])).

fof(f199,plain,(
    k1_xboole_0 = k2_relat_1(sK4(k1_xboole_0)) ),
    inference(resolution,[],[f177,f65])).

fof(f65,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f51,f63])).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f51,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f177,plain,(
    ! [X22] :
      ( r2_hidden(sK1(sK4(k1_xboole_0),X22),X22)
      | k2_relat_1(sK4(k1_xboole_0)) = X22 ) ),
    inference(resolution,[],[f165,f65])).

fof(f165,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(sK4(X0),X1),X0)
      | r2_hidden(sK1(sK4(X0),X1),X1)
      | k2_relat_1(sK4(X0)) = X1 ) ),
    inference(forward_demodulation,[],[f164,f49])).

fof(f164,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(sK4(X0),X1),k1_relat_1(sK4(X0)))
      | r2_hidden(sK1(sK4(X0),X1),X1)
      | k2_relat_1(sK4(X0)) = X1 ) ),
    inference(subsumption_resolution,[],[f161,f47])).

fof(f161,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(sK4(X0),X1),k1_relat_1(sK4(X0)))
      | r2_hidden(sK1(sK4(X0),X1),X1)
      | k2_relat_1(sK4(X0)) = X1
      | ~ v1_relat_1(sK4(X0)) ) ),
    inference(resolution,[],[f44,f48])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK1(X0,X1),X1)
      | k2_relat_1(X0) = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f216,plain,(
    ! [X0] :
      ( r2_hidden(np__1,k2_relat_1(sK4(X0)))
      | k1_xboole_0 = X0
      | k2_relat_1(sK4(k1_xboole_0)) = X0 ) ),
    inference(subsumption_resolution,[],[f214,f65])).

fof(f214,plain,(
    ! [X0] :
      ( r2_hidden(np__1,k2_relat_1(sK4(X0)))
      | k1_xboole_0 = X0
      | r2_hidden(sK2(sK4(k1_xboole_0),X0),k1_xboole_0)
      | k2_relat_1(sK4(k1_xboole_0)) = X0 ) ),
    inference(resolution,[],[f213,f165])).

fof(f213,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(sK4(k1_xboole_0),X0),X0)
      | r2_hidden(np__1,k2_relat_1(sK4(X0)))
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f212,f49])).

fof(f212,plain,(
    ! [X0] :
      ( r2_hidden(np__1,k2_relat_1(sK4(X0)))
      | ~ r2_hidden(sK1(sK4(k1_xboole_0),X0),k1_relat_1(sK4(X0)))
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f211,f47])).

fof(f211,plain,(
    ! [X0] :
      ( r2_hidden(np__1,k2_relat_1(sK4(X0)))
      | ~ r2_hidden(sK1(sK4(k1_xboole_0),X0),k1_relat_1(sK4(X0)))
      | ~ v1_relat_1(sK4(X0))
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f210,f48])).

fof(f210,plain,(
    ! [X0] :
      ( r2_hidden(np__1,k2_relat_1(sK4(X0)))
      | ~ r2_hidden(sK1(sK4(k1_xboole_0),X0),k1_relat_1(sK4(X0)))
      | ~ v1_funct_1(sK4(X0))
      | ~ v1_relat_1(sK4(X0))
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f60,f209])).

% (3528)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f209,plain,(
    ! [X0] :
      ( np__1 = k1_funct_1(sK4(X0),sK1(sK4(k1_xboole_0),X0))
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f191,f199])).

fof(f191,plain,(
    ! [X0] :
      ( k2_relat_1(sK4(k1_xboole_0)) = X0
      | np__1 = k1_funct_1(sK4(X0),sK1(sK4(k1_xboole_0),X0)) ) ),
    inference(resolution,[],[f177,f50])).

fof(f50,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | np__1 = k1_funct_1(sK4(X0),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f430,plain,(
    ! [X0] : k1_xboole_0 != X0 ),
    inference(superposition,[],[f35,f300])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:42:26 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.54  % (3523)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.55  % (3524)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.55  % (3519)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.55  % (3525)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.55  % (3524)Refutation not found, incomplete strategy% (3524)------------------------------
% 0.22/0.55  % (3524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (3524)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (3524)Memory used [KB]: 6140
% 0.22/0.55  % (3524)Time elapsed: 0.121 s
% 0.22/0.55  % (3524)------------------------------
% 0.22/0.55  % (3524)------------------------------
% 0.22/0.55  % (3519)Refutation not found, incomplete strategy% (3519)------------------------------
% 0.22/0.55  % (3519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (3519)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (3519)Memory used [KB]: 10490
% 0.22/0.55  % (3519)Time elapsed: 0.111 s
% 0.22/0.55  % (3519)------------------------------
% 0.22/0.55  % (3519)------------------------------
% 0.22/0.55  % (3520)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.32/0.56  % (3529)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.32/0.56  % (3522)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.32/0.56  % (3520)Refutation not found, incomplete strategy% (3520)------------------------------
% 1.32/0.56  % (3520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (3520)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.56  
% 1.32/0.56  % (3520)Memory used [KB]: 10618
% 1.32/0.56  % (3520)Time elapsed: 0.123 s
% 1.32/0.56  % (3520)------------------------------
% 1.32/0.56  % (3520)------------------------------
% 1.32/0.56  % (3540)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.32/0.56  % (3525)Refutation not found, incomplete strategy% (3525)------------------------------
% 1.32/0.56  % (3525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (3525)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.56  
% 1.32/0.56  % (3525)Memory used [KB]: 10490
% 1.32/0.56  % (3525)Time elapsed: 0.117 s
% 1.32/0.56  % (3525)------------------------------
% 1.32/0.56  % (3525)------------------------------
% 1.32/0.56  % (3541)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.32/0.56  % (3539)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.32/0.56  % (3521)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.32/0.57  % (3537)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.32/0.57  % (3538)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.32/0.57  % (3540)Refutation found. Thanks to Tanya!
% 1.32/0.57  % SZS status Theorem for theBenchmark
% 1.32/0.57  % SZS output start Proof for theBenchmark
% 1.32/0.57  fof(f450,plain,(
% 1.32/0.57    $false),
% 1.32/0.57    inference(subsumption_resolution,[],[f430,f300])).
% 1.32/0.57  fof(f300,plain,(
% 1.32/0.57    ( ! [X0,X1] : (X0 = X1) )),
% 1.32/0.57    inference(superposition,[],[f295,f295])).
% 1.32/0.57  fof(f295,plain,(
% 1.32/0.57    ( ! [X0] : (k1_funct_1(sK4(sK0),sK3(sK4(sK0),np__1)) = X0) )),
% 1.32/0.57    inference(subsumption_resolution,[],[f293,f35])).
% 1.32/0.57  fof(f35,plain,(
% 1.32/0.57    k1_xboole_0 != sK0),
% 1.32/0.57    inference(cnf_transformation,[],[f21])).
% 1.32/0.57  fof(f21,plain,(
% 1.32/0.57    k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.32/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f20])).
% 1.32/0.57  fof(f20,plain,(
% 1.32/0.57    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.32/0.57    introduced(choice_axiom,[])).
% 1.32/0.57  fof(f13,plain,(
% 1.32/0.57    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.32/0.57    inference(flattening,[],[f12])).
% 1.32/0.57  fof(f12,plain,(
% 1.32/0.57    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 1.32/0.57    inference(ennf_transformation,[],[f11])).
% 1.32/0.57  fof(f11,negated_conjecture,(
% 1.32/0.57    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 1.32/0.57    inference(negated_conjecture,[],[f10])).
% 1.32/0.57  fof(f10,conjecture,(
% 1.32/0.57    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).
% 1.32/0.57  fof(f293,plain,(
% 1.32/0.57    ( ! [X0] : (k1_funct_1(sK4(sK0),sK3(sK4(sK0),np__1)) = X0 | k1_xboole_0 = sK0) )),
% 1.32/0.57    inference(superposition,[],[f238,f141])).
% 1.32/0.57  fof(f141,plain,(
% 1.32/0.57    ( ! [X0] : (sK4(sK0) = sK5(sK0,X0)) )),
% 1.32/0.57    inference(equality_resolution,[],[f140])).
% 1.32/0.57  fof(f140,plain,(
% 1.32/0.57    ( ! [X0,X1] : (sK0 != X0 | sK5(X0,X1) = sK4(sK0)) )),
% 1.32/0.57    inference(equality_resolution,[],[f139])).
% 1.32/0.57  fof(f139,plain,(
% 1.32/0.57    ( ! [X2,X0,X1] : (sK0 != X2 | sK0 != X0 | sK5(X0,X1) = sK4(X2)) )),
% 1.32/0.57    inference(superposition,[],[f133,f57])).
% 1.32/0.57  fof(f57,plain,(
% 1.32/0.57    ( ! [X0,X1] : (k1_relat_1(sK5(X0,X1)) = X0) )),
% 1.32/0.57    inference(cnf_transformation,[],[f33])).
% 1.32/0.57  fof(f33,plain,(
% 1.32/0.57    ! [X0,X1] : (! [X3] : (k1_funct_1(sK5(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK5(X0,X1)) = X0 & v1_funct_1(sK5(X0,X1)) & v1_relat_1(sK5(X0,X1)))),
% 1.32/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f32])).
% 1.32/0.57  fof(f32,plain,(
% 1.32/0.57    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK5(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK5(X0,X1)) = X0 & v1_funct_1(sK5(X0,X1)) & v1_relat_1(sK5(X0,X1))))),
% 1.32/0.57    introduced(choice_axiom,[])).
% 1.32/0.57  fof(f19,plain,(
% 1.32/0.57    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.32/0.57    inference(ennf_transformation,[],[f8])).
% 1.32/0.57  fof(f8,axiom,(
% 1.32/0.57    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 1.32/0.57  fof(f133,plain,(
% 1.32/0.57    ( ! [X6,X4,X5] : (sK0 != k1_relat_1(sK5(X4,X5)) | sK0 != X6 | sK5(X4,X5) = sK4(X6)) )),
% 1.32/0.57    inference(subsumption_resolution,[],[f130,f55])).
% 1.32/0.57  fof(f55,plain,(
% 1.32/0.57    ( ! [X0,X1] : (v1_relat_1(sK5(X0,X1))) )),
% 1.32/0.57    inference(cnf_transformation,[],[f33])).
% 1.32/0.57  fof(f130,plain,(
% 1.32/0.57    ( ! [X6,X4,X5] : (sK0 != k1_relat_1(sK5(X4,X5)) | sK0 != X6 | ~v1_relat_1(sK5(X4,X5)) | sK5(X4,X5) = sK4(X6)) )),
% 1.32/0.57    inference(resolution,[],[f124,f56])).
% 1.32/0.57  fof(f56,plain,(
% 1.32/0.57    ( ! [X0,X1] : (v1_funct_1(sK5(X0,X1))) )),
% 1.32/0.57    inference(cnf_transformation,[],[f33])).
% 1.32/0.57  fof(f124,plain,(
% 1.32/0.57    ( ! [X0,X1] : (~v1_funct_1(X0) | k1_relat_1(X0) != sK0 | sK0 != X1 | ~v1_relat_1(X0) | sK4(X1) = X0) )),
% 1.32/0.57    inference(forward_demodulation,[],[f123,f49])).
% 1.32/0.57  fof(f49,plain,(
% 1.32/0.57    ( ! [X0] : (k1_relat_1(sK4(X0)) = X0) )),
% 1.32/0.57    inference(cnf_transformation,[],[f29])).
% 1.32/0.57  fof(f29,plain,(
% 1.32/0.57    ! [X0] : (! [X2] : (np__1 = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0)))),
% 1.32/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f28])).
% 1.32/0.57  fof(f28,plain,(
% 1.32/0.57    ! [X0] : (? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (np__1 = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0))))),
% 1.32/0.57    introduced(choice_axiom,[])).
% 1.32/0.57  fof(f18,plain,(
% 1.32/0.57    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.32/0.57    inference(ennf_transformation,[],[f9])).
% 1.32/0.57  fof(f9,axiom,(
% 1.32/0.57    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = np__1) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).
% 1.32/0.57  fof(f123,plain,(
% 1.32/0.57    ( ! [X0,X1] : (k1_relat_1(X0) != sK0 | sK0 != k1_relat_1(sK4(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK4(X1) = X0) )),
% 1.32/0.57    inference(subsumption_resolution,[],[f120,f47])).
% 1.32/0.57  fof(f47,plain,(
% 1.32/0.57    ( ! [X0] : (v1_relat_1(sK4(X0))) )),
% 1.32/0.57    inference(cnf_transformation,[],[f29])).
% 1.32/0.57  fof(f120,plain,(
% 1.32/0.57    ( ! [X0,X1] : (k1_relat_1(X0) != sK0 | sK0 != k1_relat_1(sK4(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK4(X1) = X0 | ~v1_relat_1(sK4(X1))) )),
% 1.32/0.57    inference(resolution,[],[f34,f48])).
% 1.32/0.57  fof(f48,plain,(
% 1.32/0.57    ( ! [X0] : (v1_funct_1(sK4(X0))) )),
% 1.32/0.57    inference(cnf_transformation,[],[f29])).
% 1.32/0.57  fof(f34,plain,(
% 1.32/0.57    ( ! [X2,X1] : (~v1_funct_1(X1) | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | X1 = X2 | ~v1_relat_1(X1)) )),
% 1.32/0.57    inference(cnf_transformation,[],[f21])).
% 1.32/0.57  fof(f238,plain,(
% 1.32/0.57    ( ! [X2,X1] : (k1_funct_1(sK5(X1,X2),sK3(sK4(X1),np__1)) = X2 | k1_xboole_0 = X1) )),
% 1.32/0.57    inference(resolution,[],[f236,f58])).
% 1.32/0.57  fof(f58,plain,(
% 1.32/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | k1_funct_1(sK5(X0,X1),X3) = X1) )),
% 1.32/0.57    inference(cnf_transformation,[],[f33])).
% 1.32/0.57  fof(f236,plain,(
% 1.32/0.57    ( ! [X1] : (r2_hidden(sK3(sK4(X1),np__1),X1) | k1_xboole_0 = X1) )),
% 1.32/0.57    inference(forward_demodulation,[],[f235,f49])).
% 1.32/0.57  fof(f235,plain,(
% 1.32/0.57    ( ! [X1] : (k1_xboole_0 = X1 | r2_hidden(sK3(sK4(X1),np__1),k1_relat_1(sK4(X1)))) )),
% 1.32/0.57    inference(subsumption_resolution,[],[f234,f47])).
% 1.32/0.57  fof(f234,plain,(
% 1.32/0.57    ( ! [X1] : (k1_xboole_0 = X1 | r2_hidden(sK3(sK4(X1),np__1),k1_relat_1(sK4(X1))) | ~v1_relat_1(sK4(X1))) )),
% 1.32/0.57    inference(subsumption_resolution,[],[f222,f48])).
% 1.32/0.57  fof(f222,plain,(
% 1.32/0.57    ( ! [X1] : (k1_xboole_0 = X1 | r2_hidden(sK3(sK4(X1),np__1),k1_relat_1(sK4(X1))) | ~v1_funct_1(sK4(X1)) | ~v1_relat_1(sK4(X1))) )),
% 1.32/0.57    inference(resolution,[],[f218,f62])).
% 1.32/0.57  fof(f62,plain,(
% 1.32/0.57    ( ! [X0,X5] : (~r2_hidden(X5,k2_relat_1(X0)) | r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.32/0.57    inference(equality_resolution,[],[f41])).
% 1.32/0.57  fof(f41,plain,(
% 1.32/0.57    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.32/0.57    inference(cnf_transformation,[],[f27])).
% 1.32/0.57  fof(f27,plain,(
% 1.32/0.57    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((sK1(X0,X1) = k1_funct_1(X0,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.32/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f26,f25,f24])).
% 1.32/0.57  fof(f24,plain,(
% 1.32/0.57    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 1.32/0.57    introduced(choice_axiom,[])).
% 1.32/0.57  fof(f25,plain,(
% 1.32/0.57    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK1(X0,X1) = k1_funct_1(X0,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))),
% 1.32/0.57    introduced(choice_axiom,[])).
% 1.32/0.57  fof(f26,plain,(
% 1.32/0.57    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 1.32/0.57    introduced(choice_axiom,[])).
% 1.32/0.57  fof(f23,plain,(
% 1.32/0.57    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.32/0.57    inference(rectify,[],[f22])).
% 1.32/0.57  fof(f22,plain,(
% 1.32/0.57    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.32/0.57    inference(nnf_transformation,[],[f17])).
% 1.32/0.57  fof(f17,plain,(
% 1.32/0.57    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.32/0.57    inference(flattening,[],[f16])).
% 1.32/0.57  fof(f16,plain,(
% 1.32/0.57    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.32/0.57    inference(ennf_transformation,[],[f7])).
% 1.32/0.57  fof(f7,axiom,(
% 1.32/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 1.32/0.57  fof(f218,plain,(
% 1.32/0.57    ( ! [X0] : (r2_hidden(np__1,k2_relat_1(sK4(X0))) | k1_xboole_0 = X0) )),
% 1.32/0.57    inference(duplicate_literal_removal,[],[f217])).
% 1.32/0.57  fof(f217,plain,(
% 1.32/0.57    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(np__1,k2_relat_1(sK4(X0))) | k1_xboole_0 = X0) )),
% 1.32/0.57    inference(forward_demodulation,[],[f216,f199])).
% 1.32/0.57  fof(f199,plain,(
% 1.32/0.57    k1_xboole_0 = k2_relat_1(sK4(k1_xboole_0))),
% 1.32/0.57    inference(resolution,[],[f177,f65])).
% 1.32/0.57  fof(f65,plain,(
% 1.32/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.32/0.57    inference(superposition,[],[f51,f63])).
% 1.32/0.57  fof(f63,plain,(
% 1.32/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.32/0.57    inference(equality_resolution,[],[f54])).
% 1.32/0.57  fof(f54,plain,(
% 1.32/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.32/0.57    inference(cnf_transformation,[],[f31])).
% 1.32/0.57  fof(f31,plain,(
% 1.32/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.32/0.57    inference(flattening,[],[f30])).
% 1.32/0.57  fof(f30,plain,(
% 1.32/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.32/0.57    inference(nnf_transformation,[],[f2])).
% 1.32/0.57  fof(f2,axiom,(
% 1.32/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.32/0.57  fof(f51,plain,(
% 1.32/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.32/0.57    inference(cnf_transformation,[],[f3])).
% 1.32/0.57  fof(f3,axiom,(
% 1.32/0.57    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.32/0.57  fof(f177,plain,(
% 1.32/0.57    ( ! [X22] : (r2_hidden(sK1(sK4(k1_xboole_0),X22),X22) | k2_relat_1(sK4(k1_xboole_0)) = X22) )),
% 1.32/0.57    inference(resolution,[],[f165,f65])).
% 1.32/0.57  fof(f165,plain,(
% 1.32/0.57    ( ! [X0,X1] : (r2_hidden(sK2(sK4(X0),X1),X0) | r2_hidden(sK1(sK4(X0),X1),X1) | k2_relat_1(sK4(X0)) = X1) )),
% 1.32/0.57    inference(forward_demodulation,[],[f164,f49])).
% 1.32/0.57  fof(f164,plain,(
% 1.32/0.57    ( ! [X0,X1] : (r2_hidden(sK2(sK4(X0),X1),k1_relat_1(sK4(X0))) | r2_hidden(sK1(sK4(X0),X1),X1) | k2_relat_1(sK4(X0)) = X1) )),
% 1.32/0.57    inference(subsumption_resolution,[],[f161,f47])).
% 1.32/0.57  fof(f161,plain,(
% 1.32/0.57    ( ! [X0,X1] : (r2_hidden(sK2(sK4(X0),X1),k1_relat_1(sK4(X0))) | r2_hidden(sK1(sK4(X0),X1),X1) | k2_relat_1(sK4(X0)) = X1 | ~v1_relat_1(sK4(X0))) )),
% 1.32/0.57    inference(resolution,[],[f44,f48])).
% 1.32/0.57  fof(f44,plain,(
% 1.32/0.57    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | r2_hidden(sK1(X0,X1),X1) | k2_relat_1(X0) = X1 | ~v1_relat_1(X0)) )),
% 1.32/0.57    inference(cnf_transformation,[],[f27])).
% 1.32/0.57  fof(f216,plain,(
% 1.32/0.57    ( ! [X0] : (r2_hidden(np__1,k2_relat_1(sK4(X0))) | k1_xboole_0 = X0 | k2_relat_1(sK4(k1_xboole_0)) = X0) )),
% 1.32/0.57    inference(subsumption_resolution,[],[f214,f65])).
% 1.32/0.57  fof(f214,plain,(
% 1.32/0.57    ( ! [X0] : (r2_hidden(np__1,k2_relat_1(sK4(X0))) | k1_xboole_0 = X0 | r2_hidden(sK2(sK4(k1_xboole_0),X0),k1_xboole_0) | k2_relat_1(sK4(k1_xboole_0)) = X0) )),
% 1.32/0.57    inference(resolution,[],[f213,f165])).
% 1.32/0.57  fof(f213,plain,(
% 1.32/0.57    ( ! [X0] : (~r2_hidden(sK1(sK4(k1_xboole_0),X0),X0) | r2_hidden(np__1,k2_relat_1(sK4(X0))) | k1_xboole_0 = X0) )),
% 1.32/0.57    inference(forward_demodulation,[],[f212,f49])).
% 1.32/0.57  fof(f212,plain,(
% 1.32/0.57    ( ! [X0] : (r2_hidden(np__1,k2_relat_1(sK4(X0))) | ~r2_hidden(sK1(sK4(k1_xboole_0),X0),k1_relat_1(sK4(X0))) | k1_xboole_0 = X0) )),
% 1.32/0.57    inference(subsumption_resolution,[],[f211,f47])).
% 1.32/0.57  fof(f211,plain,(
% 1.32/0.57    ( ! [X0] : (r2_hidden(np__1,k2_relat_1(sK4(X0))) | ~r2_hidden(sK1(sK4(k1_xboole_0),X0),k1_relat_1(sK4(X0))) | ~v1_relat_1(sK4(X0)) | k1_xboole_0 = X0) )),
% 1.32/0.57    inference(subsumption_resolution,[],[f210,f48])).
% 1.32/0.57  fof(f210,plain,(
% 1.32/0.57    ( ! [X0] : (r2_hidden(np__1,k2_relat_1(sK4(X0))) | ~r2_hidden(sK1(sK4(k1_xboole_0),X0),k1_relat_1(sK4(X0))) | ~v1_funct_1(sK4(X0)) | ~v1_relat_1(sK4(X0)) | k1_xboole_0 = X0) )),
% 1.32/0.57    inference(superposition,[],[f60,f209])).
% 1.32/0.57  % (3528)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.32/0.57  fof(f209,plain,(
% 1.32/0.57    ( ! [X0] : (np__1 = k1_funct_1(sK4(X0),sK1(sK4(k1_xboole_0),X0)) | k1_xboole_0 = X0) )),
% 1.32/0.57    inference(forward_demodulation,[],[f191,f199])).
% 1.32/0.57  fof(f191,plain,(
% 1.32/0.57    ( ! [X0] : (k2_relat_1(sK4(k1_xboole_0)) = X0 | np__1 = k1_funct_1(sK4(X0),sK1(sK4(k1_xboole_0),X0))) )),
% 1.32/0.57    inference(resolution,[],[f177,f50])).
% 1.32/0.57  fof(f50,plain,(
% 1.32/0.57    ( ! [X2,X0] : (~r2_hidden(X2,X0) | np__1 = k1_funct_1(sK4(X0),X2)) )),
% 1.32/0.57    inference(cnf_transformation,[],[f29])).
% 1.32/0.57  fof(f60,plain,(
% 1.32/0.57    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.32/0.57    inference(equality_resolution,[],[f59])).
% 1.32/0.57  fof(f59,plain,(
% 1.32/0.57    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.32/0.57    inference(equality_resolution,[],[f43])).
% 1.32/0.57  fof(f43,plain,(
% 1.32/0.57    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.32/0.57    inference(cnf_transformation,[],[f27])).
% 1.32/0.57  fof(f430,plain,(
% 1.32/0.57    ( ! [X0] : (k1_xboole_0 != X0) )),
% 1.32/0.57    inference(superposition,[],[f35,f300])).
% 1.32/0.57  % SZS output end Proof for theBenchmark
% 1.32/0.57  % (3540)------------------------------
% 1.32/0.57  % (3540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.57  % (3540)Termination reason: Refutation
% 1.32/0.57  
% 1.32/0.57  % (3540)Memory used [KB]: 6524
% 1.32/0.57  % (3540)Time elapsed: 0.135 s
% 1.32/0.57  % (3540)------------------------------
% 1.32/0.57  % (3540)------------------------------
% 1.62/0.58  % (3518)Success in time 0.208 s
%------------------------------------------------------------------------------
