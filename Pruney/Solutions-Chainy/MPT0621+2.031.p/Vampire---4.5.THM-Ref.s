%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:59 EST 2020

% Result     : Theorem 2.31s
% Output     : Refutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   81 (1685 expanded)
%              Number of leaves         :   13 ( 510 expanded)
%              Depth                    :   26
%              Number of atoms          :  340 (7815 expanded)
%              Number of equality atoms :  171 (3566 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1813,plain,(
    $false ),
    inference(subsumption_resolution,[],[f32,f1728])).

fof(f1728,plain,(
    ! [X0,X1] : X0 = X1 ),
    inference(superposition,[],[f1462,f1462])).

fof(f1462,plain,(
    ! [X1] : k1_funct_1(sK6(sK2),sK3(k1_xboole_0,sK2)) = X1 ),
    inference(subsumption_resolution,[],[f1369,f32])).

fof(f1369,plain,(
    ! [X1] :
      ( k1_xboole_0 = sK2
      | k1_funct_1(sK6(sK2),sK3(k1_xboole_0,sK2)) = X1 ) ),
    inference(backward_demodulation,[],[f1079,f1241])).

fof(f1241,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(condensation,[],[f1240])).

fof(f1240,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_xboole_0 = k2_relat_1(k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f1093])).

fof(f1093,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_xboole_0 = k2_relat_1(k1_xboole_0)
      | k1_xboole_0 = k2_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f1078,f1078])).

fof(f1078,plain,(
    ! [X0] :
      ( k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k1_xboole_0)) = X0
      | k1_xboole_0 = k2_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f1068,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = sK7(k1_xboole_0,X0) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = sK7(X0,X1) ) ),
    inference(superposition,[],[f55,f50])).

fof(f50,plain,(
    ! [X0,X1] : k1_relat_1(sK7(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK7(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK7(X0,X1)) = X0
      & v1_funct_1(sK7(X0,X1))
      & v1_relat_1(sK7(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f14,f29])).

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
            ( k1_funct_1(sK7(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK7(X0,X1)) = X0
        & v1_funct_1(sK7(X0,X1))
        & v1_relat_1(sK7(X0,X1)) ) ) ),
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f55,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relat_1(sK7(X1,X2))
      | k1_xboole_0 = sK7(X1,X2) ) ),
    inference(resolution,[],[f33,f48])).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(sK7(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) != k1_xboole_0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f1068,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK7(X0,X1),sK3(k1_xboole_0,X0)) = X1
      | k2_relat_1(k1_xboole_0) = X0 ) ),
    inference(condensation,[],[f1067])).

fof(f1067,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(sK7(X0,X1),sK3(k1_xboole_0,X0)) = X1
      | k2_relat_1(k1_xboole_0) = X0
      | k1_funct_1(sK7(X0,X2),sK3(k1_xboole_0,X0)) = X2 ) ),
    inference(condensation,[],[f1066])).

fof(f1066,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X1 = X2
      | k1_funct_1(sK7(X0,X3),sK3(k1_xboole_0,X0)) = X3
      | k2_relat_1(k1_xboole_0) = X0
      | k1_funct_1(sK7(X0,X4),sK3(k1_xboole_0,X0)) = X4 ) ),
    inference(duplicate_literal_removal,[],[f899])).

fof(f899,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X1 = X2
      | k1_funct_1(sK7(X0,X3),sK3(k1_xboole_0,X0)) = X3
      | k2_relat_1(k1_xboole_0) = X0
      | k1_funct_1(sK7(X0,X4),sK3(k1_xboole_0,X0)) = X4
      | k2_relat_1(k1_xboole_0) = X0 ) ),
    inference(superposition,[],[f393,f393])).

fof(f393,plain,(
    ! [X8,X7,X9] :
      ( k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X7)) = X8
      | k1_funct_1(sK7(X7,X9),sK3(k1_xboole_0,X7)) = X9
      | k2_relat_1(k1_xboole_0) = X7 ) ),
    inference(subsumption_resolution,[],[f392,f62])).

fof(f62,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f44,f58])).

fof(f58,plain,(
    k1_xboole_0 = sK6(k1_xboole_0) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = sK6(X0) ) ),
    inference(superposition,[],[f54,f46])).

fof(f46,plain,(
    ! [X0] : k1_relat_1(sK6(X0)) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK6(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK6(X0)) = X0
      & v1_funct_1(sK6(X0))
      & v1_relat_1(sK6(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f13,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK6(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK6(X0)) = X0
        & v1_funct_1(sK6(X0))
        & v1_relat_1(sK6(X0)) ) ) ),
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(sK6(X0))
      | k1_xboole_0 = sK6(X0) ) ),
    inference(resolution,[],[f33,f44])).

fof(f44,plain,(
    ! [X0] : v1_relat_1(sK6(X0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f392,plain,(
    ! [X8,X7,X9] :
      ( k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X7)) = X8
      | k1_funct_1(sK7(X7,X9),sK3(k1_xboole_0,X7)) = X9
      | k2_relat_1(k1_xboole_0) = X7
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f388,f61])).

fof(f61,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f45,f58])).

fof(f45,plain,(
    ! [X0] : v1_funct_1(sK6(X0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f388,plain,(
    ! [X8,X7,X9] :
      ( k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X7)) = X8
      | k1_funct_1(sK7(X7,X9),sK3(k1_xboole_0,X7)) = X9
      | k2_relat_1(k1_xboole_0) = X7
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f120,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k2_relat_1(X0) = X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f36,f43])).

fof(f43,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f12,f16,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( k1_funct_1(X0,X3) = X2
              & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> sP0(X0,X1) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0)
      | ~ sP0(X0,X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ~ sP0(X0,X1) )
          & ( sP0(X0,X1)
            | k2_relat_1(X0) != X1 ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f120,plain,(
    ! [X12,X13,X11] :
      ( sP0(k1_xboole_0,X11)
      | k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X11)) = X12
      | k1_funct_1(sK7(X11,X13),sK3(k1_xboole_0,X11)) = X13 ) ),
    inference(resolution,[],[f92,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(sK7(X0,X1),X3) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f92,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK3(k1_xboole_0,X4),X4)
      | k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X4)) = X5
      | sP0(k1_xboole_0,X4) ) ),
    inference(forward_demodulation,[],[f86,f65])).

fof(f86,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK3(k1_xboole_0,X4),X4)
      | sP0(k1_xboole_0,X4)
      | k1_funct_1(sK7(k1_xboole_0,X5),sK4(k1_xboole_0,X4)) = X5 ) ),
    inference(resolution,[],[f83,f51])).

fof(f83,plain,(
    ! [X5] :
      ( r2_hidden(sK4(k1_xboole_0,X5),k1_xboole_0)
      | r2_hidden(sK3(k1_xboole_0,X5),X5)
      | sP0(k1_xboole_0,X5) ) ),
    inference(superposition,[],[f40,f60])).

fof(f60,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f46,f58])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK3(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != sK3(X0,X1)
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
              & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( k1_funct_1(X0,X6) != X5
                  | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
            & ( ( k1_funct_1(X0,sK5(X0,X5)) = X5
                & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) )
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f25,f24,f23])).

fof(f23,plain,(
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
              ( k1_funct_1(X0,X3) != sK3(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK3(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK3(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X5)) = X5
        & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f1079,plain,(
    ! [X1] :
      ( k1_funct_1(sK6(sK2),sK3(k1_xboole_0,sK2)) = X1
      | sK2 = k2_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f1068,f231])).

fof(f231,plain,(
    ! [X0] : sK6(sK2) = sK7(sK2,X0) ),
    inference(equality_resolution,[],[f230])).

fof(f230,plain,(
    ! [X0,X1] :
      ( sK2 != X0
      | sK7(X0,X1) = sK6(sK2) ) ),
    inference(equality_resolution,[],[f228])).

fof(f228,plain,(
    ! [X2,X0,X1] :
      ( sK2 != X2
      | sK2 != X0
      | sK7(X0,X1) = sK6(X2) ) ),
    inference(superposition,[],[f219,f50])).

fof(f219,plain,(
    ! [X4,X2,X3] :
      ( sK2 != k1_relat_1(sK7(X2,X3))
      | sK2 != X4
      | sK7(X2,X3) = sK6(X4) ) ),
    inference(subsumption_resolution,[],[f216,f48])).

fof(f216,plain,(
    ! [X4,X2,X3] :
      ( sK2 != k1_relat_1(sK7(X2,X3))
      | sK2 != X4
      | ~ v1_relat_1(sK7(X2,X3))
      | sK7(X2,X3) = sK6(X4) ) ),
    inference(resolution,[],[f210,f49])).

fof(f49,plain,(
    ! [X0,X1] : v1_funct_1(sK7(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f210,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | k1_relat_1(X0) != sK2
      | sK2 != X1
      | ~ v1_relat_1(X0)
      | sK6(X1) = X0 ) ),
    inference(forward_demodulation,[],[f209,f46])).

fof(f209,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != sK2
      | sK2 != k1_relat_1(sK6(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK6(X1) = X0 ) ),
    inference(subsumption_resolution,[],[f206,f44])).

fof(f206,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != sK2
      | sK2 != k1_relat_1(sK6(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK6(X1) = X0
      | ~ v1_relat_1(sK6(X1)) ) ),
    inference(resolution,[],[f31,f45])).

fof(f31,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X1)
      | k1_relat_1(X2) != sK2
      | k1_relat_1(X1) != sK2
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | X1 = X2
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k1_xboole_0 != sK2
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK2
            | k1_relat_1(X1) != sK2
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f18])).

fof(f18,plain,
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
   => ( k1_xboole_0 != sK2
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK2
              | k1_relat_1(X1) != sK2
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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

fof(f32,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 14:08:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.50  % (1662)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.23/0.50  % (1655)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.23/0.51  % (1656)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.51  % (1654)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.52  % (1653)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.52  % (1657)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.52  % (1661)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.23/0.53  % (1673)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.23/0.53  % (1652)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.23/0.53  % (1672)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.23/0.53  % (1657)Refutation not found, incomplete strategy% (1657)------------------------------
% 0.23/0.53  % (1657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (1663)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.23/0.53  % (1657)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (1657)Memory used [KB]: 6140
% 0.23/0.53  % (1657)Time elapsed: 0.110 s
% 0.23/0.53  % (1657)------------------------------
% 0.23/0.53  % (1657)------------------------------
% 0.23/0.53  % (1663)Refutation not found, incomplete strategy% (1663)------------------------------
% 0.23/0.53  % (1663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (1663)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (1663)Memory used [KB]: 10618
% 0.23/0.53  % (1663)Time elapsed: 0.117 s
% 0.23/0.53  % (1663)------------------------------
% 0.23/0.53  % (1663)------------------------------
% 0.23/0.53  % (1664)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.23/0.53  % (1660)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.23/0.53  % (1677)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.23/0.53  % (1658)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.23/0.53  % (1674)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.53  % (1665)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.23/0.53  % (1670)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.23/0.54  % (1659)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.23/0.54  % (1652)Refutation not found, incomplete strategy% (1652)------------------------------
% 0.23/0.54  % (1652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (1652)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (1652)Memory used [KB]: 10618
% 0.23/0.54  % (1652)Time elapsed: 0.116 s
% 0.23/0.54  % (1652)------------------------------
% 0.23/0.54  % (1652)------------------------------
% 0.23/0.54  % (1653)Refutation not found, incomplete strategy% (1653)------------------------------
% 0.23/0.54  % (1653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (1653)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (1653)Memory used [KB]: 10618
% 0.23/0.54  % (1653)Time elapsed: 0.106 s
% 0.23/0.54  % (1653)------------------------------
% 0.23/0.54  % (1653)------------------------------
% 0.23/0.54  % (1671)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.23/0.54  % (1665)Refutation not found, incomplete strategy% (1665)------------------------------
% 0.23/0.54  % (1665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (1665)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (1665)Memory used [KB]: 6140
% 0.23/0.54  % (1665)Time elapsed: 0.123 s
% 0.23/0.54  % (1665)------------------------------
% 0.23/0.54  % (1665)------------------------------
% 0.23/0.54  % (1668)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.23/0.54  % (1675)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.23/0.54  % (1659)Refutation not found, incomplete strategy% (1659)------------------------------
% 0.23/0.54  % (1659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (1666)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.54  % (1667)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.23/0.55  % (1669)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.23/0.56  % (1658)Refutation not found, incomplete strategy% (1658)------------------------------
% 0.23/0.56  % (1658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (1658)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (1658)Memory used [KB]: 10618
% 0.23/0.56  % (1658)Time elapsed: 0.105 s
% 0.23/0.56  % (1658)------------------------------
% 0.23/0.56  % (1658)------------------------------
% 0.23/0.56  % (1659)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (1659)Memory used [KB]: 1663
% 0.23/0.56  % (1659)Time elapsed: 0.125 s
% 0.23/0.56  % (1659)------------------------------
% 0.23/0.56  % (1659)------------------------------
% 0.23/0.56  % (1676)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 2.31/0.68  % (1655)Refutation found. Thanks to Tanya!
% 2.31/0.68  % SZS status Theorem for theBenchmark
% 2.31/0.68  % SZS output start Proof for theBenchmark
% 2.31/0.68  fof(f1813,plain,(
% 2.31/0.68    $false),
% 2.31/0.68    inference(subsumption_resolution,[],[f32,f1728])).
% 2.31/0.68  fof(f1728,plain,(
% 2.31/0.68    ( ! [X0,X1] : (X0 = X1) )),
% 2.31/0.68    inference(superposition,[],[f1462,f1462])).
% 2.31/0.68  fof(f1462,plain,(
% 2.31/0.68    ( ! [X1] : (k1_funct_1(sK6(sK2),sK3(k1_xboole_0,sK2)) = X1) )),
% 2.31/0.68    inference(subsumption_resolution,[],[f1369,f32])).
% 2.31/0.68  fof(f1369,plain,(
% 2.31/0.68    ( ! [X1] : (k1_xboole_0 = sK2 | k1_funct_1(sK6(sK2),sK3(k1_xboole_0,sK2)) = X1) )),
% 2.31/0.68    inference(backward_demodulation,[],[f1079,f1241])).
% 2.31/0.68  fof(f1241,plain,(
% 2.31/0.68    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.31/0.68    inference(condensation,[],[f1240])).
% 2.31/0.68  fof(f1240,plain,(
% 2.31/0.68    ( ! [X0,X1] : (X0 = X1 | k1_xboole_0 = k2_relat_1(k1_xboole_0)) )),
% 2.31/0.68    inference(duplicate_literal_removal,[],[f1093])).
% 2.31/0.68  fof(f1093,plain,(
% 2.31/0.68    ( ! [X0,X1] : (X0 = X1 | k1_xboole_0 = k2_relat_1(k1_xboole_0) | k1_xboole_0 = k2_relat_1(k1_xboole_0)) )),
% 2.31/0.68    inference(superposition,[],[f1078,f1078])).
% 2.31/0.68  fof(f1078,plain,(
% 2.31/0.68    ( ! [X0] : (k1_funct_1(k1_xboole_0,sK3(k1_xboole_0,k1_xboole_0)) = X0 | k1_xboole_0 = k2_relat_1(k1_xboole_0)) )),
% 2.31/0.68    inference(superposition,[],[f1068,f65])).
% 2.31/0.68  fof(f65,plain,(
% 2.31/0.68    ( ! [X0] : (k1_xboole_0 = sK7(k1_xboole_0,X0)) )),
% 2.31/0.68    inference(equality_resolution,[],[f64])).
% 2.31/0.68  fof(f64,plain,(
% 2.31/0.68    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = sK7(X0,X1)) )),
% 2.31/0.68    inference(superposition,[],[f55,f50])).
% 2.31/0.68  fof(f50,plain,(
% 2.31/0.68    ( ! [X0,X1] : (k1_relat_1(sK7(X0,X1)) = X0) )),
% 2.31/0.68    inference(cnf_transformation,[],[f30])).
% 2.31/0.68  fof(f30,plain,(
% 2.31/0.68    ! [X0,X1] : (! [X3] : (k1_funct_1(sK7(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK7(X0,X1)) = X0 & v1_funct_1(sK7(X0,X1)) & v1_relat_1(sK7(X0,X1)))),
% 2.31/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f14,f29])).
% 2.31/0.68  fof(f29,plain,(
% 2.31/0.68    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK7(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK7(X0,X1)) = X0 & v1_funct_1(sK7(X0,X1)) & v1_relat_1(sK7(X0,X1))))),
% 2.31/0.68    introduced(choice_axiom,[])).
% 2.31/0.68  fof(f14,plain,(
% 2.31/0.68    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 2.31/0.68    inference(ennf_transformation,[],[f3])).
% 2.31/0.68  fof(f3,axiom,(
% 2.31/0.68    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 2.31/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 2.31/0.68  fof(f55,plain,(
% 2.31/0.68    ( ! [X2,X1] : (k1_xboole_0 != k1_relat_1(sK7(X1,X2)) | k1_xboole_0 = sK7(X1,X2)) )),
% 2.31/0.68    inference(resolution,[],[f33,f48])).
% 2.31/0.68  fof(f48,plain,(
% 2.31/0.68    ( ! [X0,X1] : (v1_relat_1(sK7(X0,X1))) )),
% 2.31/0.68    inference(cnf_transformation,[],[f30])).
% 2.31/0.68  fof(f33,plain,(
% 2.31/0.68    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0) )),
% 2.31/0.68    inference(cnf_transformation,[],[f10])).
% 2.31/0.68  fof(f10,plain,(
% 2.31/0.68    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 2.31/0.68    inference(flattening,[],[f9])).
% 2.31/0.68  fof(f9,plain,(
% 2.31/0.68    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 2.31/0.68    inference(ennf_transformation,[],[f1])).
% 2.31/0.68  fof(f1,axiom,(
% 2.31/0.68    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 2.31/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 2.31/0.68  fof(f1068,plain,(
% 2.31/0.68    ( ! [X0,X1] : (k1_funct_1(sK7(X0,X1),sK3(k1_xboole_0,X0)) = X1 | k2_relat_1(k1_xboole_0) = X0) )),
% 2.31/0.68    inference(condensation,[],[f1067])).
% 2.31/0.68  fof(f1067,plain,(
% 2.31/0.68    ( ! [X2,X0,X1] : (k1_funct_1(sK7(X0,X1),sK3(k1_xboole_0,X0)) = X1 | k2_relat_1(k1_xboole_0) = X0 | k1_funct_1(sK7(X0,X2),sK3(k1_xboole_0,X0)) = X2) )),
% 2.31/0.68    inference(condensation,[],[f1066])).
% 2.31/0.68  fof(f1066,plain,(
% 2.31/0.68    ( ! [X4,X2,X0,X3,X1] : (X1 = X2 | k1_funct_1(sK7(X0,X3),sK3(k1_xboole_0,X0)) = X3 | k2_relat_1(k1_xboole_0) = X0 | k1_funct_1(sK7(X0,X4),sK3(k1_xboole_0,X0)) = X4) )),
% 2.31/0.68    inference(duplicate_literal_removal,[],[f899])).
% 2.31/0.68  fof(f899,plain,(
% 2.31/0.68    ( ! [X4,X2,X0,X3,X1] : (X1 = X2 | k1_funct_1(sK7(X0,X3),sK3(k1_xboole_0,X0)) = X3 | k2_relat_1(k1_xboole_0) = X0 | k1_funct_1(sK7(X0,X4),sK3(k1_xboole_0,X0)) = X4 | k2_relat_1(k1_xboole_0) = X0) )),
% 2.31/0.68    inference(superposition,[],[f393,f393])).
% 2.31/0.68  fof(f393,plain,(
% 2.31/0.68    ( ! [X8,X7,X9] : (k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X7)) = X8 | k1_funct_1(sK7(X7,X9),sK3(k1_xboole_0,X7)) = X9 | k2_relat_1(k1_xboole_0) = X7) )),
% 2.31/0.68    inference(subsumption_resolution,[],[f392,f62])).
% 2.31/0.68  fof(f62,plain,(
% 2.31/0.68    v1_relat_1(k1_xboole_0)),
% 2.31/0.68    inference(superposition,[],[f44,f58])).
% 2.31/0.68  fof(f58,plain,(
% 2.31/0.68    k1_xboole_0 = sK6(k1_xboole_0)),
% 2.31/0.68    inference(equality_resolution,[],[f57])).
% 2.31/0.68  fof(f57,plain,(
% 2.31/0.68    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = sK6(X0)) )),
% 2.31/0.68    inference(superposition,[],[f54,f46])).
% 2.31/0.68  fof(f46,plain,(
% 2.31/0.68    ( ! [X0] : (k1_relat_1(sK6(X0)) = X0) )),
% 2.31/0.68    inference(cnf_transformation,[],[f28])).
% 2.31/0.68  fof(f28,plain,(
% 2.31/0.68    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK6(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK6(X0)) = X0 & v1_funct_1(sK6(X0)) & v1_relat_1(sK6(X0)))),
% 2.31/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f13,f27])).
% 2.31/0.68  fof(f27,plain,(
% 2.31/0.68    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK6(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK6(X0)) = X0 & v1_funct_1(sK6(X0)) & v1_relat_1(sK6(X0))))),
% 2.31/0.68    introduced(choice_axiom,[])).
% 2.31/0.68  fof(f13,plain,(
% 2.31/0.68    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.31/0.68    inference(ennf_transformation,[],[f4])).
% 2.31/0.68  fof(f4,axiom,(
% 2.31/0.68    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 2.31/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 2.31/0.68  fof(f54,plain,(
% 2.31/0.68    ( ! [X0] : (k1_xboole_0 != k1_relat_1(sK6(X0)) | k1_xboole_0 = sK6(X0)) )),
% 2.31/0.68    inference(resolution,[],[f33,f44])).
% 2.31/0.68  fof(f44,plain,(
% 2.31/0.68    ( ! [X0] : (v1_relat_1(sK6(X0))) )),
% 2.31/0.68    inference(cnf_transformation,[],[f28])).
% 2.31/0.68  fof(f392,plain,(
% 2.31/0.68    ( ! [X8,X7,X9] : (k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X7)) = X8 | k1_funct_1(sK7(X7,X9),sK3(k1_xboole_0,X7)) = X9 | k2_relat_1(k1_xboole_0) = X7 | ~v1_relat_1(k1_xboole_0)) )),
% 2.31/0.68    inference(subsumption_resolution,[],[f388,f61])).
% 2.31/0.68  fof(f61,plain,(
% 2.31/0.68    v1_funct_1(k1_xboole_0)),
% 2.31/0.68    inference(superposition,[],[f45,f58])).
% 2.31/0.68  fof(f45,plain,(
% 2.31/0.68    ( ! [X0] : (v1_funct_1(sK6(X0))) )),
% 2.31/0.68    inference(cnf_transformation,[],[f28])).
% 2.31/0.68  fof(f388,plain,(
% 2.31/0.68    ( ! [X8,X7,X9] : (k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X7)) = X8 | k1_funct_1(sK7(X7,X9),sK3(k1_xboole_0,X7)) = X9 | k2_relat_1(k1_xboole_0) = X7 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 2.31/0.68    inference(resolution,[],[f120,f56])).
% 2.31/0.68  fof(f56,plain,(
% 2.31/0.68    ( ! [X0,X1] : (~sP0(X0,X1) | k2_relat_1(X0) = X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.31/0.68    inference(resolution,[],[f36,f43])).
% 2.31/0.68  fof(f43,plain,(
% 2.31/0.68    ( ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.31/0.68    inference(cnf_transformation,[],[f17])).
% 2.31/0.68  fof(f17,plain,(
% 2.31/0.68    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.31/0.68    inference(definition_folding,[],[f12,f16,f15])).
% 2.31/0.68  fof(f15,plain,(
% 2.31/0.68    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0)))))),
% 2.31/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.31/0.68  fof(f16,plain,(
% 2.31/0.68    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> sP0(X0,X1)) | ~sP1(X0))),
% 2.31/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.31/0.68  fof(f12,plain,(
% 2.31/0.68    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.31/0.68    inference(flattening,[],[f11])).
% 2.31/0.68  fof(f11,plain,(
% 2.31/0.68    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.31/0.68    inference(ennf_transformation,[],[f2])).
% 2.31/0.68  fof(f2,axiom,(
% 2.31/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 2.31/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 2.31/0.68  fof(f36,plain,(
% 2.31/0.68    ( ! [X0,X1] : (~sP1(X0) | ~sP0(X0,X1) | k2_relat_1(X0) = X1) )),
% 2.31/0.68    inference(cnf_transformation,[],[f20])).
% 2.31/0.68  fof(f20,plain,(
% 2.31/0.68    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k2_relat_1(X0) != X1)) | ~sP1(X0))),
% 2.31/0.68    inference(nnf_transformation,[],[f16])).
% 2.31/0.68  fof(f120,plain,(
% 2.31/0.68    ( ! [X12,X13,X11] : (sP0(k1_xboole_0,X11) | k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X11)) = X12 | k1_funct_1(sK7(X11,X13),sK3(k1_xboole_0,X11)) = X13) )),
% 2.31/0.68    inference(resolution,[],[f92,f51])).
% 2.31/0.68  fof(f51,plain,(
% 2.31/0.68    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | k1_funct_1(sK7(X0,X1),X3) = X1) )),
% 2.31/0.68    inference(cnf_transformation,[],[f30])).
% 2.31/0.68  fof(f92,plain,(
% 2.31/0.68    ( ! [X4,X5] : (r2_hidden(sK3(k1_xboole_0,X4),X4) | k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,X4)) = X5 | sP0(k1_xboole_0,X4)) )),
% 2.31/0.68    inference(forward_demodulation,[],[f86,f65])).
% 2.31/0.68  fof(f86,plain,(
% 2.31/0.68    ( ! [X4,X5] : (r2_hidden(sK3(k1_xboole_0,X4),X4) | sP0(k1_xboole_0,X4) | k1_funct_1(sK7(k1_xboole_0,X5),sK4(k1_xboole_0,X4)) = X5) )),
% 2.31/0.68    inference(resolution,[],[f83,f51])).
% 2.31/0.68  fof(f83,plain,(
% 2.31/0.68    ( ! [X5] : (r2_hidden(sK4(k1_xboole_0,X5),k1_xboole_0) | r2_hidden(sK3(k1_xboole_0,X5),X5) | sP0(k1_xboole_0,X5)) )),
% 2.31/0.68    inference(superposition,[],[f40,f60])).
% 2.31/0.68  fof(f60,plain,(
% 2.31/0.68    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.31/0.68    inference(superposition,[],[f46,f58])).
% 2.31/0.68  fof(f40,plain,(
% 2.31/0.68    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | r2_hidden(sK3(X0,X1),X1) | sP0(X0,X1)) )),
% 2.31/0.68    inference(cnf_transformation,[],[f26])).
% 2.31/0.68  fof(f26,plain,(
% 2.31/0.68    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & ((sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 2.31/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f25,f24,f23])).
% 2.31/0.68  fof(f23,plain,(
% 2.31/0.68    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1))))),
% 2.31/0.68    introduced(choice_axiom,[])).
% 2.31/0.68  fof(f24,plain,(
% 2.31/0.68    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 2.31/0.68    introduced(choice_axiom,[])).
% 2.31/0.68  fof(f25,plain,(
% 2.31/0.68    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))))),
% 2.31/0.68    introduced(choice_axiom,[])).
% 2.31/0.68  fof(f22,plain,(
% 2.31/0.68    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 2.31/0.68    inference(rectify,[],[f21])).
% 2.31/0.68  fof(f21,plain,(
% 2.31/0.68    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 2.31/0.68    inference(nnf_transformation,[],[f15])).
% 2.31/0.68  fof(f1079,plain,(
% 2.31/0.68    ( ! [X1] : (k1_funct_1(sK6(sK2),sK3(k1_xboole_0,sK2)) = X1 | sK2 = k2_relat_1(k1_xboole_0)) )),
% 2.31/0.68    inference(superposition,[],[f1068,f231])).
% 2.31/0.68  fof(f231,plain,(
% 2.31/0.68    ( ! [X0] : (sK6(sK2) = sK7(sK2,X0)) )),
% 2.31/0.68    inference(equality_resolution,[],[f230])).
% 2.31/0.68  fof(f230,plain,(
% 2.31/0.68    ( ! [X0,X1] : (sK2 != X0 | sK7(X0,X1) = sK6(sK2)) )),
% 2.31/0.68    inference(equality_resolution,[],[f228])).
% 2.31/0.68  fof(f228,plain,(
% 2.31/0.68    ( ! [X2,X0,X1] : (sK2 != X2 | sK2 != X0 | sK7(X0,X1) = sK6(X2)) )),
% 2.31/0.68    inference(superposition,[],[f219,f50])).
% 2.31/0.68  fof(f219,plain,(
% 2.31/0.68    ( ! [X4,X2,X3] : (sK2 != k1_relat_1(sK7(X2,X3)) | sK2 != X4 | sK7(X2,X3) = sK6(X4)) )),
% 2.31/0.68    inference(subsumption_resolution,[],[f216,f48])).
% 2.31/0.68  fof(f216,plain,(
% 2.31/0.68    ( ! [X4,X2,X3] : (sK2 != k1_relat_1(sK7(X2,X3)) | sK2 != X4 | ~v1_relat_1(sK7(X2,X3)) | sK7(X2,X3) = sK6(X4)) )),
% 2.31/0.68    inference(resolution,[],[f210,f49])).
% 2.31/0.68  fof(f49,plain,(
% 2.31/0.68    ( ! [X0,X1] : (v1_funct_1(sK7(X0,X1))) )),
% 2.31/0.68    inference(cnf_transformation,[],[f30])).
% 2.31/0.68  fof(f210,plain,(
% 2.31/0.68    ( ! [X0,X1] : (~v1_funct_1(X0) | k1_relat_1(X0) != sK2 | sK2 != X1 | ~v1_relat_1(X0) | sK6(X1) = X0) )),
% 2.31/0.68    inference(forward_demodulation,[],[f209,f46])).
% 2.31/0.68  fof(f209,plain,(
% 2.31/0.68    ( ! [X0,X1] : (k1_relat_1(X0) != sK2 | sK2 != k1_relat_1(sK6(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK6(X1) = X0) )),
% 2.31/0.68    inference(subsumption_resolution,[],[f206,f44])).
% 2.31/0.68  fof(f206,plain,(
% 2.31/0.68    ( ! [X0,X1] : (k1_relat_1(X0) != sK2 | sK2 != k1_relat_1(sK6(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sK6(X1) = X0 | ~v1_relat_1(sK6(X1))) )),
% 2.31/0.68    inference(resolution,[],[f31,f45])).
% 2.31/0.68  fof(f31,plain,(
% 2.31/0.68    ( ! [X2,X1] : (~v1_funct_1(X1) | k1_relat_1(X2) != sK2 | k1_relat_1(X1) != sK2 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | X1 = X2 | ~v1_relat_1(X1)) )),
% 2.31/0.68    inference(cnf_transformation,[],[f19])).
% 2.31/0.68  fof(f19,plain,(
% 2.31/0.68    k1_xboole_0 != sK2 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK2 | k1_relat_1(X1) != sK2 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.31/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f18])).
% 2.31/0.68  fof(f18,plain,(
% 2.31/0.68    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK2 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK2 | k1_relat_1(X1) != sK2 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.31/0.68    introduced(choice_axiom,[])).
% 2.31/0.68  fof(f8,plain,(
% 2.31/0.68    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.31/0.68    inference(flattening,[],[f7])).
% 2.31/0.68  fof(f7,plain,(
% 2.31/0.68    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 2.31/0.68    inference(ennf_transformation,[],[f6])).
% 2.31/0.68  fof(f6,negated_conjecture,(
% 2.31/0.68    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 2.31/0.68    inference(negated_conjecture,[],[f5])).
% 2.31/0.68  fof(f5,conjecture,(
% 2.31/0.68    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 2.31/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).
% 2.31/0.68  fof(f32,plain,(
% 2.31/0.68    k1_xboole_0 != sK2),
% 2.31/0.68    inference(cnf_transformation,[],[f19])).
% 2.31/0.68  % SZS output end Proof for theBenchmark
% 2.31/0.68  % (1655)------------------------------
% 2.31/0.68  % (1655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.31/0.68  % (1655)Termination reason: Refutation
% 2.31/0.68  
% 2.31/0.68  % (1655)Memory used [KB]: 7164
% 2.31/0.68  % (1655)Time elapsed: 0.257 s
% 2.31/0.68  % (1655)------------------------------
% 2.31/0.68  % (1655)------------------------------
% 2.31/0.68  % (1650)Success in time 0.312 s
%------------------------------------------------------------------------------
