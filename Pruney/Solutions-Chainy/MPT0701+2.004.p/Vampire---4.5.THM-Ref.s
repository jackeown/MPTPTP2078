%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:11 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  114 (2671 expanded)
%              Number of leaves         :   12 ( 970 expanded)
%              Depth                    :   22
%              Number of atoms          :  500 (27474 expanded)
%              Number of equality atoms :  155 (12661 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1001,plain,(
    $false ),
    inference(subsumption_resolution,[],[f998,f949])).

fof(f949,plain,(
    r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2) ),
    inference(subsumption_resolution,[],[f946,f226])).

fof(f226,plain,(
    r2_hidden(sK4(sK3,sK2),sK0) ),
    inference(subsumption_resolution,[],[f225,f71])).

fof(f71,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
      | r2_hidden(X2,sK0) ) ),
    inference(forward_demodulation,[],[f70,f39])).

fof(f39,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK2 != sK3
    & k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3)
    & sK0 = k1_relat_1(sK3)
    & sK0 = k1_relat_1(sK2)
    & sK0 = k2_relat_1(sK1)
    & v1_funct_1(sK3)
    & v1_relat_1(sK3)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( X2 != X3
                & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
                & k1_relat_1(X3) = X0
                & k1_relat_1(X2) = X0
                & k2_relat_1(X1) = X0
                & v1_funct_1(X3)
                & v1_relat_1(X3) )
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k5_relat_1(sK1,X2) = k5_relat_1(sK1,X3)
              & k1_relat_1(X3) = sK0
              & k1_relat_1(X2) = sK0
              & sK0 = k2_relat_1(sK1)
              & v1_funct_1(X3)
              & v1_relat_1(X3) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( X2 != X3
            & k5_relat_1(sK1,X2) = k5_relat_1(sK1,X3)
            & k1_relat_1(X3) = sK0
            & k1_relat_1(X2) = sK0
            & sK0 = k2_relat_1(sK1)
            & v1_funct_1(X3)
            & v1_relat_1(X3) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( sK2 != X3
          & k5_relat_1(sK1,X3) = k5_relat_1(sK1,sK2)
          & k1_relat_1(X3) = sK0
          & sK0 = k1_relat_1(sK2)
          & sK0 = k2_relat_1(sK1)
          & v1_funct_1(X3)
          & v1_relat_1(X3) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X3] :
        ( sK2 != X3
        & k5_relat_1(sK1,X3) = k5_relat_1(sK1,sK2)
        & k1_relat_1(X3) = sK0
        & sK0 = k1_relat_1(sK2)
        & sK0 = k2_relat_1(sK1)
        & v1_funct_1(X3)
        & v1_relat_1(X3) )
   => ( sK2 != sK3
      & k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3)
      & sK0 = k1_relat_1(sK3)
      & sK0 = k1_relat_1(sK2)
      & sK0 = k2_relat_1(sK1)
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
              & k1_relat_1(X3) = X0
              & k1_relat_1(X2) = X0
              & k2_relat_1(X1) = X0
              & v1_funct_1(X3)
              & v1_relat_1(X3) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
              & k1_relat_1(X3) = X0
              & k1_relat_1(X2) = X0
              & k2_relat_1(X1) = X0
              & v1_funct_1(X3)
              & v1_relat_1(X3) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_relat_1(X3) )
               => ( ( k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
                    & k1_relat_1(X3) = X0
                    & k1_relat_1(X2) = X0
                    & k2_relat_1(X1) = X0 )
                 => X2 = X3 ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_relat_1(X3) )
             => ( ( k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
                  & k1_relat_1(X3) = X0
                  & k1_relat_1(X2) = X0
                  & k2_relat_1(X1) = X0 )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_funct_1)).

fof(f70,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
      | r2_hidden(X2,k1_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f67,f34])).

fof(f34,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f67,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
      | r2_hidden(X2,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f54,f35])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f225,plain,
    ( r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2)
    | r2_hidden(sK4(sK3,sK2),sK0) ),
    inference(resolution,[],[f136,f73])).

fof(f73,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),sK3)
      | r2_hidden(X4,sK0) ) ),
    inference(forward_demodulation,[],[f72,f40])).

fof(f40,plain,(
    sK0 = k1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),sK3)
      | r2_hidden(X4,k1_relat_1(sK3)) ) ),
    inference(subsumption_resolution,[],[f68,f36])).

fof(f36,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),sK3)
      | r2_hidden(X4,k1_relat_1(sK3))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f54,f37])).

fof(f37,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f136,plain,
    ( r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK3)
    | r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2) ),
    inference(subsumption_resolution,[],[f135,f36])).

fof(f135,plain,
    ( r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2)
    | r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f127,f34])).

fof(f127,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2)
    | r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(extensionality_resolution,[],[f45,f42])).

fof(f42,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | X0 = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
                  | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) )
                & ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
                  | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r2_hidden(k4_tarski(X2,X3),X1)
            | r2_hidden(k4_tarski(X2,X3),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
          | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) )
        & ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
          | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) )
                  & ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( X0 = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | r2_hidden(k4_tarski(X2,X3),X0) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
              | X0 != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( X0 = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X0)
              <=> r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_relat_1)).

fof(f946,plain,
    ( r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2)
    | ~ r2_hidden(sK4(sK3,sK2),sK0) ),
    inference(superposition,[],[f101,f879])).

fof(f879,plain,(
    sK5(sK3,sK2) = k1_funct_1(sK2,sK4(sK3,sK2)) ),
    inference(duplicate_literal_removal,[],[f872])).

fof(f872,plain,
    ( sK5(sK3,sK2) = k1_funct_1(sK2,sK4(sK3,sK2))
    | sK5(sK3,sK2) = k1_funct_1(sK2,sK4(sK3,sK2)) ),
    inference(superposition,[],[f736,f433])).

fof(f433,plain,
    ( sK5(sK3,sK2) = k1_funct_1(sK3,sK4(sK3,sK2))
    | sK5(sK3,sK2) = k1_funct_1(sK2,sK4(sK3,sK2)) ),
    inference(resolution,[],[f224,f78])).

fof(f78,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
      | k1_funct_1(sK2,X2) = X3 ) ),
    inference(subsumption_resolution,[],[f75,f34])).

fof(f75,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
      | k1_funct_1(sK2,X2) = X3
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f55,f35])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f224,plain,
    ( r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2)
    | sK5(sK3,sK2) = k1_funct_1(sK3,sK4(sK3,sK2)) ),
    inference(resolution,[],[f136,f79])).

fof(f79,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),sK3)
      | k1_funct_1(sK3,X4) = X5 ) ),
    inference(subsumption_resolution,[],[f76,f36])).

fof(f76,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),sK3)
      | k1_funct_1(sK3,X4) = X5
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f55,f37])).

fof(f736,plain,(
    k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2)) ),
    inference(forward_demodulation,[],[f735,f715])).

fof(f715,plain,(
    k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(k5_relat_1(sK1,sK2),sK8(sK1,sK4(sK3,sK2))) ),
    inference(forward_demodulation,[],[f699,f229])).

fof(f229,plain,(
    sK4(sK3,sK2) = k1_funct_1(sK1,sK8(sK1,sK4(sK3,sK2))) ),
    inference(resolution,[],[f226,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK1,sK8(sK1,X0)) = X0 ) ),
    inference(forward_demodulation,[],[f92,f38])).

fof(f38,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | k1_funct_1(sK1,sK8(sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f89,f32])).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f89,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | k1_funct_1(sK1,sK8(sK1,X0)) = X0
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f61,f33])).

fof(f33,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    ! [X0,X5] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | k1_funct_1(X0,sK8(X0,X5)) = X5
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK8(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK6(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK6(X0,X1),X1) )
              & ( ( sK6(X0,X1) = k1_funct_1(X0,sK7(X0,X1))
                  & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK6(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK8(X0,X5)) = X5
                    & r2_hidden(sK8(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f25,f28,f27,f26])).

fof(f26,plain,(
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
              ( k1_funct_1(X0,X3) != sK6(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK6(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK6(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK6(X0,X1) = k1_funct_1(X0,sK7(X0,X1))
        & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK8(X0,X5)) = X5
        & r2_hidden(sK8(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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

fof(f699,plain,(
    k1_funct_1(sK2,k1_funct_1(sK1,sK8(sK1,sK4(sK3,sK2)))) = k1_funct_1(k5_relat_1(sK1,sK2),sK8(sK1,sK4(sK3,sK2))) ),
    inference(resolution,[],[f409,f226])).

fof(f409,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK2,k1_funct_1(sK1,sK8(sK1,X1))) = k1_funct_1(k5_relat_1(sK1,sK2),sK8(sK1,X1)) ) ),
    inference(forward_demodulation,[],[f408,f38])).

fof(f408,plain,(
    ! [X1] :
      ( k1_funct_1(sK2,k1_funct_1(sK1,sK8(sK1,X1))) = k1_funct_1(k5_relat_1(sK1,sK2),sK8(sK1,X1))
      | ~ r2_hidden(X1,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f407,f32])).

fof(f407,plain,(
    ! [X1] :
      ( k1_funct_1(sK2,k1_funct_1(sK1,sK8(sK1,X1))) = k1_funct_1(k5_relat_1(sK1,sK2),sK8(sK1,X1))
      | ~ r2_hidden(X1,k2_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f406,f33])).

fof(f406,plain,(
    ! [X1] :
      ( k1_funct_1(sK2,k1_funct_1(sK1,sK8(sK1,X1))) = k1_funct_1(k5_relat_1(sK1,sK2),sK8(sK1,X1))
      | ~ r2_hidden(X1,k2_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f263,f62])).

fof(f62,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK8(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK8(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f263,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK2,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0) ) ),
    inference(subsumption_resolution,[],[f260,f32])).

fof(f260,plain,(
    ! [X0] :
      ( k1_funct_1(sK2,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f124,f33])).

fof(f124,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_1(X3)
      | k1_funct_1(k5_relat_1(X3,sK2),X2) = k1_funct_1(sK2,k1_funct_1(X3,X2))
      | ~ r2_hidden(X2,k1_relat_1(X3))
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f121,f34])).

fof(f121,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_relat_1(X3))
      | k1_funct_1(k5_relat_1(X3,sK2),X2) = k1_funct_1(sK2,k1_funct_1(X3,X2))
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f53,f35])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

fof(f735,plain,(
    k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(k5_relat_1(sK1,sK2),sK8(sK1,sK4(sK3,sK2))) ),
    inference(forward_demodulation,[],[f718,f229])).

fof(f718,plain,(
    k1_funct_1(k5_relat_1(sK1,sK2),sK8(sK1,sK4(sK3,sK2))) = k1_funct_1(sK3,k1_funct_1(sK1,sK8(sK1,sK4(sK3,sK2)))) ),
    inference(resolution,[],[f420,f226])).

fof(f420,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | k1_funct_1(k5_relat_1(sK1,sK2),sK8(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,sK8(sK1,X1))) ) ),
    inference(forward_demodulation,[],[f419,f38])).

fof(f419,plain,(
    ! [X1] :
      ( k1_funct_1(k5_relat_1(sK1,sK2),sK8(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,sK8(sK1,X1)))
      | ~ r2_hidden(X1,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f418,f32])).

fof(f418,plain,(
    ! [X1] :
      ( k1_funct_1(k5_relat_1(sK1,sK2),sK8(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,sK8(sK1,X1)))
      | ~ r2_hidden(X1,k2_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f417,f33])).

fof(f417,plain,(
    ! [X1] :
      ( k1_funct_1(k5_relat_1(sK1,sK2),sK8(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,sK8(sK1,X1)))
      | ~ r2_hidden(X1,k2_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f285,f62])).

fof(f285,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0) ) ),
    inference(forward_demodulation,[],[f284,f41])).

fof(f41,plain,(
    k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f284,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK3),X0)
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f281,f32])).

fof(f281,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK3),X0)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f125,f33])).

fof(f125,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_1(X5)
      | k1_funct_1(k5_relat_1(X5,sK3),X4) = k1_funct_1(sK3,k1_funct_1(X5,X4))
      | ~ r2_hidden(X4,k1_relat_1(X5))
      | ~ v1_relat_1(X5) ) ),
    inference(subsumption_resolution,[],[f122,f36])).

fof(f122,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_relat_1(X5))
      | k1_funct_1(k5_relat_1(X5,sK3),X4) = k1_funct_1(sK3,k1_funct_1(X5,X4))
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(resolution,[],[f53,f37])).

fof(f101,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(sK2,X1)),sK2)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(forward_demodulation,[],[f100,f39])).

fof(f100,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK2))
      | r2_hidden(k4_tarski(X1,k1_funct_1(sK2,X1)),sK2) ) ),
    inference(subsumption_resolution,[],[f97,f34])).

fof(f97,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK2))
      | r2_hidden(k4_tarski(X1,k1_funct_1(sK2,X1)),sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f63,f35])).

fof(f63,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f998,plain,(
    ~ r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2) ),
    inference(resolution,[],[f882,f147])).

fof(f147,plain,
    ( ~ r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK3)
    | ~ r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2) ),
    inference(subsumption_resolution,[],[f146,f36])).

fof(f146,plain,
    ( ~ r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2)
    | ~ r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f138,f34])).

fof(f138,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2)
    | ~ r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(extensionality_resolution,[],[f46,f42])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | X0 = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f882,plain,(
    r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK3) ),
    inference(forward_demodulation,[],[f881,f879])).

fof(f881,plain,(
    r2_hidden(k4_tarski(sK4(sK3,sK2),k1_funct_1(sK2,sK4(sK3,sK2))),sK3) ),
    inference(subsumption_resolution,[],[f875,f226])).

fof(f875,plain,
    ( r2_hidden(k4_tarski(sK4(sK3,sK2),k1_funct_1(sK2,sK4(sK3,sK2))),sK3)
    | ~ r2_hidden(sK4(sK3,sK2),sK0) ),
    inference(superposition,[],[f103,f736])).

fof(f103,plain,(
    ! [X2] :
      ( r2_hidden(k4_tarski(X2,k1_funct_1(sK3,X2)),sK3)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(forward_demodulation,[],[f102,f40])).

fof(f102,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(sK3))
      | r2_hidden(k4_tarski(X2,k1_funct_1(sK3,X2)),sK3) ) ),
    inference(subsumption_resolution,[],[f98,f36])).

fof(f98,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(sK3))
      | r2_hidden(k4_tarski(X2,k1_funct_1(sK3,X2)),sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f63,f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:31:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (32226)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (32223)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.50  % (32227)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (32243)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.50  % (32241)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.50  % (32224)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (32228)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (32225)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (32244)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.50  % (32223)Refutation not found, incomplete strategy% (32223)------------------------------
% 0.22/0.50  % (32223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (32223)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (32223)Memory used [KB]: 10618
% 0.22/0.50  % (32223)Time elapsed: 0.049 s
% 0.22/0.50  % (32223)------------------------------
% 0.22/0.50  % (32223)------------------------------
% 0.22/0.51  % (32237)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (32231)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.51  % (32229)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (32235)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (32230)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (32233)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (32230)Refutation not found, incomplete strategy% (32230)------------------------------
% 0.22/0.52  % (32230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (32230)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (32230)Memory used [KB]: 1663
% 0.22/0.52  % (32230)Time elapsed: 0.105 s
% 0.22/0.52  % (32230)------------------------------
% 0.22/0.52  % (32230)------------------------------
% 0.22/0.52  % (32236)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (32238)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.52  % (32248)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.52  % (32240)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (32247)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.53  % (32245)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (32242)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.37/0.53  % (32246)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.37/0.54  % (32232)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.37/0.54  % (32239)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.37/0.55  % (32234)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.54/0.60  % (32239)Refutation found. Thanks to Tanya!
% 1.54/0.60  % SZS status Theorem for theBenchmark
% 1.54/0.60  % SZS output start Proof for theBenchmark
% 1.54/0.60  fof(f1001,plain,(
% 1.54/0.60    $false),
% 1.54/0.60    inference(subsumption_resolution,[],[f998,f949])).
% 1.54/0.60  fof(f949,plain,(
% 1.54/0.60    r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2)),
% 1.54/0.60    inference(subsumption_resolution,[],[f946,f226])).
% 1.54/0.60  fof(f226,plain,(
% 1.54/0.60    r2_hidden(sK4(sK3,sK2),sK0)),
% 1.54/0.60    inference(subsumption_resolution,[],[f225,f71])).
% 1.54/0.60  fof(f71,plain,(
% 1.54/0.60    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK2) | r2_hidden(X2,sK0)) )),
% 1.54/0.60    inference(forward_demodulation,[],[f70,f39])).
% 1.54/0.60  fof(f39,plain,(
% 1.54/0.60    sK0 = k1_relat_1(sK2)),
% 1.54/0.60    inference(cnf_transformation,[],[f19])).
% 1.54/0.60  fof(f19,plain,(
% 1.54/0.60    ((sK2 != sK3 & k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3) & sK0 = k1_relat_1(sK3) & sK0 = k1_relat_1(sK2) & sK0 = k2_relat_1(sK1) & v1_funct_1(sK3) & v1_relat_1(sK3)) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.54/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f18,f17,f16])).
% 1.54/0.60  fof(f16,plain,(
% 1.54/0.60    ? [X0,X1] : (? [X2] : (? [X3] : (X2 != X3 & k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0 & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (? [X3] : (X2 != X3 & k5_relat_1(sK1,X2) = k5_relat_1(sK1,X3) & k1_relat_1(X3) = sK0 & k1_relat_1(X2) = sK0 & sK0 = k2_relat_1(sK1) & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.54/0.60    introduced(choice_axiom,[])).
% 1.54/0.60  fof(f17,plain,(
% 1.54/0.60    ? [X2] : (? [X3] : (X2 != X3 & k5_relat_1(sK1,X2) = k5_relat_1(sK1,X3) & k1_relat_1(X3) = sK0 & k1_relat_1(X2) = sK0 & sK0 = k2_relat_1(sK1) & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(X2) & v1_relat_1(X2)) => (? [X3] : (sK2 != X3 & k5_relat_1(sK1,X3) = k5_relat_1(sK1,sK2) & k1_relat_1(X3) = sK0 & sK0 = k1_relat_1(sK2) & sK0 = k2_relat_1(sK1) & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.54/0.60    introduced(choice_axiom,[])).
% 1.54/0.60  fof(f18,plain,(
% 1.54/0.60    ? [X3] : (sK2 != X3 & k5_relat_1(sK1,X3) = k5_relat_1(sK1,sK2) & k1_relat_1(X3) = sK0 & sK0 = k1_relat_1(sK2) & sK0 = k2_relat_1(sK1) & v1_funct_1(X3) & v1_relat_1(X3)) => (sK2 != sK3 & k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3) & sK0 = k1_relat_1(sK3) & sK0 = k1_relat_1(sK2) & sK0 = k2_relat_1(sK1) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 1.54/0.60    introduced(choice_axiom,[])).
% 1.54/0.60  fof(f8,plain,(
% 1.54/0.60    ? [X0,X1] : (? [X2] : (? [X3] : (X2 != X3 & k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0 & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.54/0.60    inference(flattening,[],[f7])).
% 1.54/0.60  fof(f7,plain,(
% 1.54/0.60    ? [X0,X1] : (? [X2] : (? [X3] : ((X2 != X3 & (k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0)) & (v1_funct_1(X3) & v1_relat_1(X3))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.54/0.60    inference(ennf_transformation,[],[f6])).
% 1.54/0.60  fof(f6,negated_conjecture,(
% 1.54/0.60    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0) => X2 = X3))))),
% 1.54/0.60    inference(negated_conjecture,[],[f5])).
% 1.54/0.60  fof(f5,conjecture,(
% 1.54/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0) => X2 = X3))))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_funct_1)).
% 1.54/0.60  fof(f70,plain,(
% 1.54/0.60    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK2) | r2_hidden(X2,k1_relat_1(sK2))) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f67,f34])).
% 1.54/0.60  fof(f34,plain,(
% 1.54/0.60    v1_relat_1(sK2)),
% 1.54/0.60    inference(cnf_transformation,[],[f19])).
% 1.54/0.60  fof(f67,plain,(
% 1.54/0.60    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK2) | r2_hidden(X2,k1_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 1.54/0.60    inference(resolution,[],[f54,f35])).
% 1.54/0.60  fof(f35,plain,(
% 1.54/0.60    v1_funct_1(sK2)),
% 1.54/0.60    inference(cnf_transformation,[],[f19])).
% 1.54/0.60  fof(f54,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f31])).
% 1.54/0.60  fof(f31,plain,(
% 1.54/0.60    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.54/0.60    inference(flattening,[],[f30])).
% 1.54/0.60  fof(f30,plain,(
% 1.54/0.60    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.54/0.60    inference(nnf_transformation,[],[f15])).
% 1.54/0.60  fof(f15,plain,(
% 1.54/0.60    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.54/0.60    inference(flattening,[],[f14])).
% 1.54/0.60  fof(f14,plain,(
% 1.54/0.60    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.54/0.60    inference(ennf_transformation,[],[f4])).
% 1.54/0.60  fof(f4,axiom,(
% 1.54/0.60    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.54/0.60  fof(f225,plain,(
% 1.54/0.60    r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2) | r2_hidden(sK4(sK3,sK2),sK0)),
% 1.54/0.60    inference(resolution,[],[f136,f73])).
% 1.54/0.60  fof(f73,plain,(
% 1.54/0.60    ( ! [X4,X5] : (~r2_hidden(k4_tarski(X4,X5),sK3) | r2_hidden(X4,sK0)) )),
% 1.54/0.60    inference(forward_demodulation,[],[f72,f40])).
% 1.54/0.60  fof(f40,plain,(
% 1.54/0.60    sK0 = k1_relat_1(sK3)),
% 1.54/0.60    inference(cnf_transformation,[],[f19])).
% 1.54/0.60  fof(f72,plain,(
% 1.54/0.60    ( ! [X4,X5] : (~r2_hidden(k4_tarski(X4,X5),sK3) | r2_hidden(X4,k1_relat_1(sK3))) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f68,f36])).
% 1.54/0.60  fof(f36,plain,(
% 1.54/0.60    v1_relat_1(sK3)),
% 1.54/0.60    inference(cnf_transformation,[],[f19])).
% 1.54/0.60  fof(f68,plain,(
% 1.54/0.60    ( ! [X4,X5] : (~r2_hidden(k4_tarski(X4,X5),sK3) | r2_hidden(X4,k1_relat_1(sK3)) | ~v1_relat_1(sK3)) )),
% 1.54/0.60    inference(resolution,[],[f54,f37])).
% 1.54/0.60  fof(f37,plain,(
% 1.54/0.60    v1_funct_1(sK3)),
% 1.54/0.60    inference(cnf_transformation,[],[f19])).
% 1.54/0.60  fof(f136,plain,(
% 1.54/0.60    r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK3) | r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2)),
% 1.54/0.60    inference(subsumption_resolution,[],[f135,f36])).
% 1.54/0.60  fof(f135,plain,(
% 1.54/0.60    r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2) | r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK3) | ~v1_relat_1(sK3)),
% 1.54/0.60    inference(subsumption_resolution,[],[f127,f34])).
% 1.54/0.60  fof(f127,plain,(
% 1.54/0.60    ~v1_relat_1(sK2) | r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2) | r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK3) | ~v1_relat_1(sK3)),
% 1.54/0.60    inference(extensionality_resolution,[],[f45,f42])).
% 1.54/0.60  fof(f42,plain,(
% 1.54/0.60    sK2 != sK3),
% 1.54/0.60    inference(cnf_transformation,[],[f19])).
% 1.54/0.60  fof(f45,plain,(
% 1.54/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | X0 = X1 | ~v1_relat_1(X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f23])).
% 1.54/0.60  fof(f23,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : (((X0 = X1 | ((~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(k4_tarski(X4,X5),X1)) & (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0))) | X0 != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.54/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f21,f22])).
% 1.54/0.60  fof(f22,plain,(
% 1.54/0.60    ! [X1,X0] : (? [X2,X3] : ((~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r2_hidden(k4_tarski(X2,X3),X1) | r2_hidden(k4_tarski(X2,X3),X0))) => ((~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0))))),
% 1.54/0.60    introduced(choice_axiom,[])).
% 1.54/0.60  fof(f21,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : (((X0 = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r2_hidden(k4_tarski(X2,X3),X1) | r2_hidden(k4_tarski(X2,X3),X0)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(k4_tarski(X4,X5),X1)) & (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0))) | X0 != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.54/0.60    inference(rectify,[],[f20])).
% 1.54/0.60  fof(f20,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : (((X0 = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r2_hidden(k4_tarski(X2,X3),X1) | r2_hidden(k4_tarski(X2,X3),X0)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | X0 != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.54/0.60    inference(nnf_transformation,[],[f9])).
% 1.54/0.60  fof(f9,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : ((X0 = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) <=> r2_hidden(k4_tarski(X2,X3),X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.54/0.60    inference(ennf_transformation,[],[f1])).
% 1.54/0.60  fof(f1,axiom,(
% 1.54/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (X0 = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) <=> r2_hidden(k4_tarski(X2,X3),X1)))))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_relat_1)).
% 1.54/0.60  fof(f946,plain,(
% 1.54/0.60    r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2) | ~r2_hidden(sK4(sK3,sK2),sK0)),
% 1.54/0.60    inference(superposition,[],[f101,f879])).
% 1.54/0.60  fof(f879,plain,(
% 1.54/0.60    sK5(sK3,sK2) = k1_funct_1(sK2,sK4(sK3,sK2))),
% 1.54/0.60    inference(duplicate_literal_removal,[],[f872])).
% 1.54/0.60  fof(f872,plain,(
% 1.54/0.60    sK5(sK3,sK2) = k1_funct_1(sK2,sK4(sK3,sK2)) | sK5(sK3,sK2) = k1_funct_1(sK2,sK4(sK3,sK2))),
% 1.54/0.60    inference(superposition,[],[f736,f433])).
% 1.54/0.60  fof(f433,plain,(
% 1.54/0.60    sK5(sK3,sK2) = k1_funct_1(sK3,sK4(sK3,sK2)) | sK5(sK3,sK2) = k1_funct_1(sK2,sK4(sK3,sK2))),
% 1.54/0.60    inference(resolution,[],[f224,f78])).
% 1.54/0.60  fof(f78,plain,(
% 1.54/0.60    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK2) | k1_funct_1(sK2,X2) = X3) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f75,f34])).
% 1.54/0.60  fof(f75,plain,(
% 1.54/0.60    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK2) | k1_funct_1(sK2,X2) = X3 | ~v1_relat_1(sK2)) )),
% 1.54/0.60    inference(resolution,[],[f55,f35])).
% 1.54/0.60  fof(f55,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f31])).
% 1.54/0.60  fof(f224,plain,(
% 1.54/0.60    r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2) | sK5(sK3,sK2) = k1_funct_1(sK3,sK4(sK3,sK2))),
% 1.54/0.60    inference(resolution,[],[f136,f79])).
% 1.54/0.60  fof(f79,plain,(
% 1.54/0.60    ( ! [X4,X5] : (~r2_hidden(k4_tarski(X4,X5),sK3) | k1_funct_1(sK3,X4) = X5) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f76,f36])).
% 1.54/0.60  fof(f76,plain,(
% 1.54/0.60    ( ! [X4,X5] : (~r2_hidden(k4_tarski(X4,X5),sK3) | k1_funct_1(sK3,X4) = X5 | ~v1_relat_1(sK3)) )),
% 1.54/0.60    inference(resolution,[],[f55,f37])).
% 1.54/0.60  fof(f736,plain,(
% 1.54/0.60    k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2))),
% 1.54/0.60    inference(forward_demodulation,[],[f735,f715])).
% 1.54/0.60  fof(f715,plain,(
% 1.54/0.60    k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(k5_relat_1(sK1,sK2),sK8(sK1,sK4(sK3,sK2)))),
% 1.54/0.60    inference(forward_demodulation,[],[f699,f229])).
% 1.54/0.60  fof(f229,plain,(
% 1.54/0.60    sK4(sK3,sK2) = k1_funct_1(sK1,sK8(sK1,sK4(sK3,sK2)))),
% 1.54/0.60    inference(resolution,[],[f226,f93])).
% 1.54/0.60  fof(f93,plain,(
% 1.54/0.60    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(sK1,sK8(sK1,X0)) = X0) )),
% 1.54/0.60    inference(forward_demodulation,[],[f92,f38])).
% 1.54/0.60  fof(f38,plain,(
% 1.54/0.60    sK0 = k2_relat_1(sK1)),
% 1.54/0.60    inference(cnf_transformation,[],[f19])).
% 1.54/0.60  fof(f92,plain,(
% 1.54/0.60    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,sK8(sK1,X0)) = X0) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f89,f32])).
% 1.54/0.60  fof(f32,plain,(
% 1.54/0.60    v1_relat_1(sK1)),
% 1.54/0.60    inference(cnf_transformation,[],[f19])).
% 1.54/0.60  fof(f89,plain,(
% 1.54/0.60    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,sK8(sK1,X0)) = X0 | ~v1_relat_1(sK1)) )),
% 1.54/0.60    inference(resolution,[],[f61,f33])).
% 1.54/0.60  fof(f33,plain,(
% 1.54/0.60    v1_funct_1(sK1)),
% 1.54/0.60    inference(cnf_transformation,[],[f19])).
% 1.54/0.60  fof(f61,plain,(
% 1.54/0.60    ( ! [X0,X5] : (~v1_funct_1(X0) | ~r2_hidden(X5,k2_relat_1(X0)) | k1_funct_1(X0,sK8(X0,X5)) = X5 | ~v1_relat_1(X0)) )),
% 1.54/0.60    inference(equality_resolution,[],[f48])).
% 1.54/0.60  fof(f48,plain,(
% 1.54/0.60    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK8(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f29])).
% 1.54/0.60  fof(f29,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK6(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK6(X0,X1),X1)) & ((sK6(X0,X1) = k1_funct_1(X0,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK8(X0,X5)) = X5 & r2_hidden(sK8(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f25,f28,f27,f26])).
% 1.54/0.60  fof(f26,plain,(
% 1.54/0.60    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK6(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK6(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK6(X0,X1),X1))))),
% 1.54/0.60    introduced(choice_axiom,[])).
% 1.54/0.60  fof(f27,plain,(
% 1.54/0.60    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK6(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK6(X0,X1) = k1_funct_1(X0,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))))),
% 1.54/0.60    introduced(choice_axiom,[])).
% 1.54/0.60  fof(f28,plain,(
% 1.54/0.60    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK8(X0,X5)) = X5 & r2_hidden(sK8(X0,X5),k1_relat_1(X0))))),
% 1.54/0.60    introduced(choice_axiom,[])).
% 1.54/0.60  fof(f25,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.60    inference(rectify,[],[f24])).
% 1.54/0.60  fof(f24,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.60    inference(nnf_transformation,[],[f11])).
% 1.54/0.60  fof(f11,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.60    inference(flattening,[],[f10])).
% 1.54/0.60  fof(f10,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.54/0.60    inference(ennf_transformation,[],[f2])).
% 1.54/0.60  fof(f2,axiom,(
% 1.54/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 1.54/0.60  fof(f699,plain,(
% 1.54/0.60    k1_funct_1(sK2,k1_funct_1(sK1,sK8(sK1,sK4(sK3,sK2)))) = k1_funct_1(k5_relat_1(sK1,sK2),sK8(sK1,sK4(sK3,sK2)))),
% 1.54/0.60    inference(resolution,[],[f409,f226])).
% 1.54/0.60  fof(f409,plain,(
% 1.54/0.60    ( ! [X1] : (~r2_hidden(X1,sK0) | k1_funct_1(sK2,k1_funct_1(sK1,sK8(sK1,X1))) = k1_funct_1(k5_relat_1(sK1,sK2),sK8(sK1,X1))) )),
% 1.54/0.60    inference(forward_demodulation,[],[f408,f38])).
% 1.54/0.60  fof(f408,plain,(
% 1.54/0.60    ( ! [X1] : (k1_funct_1(sK2,k1_funct_1(sK1,sK8(sK1,X1))) = k1_funct_1(k5_relat_1(sK1,sK2),sK8(sK1,X1)) | ~r2_hidden(X1,k2_relat_1(sK1))) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f407,f32])).
% 1.54/0.60  fof(f407,plain,(
% 1.54/0.60    ( ! [X1] : (k1_funct_1(sK2,k1_funct_1(sK1,sK8(sK1,X1))) = k1_funct_1(k5_relat_1(sK1,sK2),sK8(sK1,X1)) | ~r2_hidden(X1,k2_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f406,f33])).
% 1.54/0.60  fof(f406,plain,(
% 1.54/0.60    ( ! [X1] : (k1_funct_1(sK2,k1_funct_1(sK1,sK8(sK1,X1))) = k1_funct_1(k5_relat_1(sK1,sK2),sK8(sK1,X1)) | ~r2_hidden(X1,k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.54/0.60    inference(resolution,[],[f263,f62])).
% 1.54/0.60  fof(f62,plain,(
% 1.54/0.60    ( ! [X0,X5] : (r2_hidden(sK8(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.60    inference(equality_resolution,[],[f47])).
% 1.54/0.60  fof(f47,plain,(
% 1.54/0.60    ( ! [X0,X5,X1] : (r2_hidden(sK8(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f29])).
% 1.54/0.60  fof(f263,plain,(
% 1.54/0.60    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK2,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0)) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f260,f32])).
% 1.54/0.60  fof(f260,plain,(
% 1.54/0.60    ( ! [X0] : (k1_funct_1(sK2,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 1.54/0.60    inference(resolution,[],[f124,f33])).
% 1.54/0.60  fof(f124,plain,(
% 1.54/0.60    ( ! [X2,X3] : (~v1_funct_1(X3) | k1_funct_1(k5_relat_1(X3,sK2),X2) = k1_funct_1(sK2,k1_funct_1(X3,X2)) | ~r2_hidden(X2,k1_relat_1(X3)) | ~v1_relat_1(X3)) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f121,f34])).
% 1.54/0.60  fof(f121,plain,(
% 1.54/0.60    ( ! [X2,X3] : (~r2_hidden(X2,k1_relat_1(X3)) | k1_funct_1(k5_relat_1(X3,sK2),X2) = k1_funct_1(sK2,k1_funct_1(X3,X2)) | ~v1_relat_1(sK2) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 1.54/0.60    inference(resolution,[],[f53,f35])).
% 1.54/0.60  fof(f53,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f13])).
% 1.54/0.60  fof(f13,plain,(
% 1.54/0.60    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.54/0.60    inference(flattening,[],[f12])).
% 1.54/0.60  fof(f12,plain,(
% 1.54/0.60    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.54/0.60    inference(ennf_transformation,[],[f3])).
% 1.54/0.60  fof(f3,axiom,(
% 1.54/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).
% 1.54/0.60  fof(f735,plain,(
% 1.54/0.60    k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(k5_relat_1(sK1,sK2),sK8(sK1,sK4(sK3,sK2)))),
% 1.54/0.60    inference(forward_demodulation,[],[f718,f229])).
% 1.54/0.60  fof(f718,plain,(
% 1.54/0.60    k1_funct_1(k5_relat_1(sK1,sK2),sK8(sK1,sK4(sK3,sK2))) = k1_funct_1(sK3,k1_funct_1(sK1,sK8(sK1,sK4(sK3,sK2))))),
% 1.54/0.60    inference(resolution,[],[f420,f226])).
% 1.54/0.60  fof(f420,plain,(
% 1.54/0.60    ( ! [X1] : (~r2_hidden(X1,sK0) | k1_funct_1(k5_relat_1(sK1,sK2),sK8(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,sK8(sK1,X1)))) )),
% 1.54/0.60    inference(forward_demodulation,[],[f419,f38])).
% 1.54/0.60  fof(f419,plain,(
% 1.54/0.60    ( ! [X1] : (k1_funct_1(k5_relat_1(sK1,sK2),sK8(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,sK8(sK1,X1))) | ~r2_hidden(X1,k2_relat_1(sK1))) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f418,f32])).
% 1.54/0.60  fof(f418,plain,(
% 1.54/0.60    ( ! [X1] : (k1_funct_1(k5_relat_1(sK1,sK2),sK8(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,sK8(sK1,X1))) | ~r2_hidden(X1,k2_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f417,f33])).
% 1.54/0.60  fof(f417,plain,(
% 1.54/0.60    ( ! [X1] : (k1_funct_1(k5_relat_1(sK1,sK2),sK8(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,sK8(sK1,X1))) | ~r2_hidden(X1,k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.54/0.60    inference(resolution,[],[f285,f62])).
% 1.54/0.60  fof(f285,plain,(
% 1.54/0.60    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0)) )),
% 1.54/0.60    inference(forward_demodulation,[],[f284,f41])).
% 1.54/0.60  fof(f41,plain,(
% 1.54/0.60    k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3)),
% 1.54/0.60    inference(cnf_transformation,[],[f19])).
% 1.54/0.60  fof(f284,plain,(
% 1.54/0.60    ( ! [X0] : (k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK3),X0) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f281,f32])).
% 1.54/0.60  fof(f281,plain,(
% 1.54/0.60    ( ! [X0] : (k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK3),X0) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 1.54/0.60    inference(resolution,[],[f125,f33])).
% 1.54/0.60  fof(f125,plain,(
% 1.54/0.60    ( ! [X4,X5] : (~v1_funct_1(X5) | k1_funct_1(k5_relat_1(X5,sK3),X4) = k1_funct_1(sK3,k1_funct_1(X5,X4)) | ~r2_hidden(X4,k1_relat_1(X5)) | ~v1_relat_1(X5)) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f122,f36])).
% 1.54/0.60  fof(f122,plain,(
% 1.54/0.60    ( ! [X4,X5] : (~r2_hidden(X4,k1_relat_1(X5)) | k1_funct_1(k5_relat_1(X5,sK3),X4) = k1_funct_1(sK3,k1_funct_1(X5,X4)) | ~v1_relat_1(sK3) | ~v1_funct_1(X5) | ~v1_relat_1(X5)) )),
% 1.54/0.60    inference(resolution,[],[f53,f37])).
% 1.54/0.60  fof(f101,plain,(
% 1.54/0.60    ( ! [X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(sK2,X1)),sK2) | ~r2_hidden(X1,sK0)) )),
% 1.54/0.60    inference(forward_demodulation,[],[f100,f39])).
% 1.54/0.60  fof(f100,plain,(
% 1.54/0.60    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK2)) | r2_hidden(k4_tarski(X1,k1_funct_1(sK2,X1)),sK2)) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f97,f34])).
% 1.54/0.60  fof(f97,plain,(
% 1.54/0.60    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK2)) | r2_hidden(k4_tarski(X1,k1_funct_1(sK2,X1)),sK2) | ~v1_relat_1(sK2)) )),
% 1.54/0.60    inference(resolution,[],[f63,f35])).
% 1.54/0.60  fof(f63,plain,(
% 1.54/0.60    ( ! [X2,X0] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_relat_1(X2)) )),
% 1.54/0.60    inference(equality_resolution,[],[f56])).
% 1.54/0.60  fof(f56,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f31])).
% 1.54/0.60  fof(f998,plain,(
% 1.54/0.60    ~r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2)),
% 1.54/0.60    inference(resolution,[],[f882,f147])).
% 1.54/0.60  fof(f147,plain,(
% 1.54/0.60    ~r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK3) | ~r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2)),
% 1.54/0.60    inference(subsumption_resolution,[],[f146,f36])).
% 1.54/0.60  fof(f146,plain,(
% 1.54/0.60    ~r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2) | ~r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK3) | ~v1_relat_1(sK3)),
% 1.54/0.60    inference(subsumption_resolution,[],[f138,f34])).
% 1.54/0.60  fof(f138,plain,(
% 1.54/0.60    ~v1_relat_1(sK2) | ~r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK2) | ~r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK3) | ~v1_relat_1(sK3)),
% 1.54/0.60    inference(extensionality_resolution,[],[f46,f42])).
% 1.54/0.60  fof(f46,plain,(
% 1.54/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | X0 = X1 | ~v1_relat_1(X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f23])).
% 1.54/0.60  fof(f882,plain,(
% 1.54/0.60    r2_hidden(k4_tarski(sK4(sK3,sK2),sK5(sK3,sK2)),sK3)),
% 1.54/0.60    inference(forward_demodulation,[],[f881,f879])).
% 1.54/0.60  fof(f881,plain,(
% 1.54/0.60    r2_hidden(k4_tarski(sK4(sK3,sK2),k1_funct_1(sK2,sK4(sK3,sK2))),sK3)),
% 1.54/0.60    inference(subsumption_resolution,[],[f875,f226])).
% 1.54/0.60  fof(f875,plain,(
% 1.54/0.60    r2_hidden(k4_tarski(sK4(sK3,sK2),k1_funct_1(sK2,sK4(sK3,sK2))),sK3) | ~r2_hidden(sK4(sK3,sK2),sK0)),
% 1.54/0.60    inference(superposition,[],[f103,f736])).
% 1.54/0.60  fof(f103,plain,(
% 1.54/0.60    ( ! [X2] : (r2_hidden(k4_tarski(X2,k1_funct_1(sK3,X2)),sK3) | ~r2_hidden(X2,sK0)) )),
% 1.54/0.60    inference(forward_demodulation,[],[f102,f40])).
% 1.54/0.60  fof(f102,plain,(
% 1.54/0.60    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(sK3)) | r2_hidden(k4_tarski(X2,k1_funct_1(sK3,X2)),sK3)) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f98,f36])).
% 1.54/0.60  fof(f98,plain,(
% 1.54/0.60    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(sK3)) | r2_hidden(k4_tarski(X2,k1_funct_1(sK3,X2)),sK3) | ~v1_relat_1(sK3)) )),
% 1.54/0.60    inference(resolution,[],[f63,f37])).
% 1.54/0.60  % SZS output end Proof for theBenchmark
% 1.54/0.60  % (32239)------------------------------
% 1.54/0.60  % (32239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.60  % (32239)Termination reason: Refutation
% 1.54/0.60  
% 1.54/0.60  % (32239)Memory used [KB]: 2174
% 1.54/0.60  % (32239)Time elapsed: 0.189 s
% 1.54/0.60  % (32239)------------------------------
% 1.54/0.60  % (32239)------------------------------
% 1.54/0.60  % (32222)Success in time 0.239 s
%------------------------------------------------------------------------------
