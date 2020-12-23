%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:11 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 657 expanded)
%              Number of leaves         :   11 ( 252 expanded)
%              Depth                    :   18
%              Number of atoms          :  430 (7042 expanded)
%              Number of equality atoms :  171 (3408 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f688,plain,(
    $false ),
    inference(subsumption_resolution,[],[f687,f277])).

fof(f277,plain,(
    k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) ),
    inference(subsumption_resolution,[],[f276,f28])).

fof(f28,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f16,f15,f14])).

fof(f14,plain,
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

fof(f15,plain,
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

fof(f16,plain,
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
    inference(flattening,[],[f6])).

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
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
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_funct_1)).

fof(f276,plain,
    ( k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f275,f29])).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f275,plain,
    ( k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f274,f36])).

fof(f36,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f17])).

fof(f274,plain,
    ( k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f272])).

fof(f272,plain,
    ( sK0 != sK0
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f125,f33])).

fof(f33,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f125,plain,(
    ! [X1] :
      ( k1_relat_1(X1) != sK0
      | k1_funct_1(sK3,sK4(sK3,X1)) != k1_funct_1(X1,sK4(sK3,X1))
      | sK3 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f124,f30])).

fof(f30,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f124,plain,(
    ! [X1] :
      ( k1_relat_1(X1) != sK0
      | k1_funct_1(sK3,sK4(sK3,X1)) != k1_funct_1(X1,sK4(sK3,X1))
      | sK3 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f117,f31])).

fof(f31,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f117,plain,(
    ! [X1] :
      ( k1_relat_1(X1) != sK0
      | k1_funct_1(sK3,sK4(sK3,X1)) != k1_funct_1(X1,sK4(sK3,X1))
      | sK3 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f38,f34])).

fof(f34,plain,(
    sK0 = k1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k1_relat_1(X1)
      | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
            & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f9,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(f687,plain,(
    k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2)) ),
    inference(forward_demodulation,[],[f686,f663])).

fof(f663,plain,(
    k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK3,sK2))) ),
    inference(forward_demodulation,[],[f647,f168])).

fof(f168,plain,(
    sK4(sK3,sK2) = k1_funct_1(sK1,sK7(sK1,sK4(sK3,sK2))) ),
    inference(resolution,[],[f165,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK1,sK7(sK1,X0)) = X0 ) ),
    inference(forward_demodulation,[],[f62,f32])).

fof(f32,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | k1_funct_1(sK1,sK7(sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f59,f26])).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | k1_funct_1(sK1,sK7(sK1,X0)) = X0
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f48,f27])).

fof(f27,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X0,X5] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | k1_funct_1(X0,sK7(X0,X5)) = X5
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK7(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK5(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK5(X0,X1),X1) )
              & ( ( sK5(X0,X1) = k1_funct_1(X0,sK6(X0,X1))
                  & r2_hidden(sK6(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK5(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK7(X0,X5)) = X5
                    & r2_hidden(sK7(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f21,f24,f23,f22])).

fof(f22,plain,(
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
              ( k1_funct_1(X0,X3) != sK5(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK5(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK5(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK5(X0,X1) = k1_funct_1(X0,sK6(X0,X1))
        & r2_hidden(sK6(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X5)) = X5
        & r2_hidden(sK7(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f165,plain,(
    r2_hidden(sK4(sK3,sK2),sK0) ),
    inference(subsumption_resolution,[],[f164,f30])).

fof(f164,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f163,f31])).

fof(f163,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f162,f36])).

fof(f162,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(trivial_inequality_removal,[],[f161])).

fof(f161,plain,
    ( sK0 != sK0
    | r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f86,f34])).

fof(f86,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK0
      | r2_hidden(sK4(X0,sK2),k1_relat_1(X0))
      | sK2 = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f85,f28])).

fof(f85,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK0
      | r2_hidden(sK4(X0,sK2),k1_relat_1(X0))
      | sK2 = X0
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f77,f29])).

fof(f77,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK0
      | r2_hidden(sK4(X0,sK2),k1_relat_1(X0))
      | sK2 = X0
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f37,f33])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k1_relat_1(X1)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f647,plain,(
    k1_funct_1(sK2,k1_funct_1(sK1,sK7(sK1,sK4(sK3,sK2)))) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK3,sK2))) ),
    inference(resolution,[],[f396,f165])).

fof(f396,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK2,k1_funct_1(sK1,sK7(sK1,X1))) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,X1)) ) ),
    inference(forward_demodulation,[],[f395,f32])).

fof(f395,plain,(
    ! [X1] :
      ( k1_funct_1(sK2,k1_funct_1(sK1,sK7(sK1,X1))) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,X1))
      | ~ r2_hidden(X1,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f394,f26])).

fof(f394,plain,(
    ! [X1] :
      ( k1_funct_1(sK2,k1_funct_1(sK1,sK7(sK1,X1))) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,X1))
      | ~ r2_hidden(X1,k2_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f393,f27])).

fof(f393,plain,(
    ! [X1] :
      ( k1_funct_1(sK2,k1_funct_1(sK1,sK7(sK1,X1))) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,X1))
      | ~ r2_hidden(X1,k2_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f237,f49])).

fof(f49,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK7(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK7(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f237,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK2,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0) ) ),
    inference(subsumption_resolution,[],[f234,f26])).

fof(f234,plain,(
    ! [X0] :
      ( k1_funct_1(sK2,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f107,f27])).

fof(f107,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_1(X3)
      | k1_funct_1(k5_relat_1(X3,sK2),X2) = k1_funct_1(sK2,k1_funct_1(X3,X2))
      | ~ r2_hidden(X2,k1_relat_1(X3))
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f104,f28])).

fof(f104,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_relat_1(X3))
      | k1_funct_1(k5_relat_1(X3,sK2),X2) = k1_funct_1(sK2,k1_funct_1(X3,X2))
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f45,f29])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f686,plain,(
    k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK3,sK2))) ),
    inference(forward_demodulation,[],[f670,f168])).

fof(f670,plain,(
    k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK3,sK2))) = k1_funct_1(sK3,k1_funct_1(sK1,sK7(sK1,sK4(sK3,sK2)))) ),
    inference(resolution,[],[f407,f165])).

fof(f407,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,sK7(sK1,X1))) ) ),
    inference(forward_demodulation,[],[f406,f32])).

fof(f406,plain,(
    ! [X1] :
      ( k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,sK7(sK1,X1)))
      | ~ r2_hidden(X1,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f405,f26])).

fof(f405,plain,(
    ! [X1] :
      ( k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,sK7(sK1,X1)))
      | ~ r2_hidden(X1,k2_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f404,f27])).

fof(f404,plain,(
    ! [X1] :
      ( k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,sK7(sK1,X1)))
      | ~ r2_hidden(X1,k2_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f246,f49])).

fof(f246,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0) ) ),
    inference(forward_demodulation,[],[f245,f35])).

fof(f35,plain,(
    k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f245,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK3),X0)
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f242,f26])).

fof(f242,plain,(
    ! [X0] :
      ( k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK3),X0)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f108,f27])).

fof(f108,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_1(X5)
      | k1_funct_1(k5_relat_1(X5,sK3),X4) = k1_funct_1(sK3,k1_funct_1(X5,X4))
      | ~ r2_hidden(X4,k1_relat_1(X5))
      | ~ v1_relat_1(X5) ) ),
    inference(subsumption_resolution,[],[f105,f30])).

fof(f105,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k1_relat_1(X5))
      | k1_funct_1(k5_relat_1(X5,sK3),X4) = k1_funct_1(sK3,k1_funct_1(X5,X4))
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(resolution,[],[f45,f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:08:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.46  % (28268)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.19/0.46  % (28260)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.19/0.48  % (28252)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.49  % (28267)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.19/0.49  % (28253)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.49  % (28255)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.19/0.50  % (28269)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.19/0.50  % (28271)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.19/0.51  % (28251)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.51  % (28264)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.51  % (28263)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.19/0.51  % (28265)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.51  % (28273)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.51  % (28267)Refutation found. Thanks to Tanya!
% 0.19/0.51  % SZS status Theorem for theBenchmark
% 0.19/0.51  % (28254)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.51  % SZS output start Proof for theBenchmark
% 0.19/0.51  fof(f688,plain,(
% 0.19/0.51    $false),
% 0.19/0.51    inference(subsumption_resolution,[],[f687,f277])).
% 0.19/0.51  fof(f277,plain,(
% 0.19/0.51    k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))),
% 0.19/0.51    inference(subsumption_resolution,[],[f276,f28])).
% 0.19/0.51  fof(f28,plain,(
% 0.19/0.51    v1_relat_1(sK2)),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f17,plain,(
% 0.19/0.51    ((sK2 != sK3 & k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3) & sK0 = k1_relat_1(sK3) & sK0 = k1_relat_1(sK2) & sK0 = k2_relat_1(sK1) & v1_funct_1(sK3) & v1_relat_1(sK3)) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f16,f15,f14])).
% 0.19/0.51  fof(f14,plain,(
% 0.19/0.51    ? [X0,X1] : (? [X2] : (? [X3] : (X2 != X3 & k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0 & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (? [X3] : (X2 != X3 & k5_relat_1(sK1,X2) = k5_relat_1(sK1,X3) & k1_relat_1(X3) = sK0 & k1_relat_1(X2) = sK0 & sK0 = k2_relat_1(sK1) & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f15,plain,(
% 0.19/0.51    ? [X2] : (? [X3] : (X2 != X3 & k5_relat_1(sK1,X2) = k5_relat_1(sK1,X3) & k1_relat_1(X3) = sK0 & k1_relat_1(X2) = sK0 & sK0 = k2_relat_1(sK1) & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(X2) & v1_relat_1(X2)) => (? [X3] : (sK2 != X3 & k5_relat_1(sK1,X3) = k5_relat_1(sK1,sK2) & k1_relat_1(X3) = sK0 & sK0 = k1_relat_1(sK2) & sK0 = k2_relat_1(sK1) & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f16,plain,(
% 0.19/0.51    ? [X3] : (sK2 != X3 & k5_relat_1(sK1,X3) = k5_relat_1(sK1,sK2) & k1_relat_1(X3) = sK0 & sK0 = k1_relat_1(sK2) & sK0 = k2_relat_1(sK1) & v1_funct_1(X3) & v1_relat_1(X3)) => (sK2 != sK3 & k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3) & sK0 = k1_relat_1(sK3) & sK0 = k1_relat_1(sK2) & sK0 = k2_relat_1(sK1) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f7,plain,(
% 0.19/0.51    ? [X0,X1] : (? [X2] : (? [X3] : (X2 != X3 & k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0 & v1_funct_1(X3) & v1_relat_1(X3)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.19/0.51    inference(flattening,[],[f6])).
% 0.19/0.51  fof(f6,plain,(
% 0.19/0.51    ? [X0,X1] : (? [X2] : (? [X3] : ((X2 != X3 & (k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0)) & (v1_funct_1(X3) & v1_relat_1(X3))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.19/0.51    inference(ennf_transformation,[],[f5])).
% 0.19/0.51  fof(f5,negated_conjecture,(
% 0.19/0.51    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0) => X2 = X3))))),
% 0.19/0.51    inference(negated_conjecture,[],[f4])).
% 0.19/0.51  fof(f4,conjecture,(
% 0.19/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X1,X2) = k5_relat_1(X1,X3) & k1_relat_1(X3) = X0 & k1_relat_1(X2) = X0 & k2_relat_1(X1) = X0) => X2 = X3))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_funct_1)).
% 0.19/0.51  fof(f276,plain,(
% 0.19/0.51    k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | ~v1_relat_1(sK2)),
% 0.19/0.51    inference(subsumption_resolution,[],[f275,f29])).
% 0.19/0.51  fof(f29,plain,(
% 0.19/0.51    v1_funct_1(sK2)),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f275,plain,(
% 0.19/0.51    k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.19/0.51    inference(subsumption_resolution,[],[f274,f36])).
% 0.19/0.51  fof(f36,plain,(
% 0.19/0.51    sK2 != sK3),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f274,plain,(
% 0.19/0.51    k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.19/0.51    inference(trivial_inequality_removal,[],[f272])).
% 0.19/0.51  fof(f272,plain,(
% 0.19/0.51    sK0 != sK0 | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.19/0.51    inference(superposition,[],[f125,f33])).
% 0.19/0.51  fof(f33,plain,(
% 0.19/0.51    sK0 = k1_relat_1(sK2)),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f125,plain,(
% 0.19/0.51    ( ! [X1] : (k1_relat_1(X1) != sK0 | k1_funct_1(sK3,sK4(sK3,X1)) != k1_funct_1(X1,sK4(sK3,X1)) | sK3 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f124,f30])).
% 0.19/0.51  fof(f30,plain,(
% 0.19/0.51    v1_relat_1(sK3)),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f124,plain,(
% 0.19/0.51    ( ! [X1] : (k1_relat_1(X1) != sK0 | k1_funct_1(sK3,sK4(sK3,X1)) != k1_funct_1(X1,sK4(sK3,X1)) | sK3 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(sK3)) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f117,f31])).
% 0.19/0.51  fof(f31,plain,(
% 0.19/0.51    v1_funct_1(sK3)),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f117,plain,(
% 0.19/0.51    ( ! [X1] : (k1_relat_1(X1) != sK0 | k1_funct_1(sK3,sK4(sK3,X1)) != k1_funct_1(X1,sK4(sK3,X1)) | sK3 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 0.19/0.51    inference(superposition,[],[f38,f34])).
% 0.19/0.51  fof(f34,plain,(
% 0.19/0.51    sK0 = k1_relat_1(sK3)),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f38,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_relat_1(X0) != k1_relat_1(X1) | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f19])).
% 0.19/0.51  fof(f19,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f9,f18])).
% 0.19/0.51  fof(f18,plain,(
% 0.19/0.51    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f9,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.51    inference(flattening,[],[f8])).
% 0.19/0.51  fof(f8,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f3])).
% 0.19/0.51  fof(f3,axiom,(
% 0.19/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 0.19/0.51  fof(f687,plain,(
% 0.19/0.51    k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2))),
% 0.19/0.51    inference(forward_demodulation,[],[f686,f663])).
% 0.19/0.51  fof(f663,plain,(
% 0.19/0.51    k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK3,sK2)))),
% 0.19/0.51    inference(forward_demodulation,[],[f647,f168])).
% 0.19/0.51  fof(f168,plain,(
% 0.19/0.51    sK4(sK3,sK2) = k1_funct_1(sK1,sK7(sK1,sK4(sK3,sK2)))),
% 0.19/0.51    inference(resolution,[],[f165,f63])).
% 0.19/0.51  fof(f63,plain,(
% 0.19/0.51    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(sK1,sK7(sK1,X0)) = X0) )),
% 0.19/0.51    inference(forward_demodulation,[],[f62,f32])).
% 0.19/0.51  fof(f32,plain,(
% 0.19/0.51    sK0 = k2_relat_1(sK1)),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f62,plain,(
% 0.19/0.51    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,sK7(sK1,X0)) = X0) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f59,f26])).
% 0.19/0.51  fof(f26,plain,(
% 0.19/0.51    v1_relat_1(sK1)),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f59,plain,(
% 0.19/0.51    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,sK7(sK1,X0)) = X0 | ~v1_relat_1(sK1)) )),
% 0.19/0.51    inference(resolution,[],[f48,f27])).
% 0.19/0.51  fof(f27,plain,(
% 0.19/0.51    v1_funct_1(sK1)),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f48,plain,(
% 0.19/0.51    ( ! [X0,X5] : (~v1_funct_1(X0) | ~r2_hidden(X5,k2_relat_1(X0)) | k1_funct_1(X0,sK7(X0,X5)) = X5 | ~v1_relat_1(X0)) )),
% 0.19/0.51    inference(equality_resolution,[],[f40])).
% 0.19/0.51  fof(f40,plain,(
% 0.19/0.51    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK7(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f25])).
% 0.19/0.51  fof(f25,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK5(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1),X1)) & ((sK5(X0,X1) = k1_funct_1(X0,sK6(X0,X1)) & r2_hidden(sK6(X0,X1),k1_relat_1(X0))) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK7(X0,X5)) = X5 & r2_hidden(sK7(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f21,f24,f23,f22])).
% 0.19/0.51  fof(f22,plain,(
% 0.19/0.51    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK5(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK5(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK5(X0,X1),X1))))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f23,plain,(
% 0.19/0.51    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK5(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK5(X0,X1) = k1_funct_1(X0,sK6(X0,X1)) & r2_hidden(sK6(X0,X1),k1_relat_1(X0))))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f24,plain,(
% 0.19/0.51    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK7(X0,X5)) = X5 & r2_hidden(sK7(X0,X5),k1_relat_1(X0))))),
% 0.19/0.51    introduced(choice_axiom,[])).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.51    inference(rectify,[],[f20])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.51    inference(nnf_transformation,[],[f11])).
% 0.19/0.51  fof(f11,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.51    inference(flattening,[],[f10])).
% 0.19/0.51  fof(f10,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.19/0.51  fof(f165,plain,(
% 0.19/0.51    r2_hidden(sK4(sK3,sK2),sK0)),
% 0.19/0.51    inference(subsumption_resolution,[],[f164,f30])).
% 0.19/0.51  fof(f164,plain,(
% 0.19/0.51    r2_hidden(sK4(sK3,sK2),sK0) | ~v1_relat_1(sK3)),
% 0.19/0.51    inference(subsumption_resolution,[],[f163,f31])).
% 0.19/0.51  fof(f163,plain,(
% 0.19/0.51    r2_hidden(sK4(sK3,sK2),sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.19/0.51    inference(subsumption_resolution,[],[f162,f36])).
% 0.19/0.51  fof(f162,plain,(
% 0.19/0.51    r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.19/0.51    inference(trivial_inequality_removal,[],[f161])).
% 0.19/0.51  fof(f161,plain,(
% 0.19/0.51    sK0 != sK0 | r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.19/0.51    inference(superposition,[],[f86,f34])).
% 0.19/0.51  fof(f86,plain,(
% 0.19/0.51    ( ! [X0] : (k1_relat_1(X0) != sK0 | r2_hidden(sK4(X0,sK2),k1_relat_1(X0)) | sK2 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f85,f28])).
% 0.19/0.51  fof(f85,plain,(
% 0.19/0.51    ( ! [X0] : (k1_relat_1(X0) != sK0 | r2_hidden(sK4(X0,sK2),k1_relat_1(X0)) | sK2 = X0 | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f77,f29])).
% 0.19/0.51  fof(f77,plain,(
% 0.19/0.51    ( ! [X0] : (k1_relat_1(X0) != sK0 | r2_hidden(sK4(X0,sK2),k1_relat_1(X0)) | sK2 = X0 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.51    inference(superposition,[],[f37,f33])).
% 0.19/0.51  fof(f37,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f19])).
% 0.19/0.51  fof(f647,plain,(
% 0.19/0.51    k1_funct_1(sK2,k1_funct_1(sK1,sK7(sK1,sK4(sK3,sK2)))) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK3,sK2)))),
% 0.19/0.51    inference(resolution,[],[f396,f165])).
% 0.19/0.52  fof(f396,plain,(
% 0.19/0.52    ( ! [X1] : (~r2_hidden(X1,sK0) | k1_funct_1(sK2,k1_funct_1(sK1,sK7(sK1,X1))) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,X1))) )),
% 0.19/0.52    inference(forward_demodulation,[],[f395,f32])).
% 0.19/0.52  fof(f395,plain,(
% 0.19/0.52    ( ! [X1] : (k1_funct_1(sK2,k1_funct_1(sK1,sK7(sK1,X1))) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,X1)) | ~r2_hidden(X1,k2_relat_1(sK1))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f394,f26])).
% 0.19/0.52  fof(f394,plain,(
% 0.19/0.52    ( ! [X1] : (k1_funct_1(sK2,k1_funct_1(sK1,sK7(sK1,X1))) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,X1)) | ~r2_hidden(X1,k2_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f393,f27])).
% 0.19/0.52  fof(f393,plain,(
% 0.19/0.52    ( ! [X1] : (k1_funct_1(sK2,k1_funct_1(sK1,sK7(sK1,X1))) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,X1)) | ~r2_hidden(X1,k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.19/0.52    inference(resolution,[],[f237,f49])).
% 0.19/0.52  fof(f49,plain,(
% 0.19/0.52    ( ! [X0,X5] : (r2_hidden(sK7(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.52    inference(equality_resolution,[],[f39])).
% 0.19/0.52  fof(f39,plain,(
% 0.19/0.52    ( ! [X0,X5,X1] : (r2_hidden(sK7(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f25])).
% 0.19/0.52  fof(f237,plain,(
% 0.19/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK2,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f234,f26])).
% 0.19/0.52  fof(f234,plain,(
% 0.19/0.52    ( ! [X0] : (k1_funct_1(sK2,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.19/0.52    inference(resolution,[],[f107,f27])).
% 0.19/0.52  fof(f107,plain,(
% 0.19/0.52    ( ! [X2,X3] : (~v1_funct_1(X3) | k1_funct_1(k5_relat_1(X3,sK2),X2) = k1_funct_1(sK2,k1_funct_1(X3,X2)) | ~r2_hidden(X2,k1_relat_1(X3)) | ~v1_relat_1(X3)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f104,f28])).
% 0.19/0.52  fof(f104,plain,(
% 0.19/0.52    ( ! [X2,X3] : (~r2_hidden(X2,k1_relat_1(X3)) | k1_funct_1(k5_relat_1(X3,sK2),X2) = k1_funct_1(sK2,k1_funct_1(X3,X2)) | ~v1_relat_1(sK2) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) )),
% 0.19/0.52    inference(resolution,[],[f45,f29])).
% 0.19/0.52  fof(f45,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f13])).
% 0.19/0.52  fof(f13,plain,(
% 0.19/0.52    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(flattening,[],[f12])).
% 0.19/0.52  fof(f12,plain,(
% 0.19/0.52    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.52    inference(ennf_transformation,[],[f2])).
% 0.19/0.52  fof(f2,axiom,(
% 0.19/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 0.19/0.52  fof(f686,plain,(
% 0.19/0.52    k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK3,sK2)))),
% 0.19/0.52    inference(forward_demodulation,[],[f670,f168])).
% 0.19/0.52  fof(f670,plain,(
% 0.19/0.52    k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,sK4(sK3,sK2))) = k1_funct_1(sK3,k1_funct_1(sK1,sK7(sK1,sK4(sK3,sK2))))),
% 0.19/0.52    inference(resolution,[],[f407,f165])).
% 0.19/0.52  fof(f407,plain,(
% 0.19/0.52    ( ! [X1] : (~r2_hidden(X1,sK0) | k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,sK7(sK1,X1)))) )),
% 0.19/0.52    inference(forward_demodulation,[],[f406,f32])).
% 0.19/0.52  fof(f406,plain,(
% 0.19/0.52    ( ! [X1] : (k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,sK7(sK1,X1))) | ~r2_hidden(X1,k2_relat_1(sK1))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f405,f26])).
% 0.19/0.52  fof(f405,plain,(
% 0.19/0.52    ( ! [X1] : (k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,sK7(sK1,X1))) | ~r2_hidden(X1,k2_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f404,f27])).
% 0.19/0.52  fof(f404,plain,(
% 0.19/0.52    ( ! [X1] : (k1_funct_1(k5_relat_1(sK1,sK2),sK7(sK1,X1)) = k1_funct_1(sK3,k1_funct_1(sK1,sK7(sK1,X1))) | ~r2_hidden(X1,k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.19/0.52    inference(resolution,[],[f246,f49])).
% 0.19/0.52  fof(f246,plain,(
% 0.19/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK2),X0)) )),
% 0.19/0.52    inference(forward_demodulation,[],[f245,f35])).
% 0.19/0.52  fof(f35,plain,(
% 0.19/0.52    k5_relat_1(sK1,sK2) = k5_relat_1(sK1,sK3)),
% 0.19/0.52    inference(cnf_transformation,[],[f17])).
% 0.19/0.52  fof(f245,plain,(
% 0.19/0.52    ( ! [X0] : (k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK3),X0) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f242,f26])).
% 0.19/0.52  fof(f242,plain,(
% 0.19/0.52    ( ! [X0] : (k1_funct_1(sK3,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK3),X0) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.19/0.52    inference(resolution,[],[f108,f27])).
% 0.19/0.52  fof(f108,plain,(
% 0.19/0.52    ( ! [X4,X5] : (~v1_funct_1(X5) | k1_funct_1(k5_relat_1(X5,sK3),X4) = k1_funct_1(sK3,k1_funct_1(X5,X4)) | ~r2_hidden(X4,k1_relat_1(X5)) | ~v1_relat_1(X5)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f105,f30])).
% 0.19/0.52  fof(f105,plain,(
% 0.19/0.52    ( ! [X4,X5] : (~r2_hidden(X4,k1_relat_1(X5)) | k1_funct_1(k5_relat_1(X5,sK3),X4) = k1_funct_1(sK3,k1_funct_1(X5,X4)) | ~v1_relat_1(sK3) | ~v1_funct_1(X5) | ~v1_relat_1(X5)) )),
% 0.19/0.52    inference(resolution,[],[f45,f31])).
% 0.19/0.52  % SZS output end Proof for theBenchmark
% 0.19/0.52  % (28267)------------------------------
% 0.19/0.52  % (28267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (28267)Termination reason: Refutation
% 0.19/0.52  
% 0.19/0.52  % (28267)Memory used [KB]: 2046
% 0.19/0.52  % (28267)Time elapsed: 0.098 s
% 0.19/0.52  % (28267)------------------------------
% 0.19/0.52  % (28267)------------------------------
% 0.19/0.52  % (28256)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.52  % (28261)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.19/0.52  % (28250)Success in time 0.163 s
%------------------------------------------------------------------------------
