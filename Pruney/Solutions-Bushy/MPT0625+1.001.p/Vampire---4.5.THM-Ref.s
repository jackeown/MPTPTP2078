%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0625+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:20 EST 2020

% Result     : Theorem 5.14s
% Output     : Refutation 5.14s
% Verified   : 
% Statistics : Number of formulae       :  118 (12376 expanded)
%              Number of leaves         :   13 (3995 expanded)
%              Depth                    :   35
%              Number of atoms          :  575 (150285 expanded)
%              Number of equality atoms :  128 (24044 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5531,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5524,f5504])).

fof(f5504,plain,(
    r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK2) ),
    inference(backward_demodulation,[],[f5452,f5496])).

fof(f5496,plain,(
    sK4(sK0,sK1,sK2) = k1_funct_1(sK1,sK5(sK0,sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f5488])).

fof(f5488,plain,
    ( sK4(sK0,sK1,sK2) = k1_funct_1(sK1,sK5(sK0,sK1,sK2))
    | sK4(sK0,sK1,sK2) = k1_funct_1(sK1,sK5(sK0,sK1,sK2)) ),
    inference(superposition,[],[f5442,f3282])).

fof(f3282,plain,
    ( sK4(sK0,sK1,sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK2))
    | sK4(sK0,sK1,sK2) = k1_funct_1(sK1,sK5(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f3279,f41])).

fof(f41,plain,(
    k5_relat_1(sK0,sK1) != sK2 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k5_relat_1(sK0,sK1) != sK2
    & ! [X3] :
        ( k1_funct_1(sK1,k1_funct_1(sK0,X3)) = k1_funct_1(sK2,X3)
        | ~ r2_hidden(X3,k1_relat_1(sK2)) )
    & ! [X4] :
        ( ( r2_hidden(X4,k1_relat_1(sK2))
          | ~ r2_hidden(k1_funct_1(sK0,X4),k1_relat_1(sK1))
          | ~ r2_hidden(X4,k1_relat_1(sK0)) )
        & ( ( r2_hidden(k1_funct_1(sK0,X4),k1_relat_1(sK1))
            & r2_hidden(X4,k1_relat_1(sK0)) )
          | ~ r2_hidden(X4,k1_relat_1(sK2)) ) )
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16,f15,f14])).

% (12966)Time limit reached!
% (12966)------------------------------
% (12966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k5_relat_1(X0,X1) != X2
                & ! [X3] :
                    ( k1_funct_1(X2,X3) = k1_funct_1(X1,k1_funct_1(X0,X3))
                    | ~ r2_hidden(X3,k1_relat_1(X2)) )
                & ! [X4] :
                    ( ( r2_hidden(X4,k1_relat_1(X2))
                      | ~ r2_hidden(k1_funct_1(X0,X4),k1_relat_1(X1))
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                    & ( ( r2_hidden(k1_funct_1(X0,X4),k1_relat_1(X1))
                        & r2_hidden(X4,k1_relat_1(X0)) )
                      | ~ r2_hidden(X4,k1_relat_1(X2)) ) )
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k5_relat_1(sK0,X1) != X2
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,k1_funct_1(sK0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X2)) )
              & ! [X4] :
                  ( ( r2_hidden(X4,k1_relat_1(X2))
                    | ~ r2_hidden(k1_funct_1(sK0,X4),k1_relat_1(X1))
                    | ~ r2_hidden(X4,k1_relat_1(sK0)) )
                  & ( ( r2_hidden(k1_funct_1(sK0,X4),k1_relat_1(X1))
                      & r2_hidden(X4,k1_relat_1(sK0)) )
                    | ~ r2_hidden(X4,k1_relat_1(X2)) ) )
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k5_relat_1(sK0,X1) != X2
            & ! [X3] :
                ( k1_funct_1(X2,X3) = k1_funct_1(X1,k1_funct_1(sK0,X3))
                | ~ r2_hidden(X3,k1_relat_1(X2)) )
            & ! [X4] :
                ( ( r2_hidden(X4,k1_relat_1(X2))
                  | ~ r2_hidden(k1_funct_1(sK0,X4),k1_relat_1(X1))
                  | ~ r2_hidden(X4,k1_relat_1(sK0)) )
                & ( ( r2_hidden(k1_funct_1(sK0,X4),k1_relat_1(X1))
                    & r2_hidden(X4,k1_relat_1(sK0)) )
                  | ~ r2_hidden(X4,k1_relat_1(X2)) ) )
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k5_relat_1(sK0,sK1) != X2
          & ! [X3] :
              ( k1_funct_1(X2,X3) = k1_funct_1(sK1,k1_funct_1(sK0,X3))
              | ~ r2_hidden(X3,k1_relat_1(X2)) )
          & ! [X4] :
              ( ( r2_hidden(X4,k1_relat_1(X2))
                | ~ r2_hidden(k1_funct_1(sK0,X4),k1_relat_1(sK1))
                | ~ r2_hidden(X4,k1_relat_1(sK0)) )
              & ( ( r2_hidden(k1_funct_1(sK0,X4),k1_relat_1(sK1))
                  & r2_hidden(X4,k1_relat_1(sK0)) )
                | ~ r2_hidden(X4,k1_relat_1(X2)) ) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

% (12966)Termination reason: Time limit
% (12966)Termination phase: Saturation
fof(f16,plain,
    ( ? [X2] :
        ( k5_relat_1(sK0,sK1) != X2
        & ! [X3] :
            ( k1_funct_1(X2,X3) = k1_funct_1(sK1,k1_funct_1(sK0,X3))
            | ~ r2_hidden(X3,k1_relat_1(X2)) )
        & ! [X4] :
            ( ( r2_hidden(X4,k1_relat_1(X2))
              | ~ r2_hidden(k1_funct_1(sK0,X4),k1_relat_1(sK1))
              | ~ r2_hidden(X4,k1_relat_1(sK0)) )
            & ( ( r2_hidden(k1_funct_1(sK0,X4),k1_relat_1(sK1))
                & r2_hidden(X4,k1_relat_1(sK0)) )
              | ~ r2_hidden(X4,k1_relat_1(X2)) ) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k5_relat_1(sK0,sK1) != sK2
      & ! [X3] :
          ( k1_funct_1(sK1,k1_funct_1(sK0,X3)) = k1_funct_1(sK2,X3)
          | ~ r2_hidden(X3,k1_relat_1(sK2)) )
      & ! [X4] :
          ( ( r2_hidden(X4,k1_relat_1(sK2))
            | ~ r2_hidden(k1_funct_1(sK0,X4),k1_relat_1(sK1))
            | ~ r2_hidden(X4,k1_relat_1(sK0)) )
          & ( ( r2_hidden(k1_funct_1(sK0,X4),k1_relat_1(sK1))
              & r2_hidden(X4,k1_relat_1(sK0)) )
            | ~ r2_hidden(X4,k1_relat_1(sK2)) ) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k5_relat_1(X0,X1) != X2
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X2)) )
              & ! [X4] :
                  ( ( r2_hidden(X4,k1_relat_1(X2))
                    | ~ r2_hidden(k1_funct_1(X0,X4),k1_relat_1(X1))
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  & ( ( r2_hidden(k1_funct_1(X0,X4),k1_relat_1(X1))
                      & r2_hidden(X4,k1_relat_1(X0)) )
                    | ~ r2_hidden(X4,k1_relat_1(X2)) ) )
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k5_relat_1(X0,X1) != X2
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X2)) )
              & ! [X4] :
                  ( ( r2_hidden(X4,k1_relat_1(X2))
                    | ~ r2_hidden(k1_funct_1(X0,X4),k1_relat_1(X1))
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  & ( ( r2_hidden(k1_funct_1(X0,X4),k1_relat_1(X1))
                      & r2_hidden(X4,k1_relat_1(X0)) )
                    | ~ r2_hidden(X4,k1_relat_1(X2)) ) )
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k5_relat_1(X0,X1) != X2
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X2)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X2))
                <=> ( r2_hidden(k1_funct_1(X0,X4),k1_relat_1(X1))
                    & r2_hidden(X4,k1_relat_1(X0)) ) )
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k5_relat_1(X0,X1) != X2
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X2)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X2))
                <=> ( r2_hidden(k1_funct_1(X0,X4),k1_relat_1(X1))
                    & r2_hidden(X4,k1_relat_1(X0)) ) )
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( ! [X3] :
                        ( r2_hidden(X3,k1_relat_1(X2))
                       => k1_funct_1(X2,X3) = k1_funct_1(X1,k1_funct_1(X0,X3)) )
                    & ! [X4] :
                        ( r2_hidden(X4,k1_relat_1(X2))
                      <=> ( r2_hidden(k1_funct_1(X0,X4),k1_relat_1(X1))
                          & r2_hidden(X4,k1_relat_1(X0)) ) ) )
                 => k5_relat_1(X0,X1) = X2 ) ) ) ) ),
    inference(rectify,[],[f5])).

% (12966)Memory used [KB]: 16758
fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( ! [X3] :
                        ( r2_hidden(X3,k1_relat_1(X2))
                       => k1_funct_1(X2,X3) = k1_funct_1(X1,k1_funct_1(X0,X3)) )
                    & ! [X3] :
                        ( r2_hidden(X3,k1_relat_1(X2))
                      <=> ( r2_hidden(k1_funct_1(X0,X3),k1_relat_1(X1))
                          & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                 => k5_relat_1(X0,X1) = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

% (12966)Time elapsed: 0.600 s
fof(f4,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( ! [X3] :
                      ( r2_hidden(X3,k1_relat_1(X2))
                     => k1_funct_1(X2,X3) = k1_funct_1(X1,k1_funct_1(X0,X3)) )
                  & ! [X3] :
                      ( r2_hidden(X3,k1_relat_1(X2))
                    <=> ( r2_hidden(k1_funct_1(X0,X3),k1_relat_1(X1))
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
               => k5_relat_1(X0,X1) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_funct_1)).

fof(f3279,plain,
    ( k5_relat_1(sK0,sK1) = sK2
    | sK4(sK0,sK1,sK2) = k1_funct_1(sK1,sK5(sK0,sK1,sK2))
    | sK4(sK0,sK1,sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK2)) ),
    inference(resolution,[],[f1564,f31])).

fof(f31,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f1564,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | sK2 = k5_relat_1(X2,sK1)
      | sK4(X2,sK1,sK2) = k1_funct_1(sK1,sK5(X2,sK1,sK2))
      | k1_funct_1(sK2,sK3(X2,sK1,sK2)) = sK4(X2,sK1,sK2) ) ),
    inference(resolution,[],[f613,f95])).

fof(f95,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),sK2)
      | k1_funct_1(sK2,X1) = X2 ) ),
    inference(subsumption_resolution,[],[f94,f62])).

fof(f62,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK7(X0,X1),X3),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f26,f29,f28,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK7(X0,X1),X3),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f94,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),sK2)
      | ~ r2_hidden(X1,k1_relat_1(sK2))
      | k1_funct_1(sK2,X1) = X2 ) ),
    inference(subsumption_resolution,[],[f90,f35])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f90,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),sK2)
      | ~ r2_hidden(X1,k1_relat_1(sK2))
      | k1_funct_1(sK2,X1) = X2
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f36,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | k1_funct_1(X0,X1) = X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f613,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK3(X0,sK1,sK2),sK4(X0,sK1,sK2)),sK2)
      | sK2 = k5_relat_1(X0,sK1)
      | ~ v1_relat_1(X0)
      | sK4(X0,sK1,sK2) = k1_funct_1(sK1,sK5(X0,sK1,sK2)) ) ),
    inference(resolution,[],[f183,f84])).

fof(f84,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),sK1)
      | k1_funct_1(sK1,X1) = X2 ) ),
    inference(subsumption_resolution,[],[f83,f62])).

fof(f83,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),sK1)
      | ~ r2_hidden(X1,k1_relat_1(sK1))
      | k1_funct_1(sK1,X1) = X2 ) ),
    inference(subsumption_resolution,[],[f79,f33])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f79,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),sK1)
      | ~ r2_hidden(X1,k1_relat_1(sK1))
      | k1_funct_1(sK1,X1) = X2
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f34,f49])).

fof(f34,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f183,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(sK5(X1,sK1,sK2),sK4(X1,sK1,sK2)),sK1)
      | sK2 = k5_relat_1(X1,sK1)
      | r2_hidden(k4_tarski(sK3(X1,sK1,sK2),sK4(X1,sK1,sK2)),sK2)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f87,f33])).

fof(f87,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X3)
      | r2_hidden(k4_tarski(sK3(X2,X3,sK2),sK4(X2,X3,sK2)),sK2)
      | sK2 = k5_relat_1(X2,X3)
      | r2_hidden(k4_tarski(sK5(X2,X3,sK2),sK4(X2,X3,sK2)),X3)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f35,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | k5_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f19,f22,f21,f20])).

% (12966)------------------------------
% (12966)------------------------------
fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(f5442,plain,(
    k1_funct_1(sK2,sK3(sK0,sK1,sK2)) = k1_funct_1(sK1,sK5(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f5426,f5338])).

fof(f5338,plain,(
    sK5(sK0,sK1,sK2) = k1_funct_1(sK0,sK3(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f5336,f3235])).

fof(f3235,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(sK0,sK3(sK0,sK1,sK2)),sK4(sK0,sK1,sK2)),sK1)
    | sK5(sK0,sK1,sK2) = k1_funct_1(sK0,sK3(sK0,sK1,sK2)) ),
    inference(resolution,[],[f1032,f809])).

fof(f809,plain,(
    r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),k1_funct_1(sK0,sK3(sK0,sK1,sK2))),sK0) ),
    inference(unit_resulting_resolution,[],[f31,f32,f806,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f806,plain,(
    r2_hidden(sK3(sK0,sK1,sK2),k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f805,f37])).

fof(f37,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_relat_1(sK2))
      | r2_hidden(X4,k1_relat_1(sK0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f805,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),k1_relat_1(sK0))
    | r2_hidden(sK3(sK0,sK1,sK2),k1_relat_1(sK2)) ),
    inference(resolution,[],[f802,f62])).

fof(f802,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK2)
    | r2_hidden(sK3(sK0,sK1,sK2),k1_relat_1(sK0)) ),
    inference(resolution,[],[f569,f62])).

fof(f569,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK5(sK0,sK1,sK2)),sK0)
    | r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK2) ),
    inference(subsumption_resolution,[],[f566,f41])).

fof(f566,plain,
    ( k5_relat_1(sK0,sK1) = sK2
    | r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK5(sK0,sK1,sK2)),sK0)
    | r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK2) ),
    inference(resolution,[],[f176,f31])).

fof(f176,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | sK2 = k5_relat_1(X1,sK1)
      | r2_hidden(k4_tarski(sK3(X1,sK1,sK2),sK5(X1,sK1,sK2)),X1)
      | r2_hidden(k4_tarski(sK3(X1,sK1,sK2),sK4(X1,sK1,sK2)),sK2) ) ),
    inference(resolution,[],[f86,f33])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK3(X0,X1,sK2),sK4(X0,X1,sK2)),sK2)
      | k5_relat_1(X0,X1) = sK2
      | r2_hidden(k4_tarski(sK3(X0,X1,sK2),sK5(X0,X1,sK2)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f35,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | k5_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f32,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f1032,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),X0),sK0)
      | sK5(sK0,sK1,sK2) = k1_funct_1(sK0,sK3(sK0,sK1,sK2))
      | ~ r2_hidden(k4_tarski(X0,sK4(sK0,sK1,sK2)),sK1) ) ),
    inference(subsumption_resolution,[],[f1031,f31])).

fof(f1031,plain,(
    ! [X0] :
      ( sK5(sK0,sK1,sK2) = k1_funct_1(sK0,sK3(sK0,sK1,sK2))
      | ~ r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),X0),sK0)
      | ~ r2_hidden(k4_tarski(X0,sK4(sK0,sK1,sK2)),sK1)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f1030,f33])).

fof(f1030,plain,(
    ! [X0] :
      ( sK5(sK0,sK1,sK2) = k1_funct_1(sK0,sK3(sK0,sK1,sK2))
      | ~ r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),X0),sK0)
      | ~ r2_hidden(k4_tarski(X0,sK4(sK0,sK1,sK2)),sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f1027,f41])).

fof(f1027,plain,(
    ! [X0] :
      ( sK5(sK0,sK1,sK2) = k1_funct_1(sK0,sK3(sK0,sK1,sK2))
      | ~ r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),X0),sK0)
      | ~ r2_hidden(k4_tarski(X0,sK4(sK0,sK1,sK2)),sK1)
      | k5_relat_1(sK0,sK1) = sK2
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f801,f88])).

fof(f88,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(k4_tarski(sK3(X5,X6,sK2),sK4(X5,X6,sK2)),sK2)
      | ~ r2_hidden(k4_tarski(sK3(X5,X6,sK2),X4),X5)
      | ~ r2_hidden(k4_tarski(X4,sK4(X5,X6,sK2)),X6)
      | sK2 = k5_relat_1(X5,X6)
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(X5) ) ),
    inference(resolution,[],[f35,f47])).

fof(f47,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | k5_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f801,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK2)
    | sK5(sK0,sK1,sK2) = k1_funct_1(sK0,sK3(sK0,sK1,sK2)) ),
    inference(resolution,[],[f569,f73])).

fof(f73,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),sK0)
      | k1_funct_1(sK0,X1) = X2 ) ),
    inference(subsumption_resolution,[],[f72,f62])).

fof(f72,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),sK0)
      | ~ r2_hidden(X1,k1_relat_1(sK0))
      | k1_funct_1(sK0,X1) = X2 ) ),
    inference(subsumption_resolution,[],[f68,f31])).

fof(f68,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),sK0)
      | ~ r2_hidden(X1,k1_relat_1(sK0))
      | k1_funct_1(sK0,X1) = X2
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f32,f49])).

fof(f5336,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK0,sK3(sK0,sK1,sK2)),sK4(sK0,sK1,sK2)),sK1)
    | sK5(sK0,sK1,sK2) = k1_funct_1(sK0,sK3(sK0,sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f5335])).

fof(f5335,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK0,sK3(sK0,sK1,sK2)),sK4(sK0,sK1,sK2)),sK1)
    | sK5(sK0,sK1,sK2) = k1_funct_1(sK0,sK3(sK0,sK1,sK2))
    | sK5(sK0,sK1,sK2) = k1_funct_1(sK0,sK3(sK0,sK1,sK2)) ),
    inference(superposition,[],[f5316,f1028])).

fof(f1028,plain,
    ( sK4(sK0,sK1,sK2) = k1_funct_1(sK2,sK3(sK0,sK1,sK2))
    | sK5(sK0,sK1,sK2) = k1_funct_1(sK0,sK3(sK0,sK1,sK2)) ),
    inference(resolution,[],[f801,f95])).

fof(f5316,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK0,sK3(sK0,sK1,sK2)),k1_funct_1(sK2,sK3(sK0,sK1,sK2))),sK1)
    | sK5(sK0,sK1,sK2) = k1_funct_1(sK0,sK3(sK0,sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f5310])).

fof(f5310,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK0,sK3(sK0,sK1,sK2)),k1_funct_1(sK2,sK3(sK0,sK1,sK2))),sK1)
    | sK5(sK0,sK1,sK2) = k1_funct_1(sK0,sK3(sK0,sK1,sK2))
    | sK5(sK0,sK1,sK2) = k1_funct_1(sK0,sK3(sK0,sK1,sK2)) ),
    inference(superposition,[],[f4963,f1085])).

fof(f1085,plain,
    ( k1_funct_1(sK2,sK3(sK0,sK1,sK2)) = k1_funct_1(sK1,k1_funct_1(sK0,sK3(sK0,sK1,sK2)))
    | sK5(sK0,sK1,sK2) = k1_funct_1(sK0,sK3(sK0,sK1,sK2)) ),
    inference(resolution,[],[f1029,f40])).

fof(f40,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relat_1(sK2))
      | k1_funct_1(sK1,k1_funct_1(sK0,X3)) = k1_funct_1(sK2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1029,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),k1_relat_1(sK2))
    | sK5(sK0,sK1,sK2) = k1_funct_1(sK0,sK3(sK0,sK1,sK2)) ),
    inference(resolution,[],[f801,f62])).

fof(f4963,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK0,sK3(sK0,sK1,sK2)),k1_funct_1(sK1,k1_funct_1(sK0,sK3(sK0,sK1,sK2)))),sK1)
    | sK5(sK0,sK1,sK2) = k1_funct_1(sK0,sK3(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f4961,f1029])).

fof(f4961,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK0,sK3(sK0,sK1,sK2)),k1_funct_1(sK1,k1_funct_1(sK0,sK3(sK0,sK1,sK2)))),sK1)
    | ~ r2_hidden(sK3(sK0,sK1,sK2),k1_relat_1(sK2))
    | sK5(sK0,sK1,sK2) = k1_funct_1(sK0,sK3(sK0,sK1,sK2)) ),
    inference(superposition,[],[f104,f1084])).

fof(f1084,plain,
    ( k1_funct_1(sK1,k1_funct_1(sK0,sK3(sK0,sK1,sK2))) = sK9(sK1,k1_funct_1(sK0,sK3(sK0,sK1,sK2)))
    | sK5(sK0,sK1,sK2) = k1_funct_1(sK0,sK3(sK0,sK1,sK2)) ),
    inference(resolution,[],[f1029,f128])).

fof(f128,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | k1_funct_1(sK1,k1_funct_1(sK0,X0)) = sK9(sK1,k1_funct_1(sK0,X0)) ) ),
    inference(resolution,[],[f104,f84])).

fof(f104,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(k1_funct_1(sK0,X0),sK9(sK1,k1_funct_1(sK0,X0))),sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f38,f63])).

fof(f63,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f38,plain,(
    ! [X4] :
      ( r2_hidden(k1_funct_1(sK0,X4),k1_relat_1(sK1))
      | ~ r2_hidden(X4,k1_relat_1(sK2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5426,plain,(
    k1_funct_1(sK2,sK3(sK0,sK1,sK2)) = k1_funct_1(sK1,k1_funct_1(sK0,sK3(sK0,sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f5411,f40])).

fof(f5411,plain,(
    r2_hidden(sK3(sK0,sK1,sK2),k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f5410,f41])).

fof(f5410,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),k1_relat_1(sK2))
    | k5_relat_1(sK0,sK1) = sK2 ),
    inference(subsumption_resolution,[],[f5407,f31])).

fof(f5407,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),k1_relat_1(sK2))
    | ~ v1_relat_1(sK0)
    | k5_relat_1(sK0,sK1) = sK2 ),
    inference(duplicate_literal_removal,[],[f5405])).

fof(f5405,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),k1_relat_1(sK2))
    | ~ v1_relat_1(sK0)
    | k5_relat_1(sK0,sK1) = sK2
    | r2_hidden(sK3(sK0,sK1,sK2),k1_relat_1(sK2)) ),
    inference(resolution,[],[f5390,f945])).

fof(f945,plain,(
    ! [X3] :
      ( r2_hidden(sK5(X3,sK1,sK2),k1_relat_1(sK1))
      | ~ v1_relat_1(X3)
      | sK2 = k5_relat_1(X3,sK1)
      | r2_hidden(sK3(X3,sK1,sK2),k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f614,f62])).

fof(f614,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(sK3(X1,sK1,sK2),sK4(X1,sK1,sK2)),sK2)
      | sK2 = k5_relat_1(X1,sK1)
      | ~ v1_relat_1(X1)
      | r2_hidden(sK5(X1,sK1,sK2),k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f183,f62])).

fof(f5390,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,sK2),k1_relat_1(sK1))
    | r2_hidden(sK3(sK0,sK1,sK2),k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f5374,f806])).

fof(f5374,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,sK2),k1_relat_1(sK1))
    | r2_hidden(sK3(sK0,sK1,sK2),k1_relat_1(sK2))
    | ~ r2_hidden(sK3(sK0,sK1,sK2),k1_relat_1(sK0)) ),
    inference(superposition,[],[f39,f5338])).

fof(f39,plain,(
    ! [X4] :
      ( ~ r2_hidden(k1_funct_1(sK0,X4),k1_relat_1(sK1))
      | r2_hidden(X4,k1_relat_1(sK2))
      | ~ r2_hidden(X4,k1_relat_1(sK0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5452,plain,(
    r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),k1_funct_1(sK1,sK5(sK0,sK1,sK2))),sK2) ),
    inference(backward_demodulation,[],[f5431,f5442])).

fof(f5431,plain,(
    r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),k1_funct_1(sK2,sK3(sK0,sK1,sK2))),sK2) ),
    inference(unit_resulting_resolution,[],[f35,f36,f5411,f61])).

fof(f5524,plain,(
    ~ r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK2) ),
    inference(unit_resulting_resolution,[],[f31,f33,f35,f41,f5339,f5501,f47])).

fof(f5501,plain,(
    r2_hidden(k4_tarski(sK5(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK1) ),
    inference(backward_demodulation,[],[f5439,f5496])).

fof(f5439,plain,(
    r2_hidden(k4_tarski(sK5(sK0,sK1,sK2),k1_funct_1(sK1,sK5(sK0,sK1,sK2))),sK1) ),
    inference(subsumption_resolution,[],[f5438,f5411])).

fof(f5438,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK1,sK2),k1_funct_1(sK1,sK5(sK0,sK1,sK2))),sK1)
    | ~ r2_hidden(sK3(sK0,sK1,sK2),k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f5376,f5436])).

fof(f5436,plain,(
    k1_funct_1(sK1,sK5(sK0,sK1,sK2)) = sK9(sK1,sK5(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f5429,f5338])).

fof(f5429,plain,(
    k1_funct_1(sK1,k1_funct_1(sK0,sK3(sK0,sK1,sK2))) = sK9(sK1,k1_funct_1(sK0,sK3(sK0,sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f5411,f128])).

fof(f5376,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK1,sK2),sK9(sK1,sK5(sK0,sK1,sK2))),sK1)
    | ~ r2_hidden(sK3(sK0,sK1,sK2),k1_relat_1(sK2)) ),
    inference(superposition,[],[f104,f5338])).

fof(f5339,plain,(
    r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK5(sK0,sK1,sK2)),sK0) ),
    inference(backward_demodulation,[],[f809,f5338])).

%------------------------------------------------------------------------------
