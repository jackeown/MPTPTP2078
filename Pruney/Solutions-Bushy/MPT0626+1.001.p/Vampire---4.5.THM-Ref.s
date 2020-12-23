%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0626+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:20 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :   92 (1303 expanded)
%              Number of leaves         :   13 ( 406 expanded)
%              Depth                    :   33
%              Number of atoms          :  497 (9786 expanded)
%              Number of equality atoms :   41 ( 562 expanded)
%              Maximal formula depth    :   16 (   8 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f357,plain,(
    $false ),
    inference(subsumption_resolution,[],[f354,f335])).

fof(f335,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f334,f34])).

fof(f34,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
      | ~ r2_hidden(sK0,k1_relat_1(sK2))
      | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) )
    & ( ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
        & r2_hidden(sK0,k1_relat_1(sK2)) )
      | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) )
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2))
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ( ~ r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1))
            | ~ r2_hidden(sK0,k1_relat_1(X2))
            | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1))) )
          & ( ( r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1))
              & r2_hidden(sK0,k1_relat_1(X2)) )
            | r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1))) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ( ~ r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1))
          | ~ r2_hidden(sK0,k1_relat_1(X2))
          | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1))) )
        & ( ( r2_hidden(k1_funct_1(X2,sK0),k1_relat_1(sK1))
            & r2_hidden(sK0,k1_relat_1(X2)) )
          | r2_hidden(sK0,k1_relat_1(k5_relat_1(X2,sK1))) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
        | ~ r2_hidden(sK0,k1_relat_1(sK2))
        | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) )
      & ( ( r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
          & r2_hidden(sK0,k1_relat_1(sK2)) )
        | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
            | ~ r2_hidden(X0,k1_relat_1(X2))
            | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) )
            | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
            | ~ r2_hidden(X0,k1_relat_1(X2))
            | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) )
            | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <~> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <~> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
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
           => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
            <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

fof(f334,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f333,f35])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f333,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f332,f133])).

fof(f133,plain,(
    r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f132,f32])).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f132,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f127,f34])).

fof(f127,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK1) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK1)
    | r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f107,f36])).

fof(f36,plain,
    ( r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
    | r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X1,X0)))
      | ~ v1_relat_1(X1)
      | r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f105,f61])).

fof(f61,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f27,f30,f29,f28])).

fof(f28,plain,(
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

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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

fof(f105,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k5_relat_1(X6,X7))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X6)
      | r2_hidden(X4,k1_relat_1(X6)) ) ),
    inference(subsumption_resolution,[],[f101,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f101,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k5_relat_1(X6,X7))
      | ~ v1_relat_1(k5_relat_1(X6,X7))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X6)
      | r2_hidden(X4,k1_relat_1(X6)) ) ),
    inference(resolution,[],[f56,f60])).

fof(f60,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f20,f23,f22,f21])).

fof(f21,plain,(
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

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

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

fof(f332,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f327,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,X1) = sK9(X0,X1)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,X1) = sK9(X0,X1)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0)) ) ),
    inference(resolution,[],[f46,f61])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) = X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f327,plain,(
    ~ r2_hidden(sK9(sK2,sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f322,f61])).

fof(f322,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(sK9(sK2,sK0),X0),sK1) ),
    inference(subsumption_resolution,[],[f319,f133])).

fof(f319,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK9(sK2,sK0),X0),sK1)
      | ~ r2_hidden(sK0,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f318,f61])).

fof(f318,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK0,X0),sK2)
      | ~ r2_hidden(k4_tarski(X0,X1),sK1) ) ),
    inference(subsumption_resolution,[],[f313,f203])).

fof(f203,plain,(
    ! [X30,X29] :
      ( ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1))
      | ~ r2_hidden(k4_tarski(X29,X30),sK1)
      | ~ r2_hidden(k4_tarski(sK0,X29),sK2) ) ),
    inference(subsumption_resolution,[],[f202,f133])).

fof(f202,plain,(
    ! [X30,X29] :
      ( ~ r2_hidden(k4_tarski(sK0,X29),sK2)
      | ~ r2_hidden(k4_tarski(X29,X30),sK1)
      | ~ r2_hidden(sK0,k1_relat_1(sK2))
      | ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f201,f34])).

fof(f201,plain,(
    ! [X30,X29] :
      ( ~ r2_hidden(k4_tarski(sK0,X29),sK2)
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(k4_tarski(X29,X30),sK1)
      | ~ r2_hidden(sK0,k1_relat_1(sK2))
      | ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f195,f32])).

fof(f195,plain,(
    ! [X30,X29] :
      ( ~ r2_hidden(k4_tarski(sK0,X29),sK2)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(k4_tarski(X29,X30),sK1)
      | ~ r2_hidden(sK0,k1_relat_1(sK2))
      | ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f188,f38])).

fof(f38,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f188,plain,(
    ! [X24,X23,X21,X25,X22] :
      ( r2_hidden(X24,k1_relat_1(k5_relat_1(X25,X23)))
      | ~ r2_hidden(k4_tarski(X24,X21),X25)
      | ~ v1_relat_1(X23)
      | ~ v1_relat_1(X25)
      | ~ r2_hidden(k4_tarski(X21,X22),X23) ) ),
    inference(subsumption_resolution,[],[f181,f49])).

fof(f181,plain,(
    ! [X24,X23,X21,X25,X22] :
      ( ~ r2_hidden(k4_tarski(X21,X22),X23)
      | ~ r2_hidden(k4_tarski(X24,X21),X25)
      | ~ v1_relat_1(k5_relat_1(X25,X23))
      | ~ v1_relat_1(X23)
      | ~ v1_relat_1(X25)
      | r2_hidden(X24,k1_relat_1(k5_relat_1(X25,X23))) ) ),
    inference(resolution,[],[f54,f60])).

fof(f54,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f313,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | ~ r2_hidden(k4_tarski(sK0,X0),sK2)
      | r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f310,f37])).

fof(f37,plain,
    ( r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
    | r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f310,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
      | ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | ~ r2_hidden(k4_tarski(sK0,X0),sK2) ) ),
    inference(subsumption_resolution,[],[f309,f35])).

fof(f309,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK2)
      | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
      | ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | ~ r2_hidden(k4_tarski(sK0,X0),sK2) ) ),
    inference(subsumption_resolution,[],[f308,f32])).

fof(f308,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | ~ v1_funct_1(sK2)
      | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
      | ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | ~ r2_hidden(k4_tarski(sK0,X0),sK2) ) ),
    inference(subsumption_resolution,[],[f299,f34])).

fof(f299,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK2)
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(sK2)
      | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1)))
      | ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | ~ r2_hidden(k4_tarski(sK0,X0),sK2) ) ),
    inference(resolution,[],[f287,f203])).

fof(f287,plain,(
    ! [X17,X15,X16] :
      ( r2_hidden(k1_funct_1(X16,X17),k1_relat_1(X15))
      | ~ v1_relat_1(X16)
      | ~ v1_relat_1(X15)
      | ~ v1_funct_1(X16)
      | ~ r2_hidden(X17,k1_relat_1(k5_relat_1(X16,X15))) ) ),
    inference(resolution,[],[f278,f61])).

fof(f278,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X7),k5_relat_1(X4,X5))
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(X4)
      | r2_hidden(k1_funct_1(X4,X6),k1_relat_1(X5))
      | ~ v1_funct_1(X4) ) ),
    inference(subsumption_resolution,[],[f276,f105])).

fof(f276,plain,(
    ! [X6,X4,X7,X5] :
      ( r2_hidden(k1_funct_1(X4,X6),k1_relat_1(X5))
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(k4_tarski(X6,X7),k5_relat_1(X4,X5))
      | ~ r2_hidden(X6,k1_relat_1(X4))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f271])).

fof(f271,plain,(
    ! [X6,X4,X7,X5] :
      ( r2_hidden(k1_funct_1(X4,X6),k1_relat_1(X5))
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(k4_tarski(X6,X7),k5_relat_1(X4,X5))
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(k4_tarski(X6,X7),k5_relat_1(X4,X5))
      | ~ r2_hidden(X6,k1_relat_1(X4))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f88,f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X0) = sK6(X2,X3,X0,X1)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f103,f49])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
      | ~ v1_relat_1(k5_relat_1(X2,X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,X0) = sK6(X2,X3,X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X2,X3))
      | ~ v1_relat_1(k5_relat_1(X2,X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,X0) = sK6(X2,X3,X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f56,f46])).

fof(f88,plain,(
    ! [X6,X4,X7,X5] :
      ( r2_hidden(sK6(X6,X7,X4,X5),k1_relat_1(X7))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X6)
      | ~ r2_hidden(k4_tarski(X4,X5),k5_relat_1(X6,X7)) ) ),
    inference(subsumption_resolution,[],[f85,f49])).

fof(f85,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k5_relat_1(X6,X7))
      | ~ v1_relat_1(k5_relat_1(X6,X7))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X6)
      | r2_hidden(sK6(X6,X7,X4,X5),k1_relat_1(X7)) ) ),
    inference(resolution,[],[f55,f60])).

fof(f55,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f354,plain,(
    r2_hidden(k1_funct_1(sK2,sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f353,f37])).

fof(f353,plain,(
    ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(subsumption_resolution,[],[f352,f35])).

fof(f352,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(subsumption_resolution,[],[f351,f32])).

fof(f351,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(subsumption_resolution,[],[f349,f34])).

fof(f349,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK2,sK1))) ),
    inference(resolution,[],[f335,f287])).

%------------------------------------------------------------------------------
