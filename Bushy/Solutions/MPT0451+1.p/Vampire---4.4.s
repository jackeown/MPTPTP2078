%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t37_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:01 EDT 2019

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   85 (1133 expanded)
%              Number of leaves         :   13 ( 351 expanded)
%              Depth                    :   22
%              Number of atoms          :  305 (5196 expanded)
%              Number of equality atoms :   61 (1281 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8064,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8063,f8047])).

fof(f8047,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(X0,sK4(k4_relat_1(sK0),k1_relat_1(sK0))),k4_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f8038,f6792])).

fof(f6792,plain,(
    k2_relat_1(k4_relat_1(sK0)) != k1_relat_1(sK0) ),
    inference(trivial_inequality_removal,[],[f6783])).

fof(f6783,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | k2_relat_1(k4_relat_1(sK0)) != k1_relat_1(sK0) ),
    inference(superposition,[],[f51,f4928])).

fof(f4928,plain,(
    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f4920,f315])).

fof(f315,plain,(
    ! [X4] :
      ( r2_hidden(sK1(k4_relat_1(sK0),X4),k2_relat_1(sK0))
      | k1_relat_1(k4_relat_1(sK0)) = X4
      | r2_hidden(sK1(k4_relat_1(sK0),X4),X4) ) ),
    inference(resolution,[],[f258,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f38,f37,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/relat_1__t37_relat_1.p',d4_relat_1)).

fof(f258,plain,(
    ! [X14,X13] :
      ( ~ r2_hidden(k4_tarski(X13,X14),k4_relat_1(sK0))
      | r2_hidden(X13,k2_relat_1(sK0)) ) ),
    inference(resolution,[],[f82,f69])).

fof(f69,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f41,f44,f43,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox2/benchmark/relat_1__t37_relat_1.p',d5_relat_1)).

fof(f82,plain,(
    ! [X6,X7] :
      ( r2_hidden(k4_tarski(X6,X7),sK0)
      | ~ r2_hidden(k4_tarski(X7,X6),k4_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f80,f74])).

fof(f74,plain,(
    v1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f50,f57])).

fof(f57,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t37_relat_1.p',dt_k4_relat_1)).

fof(f50,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( k2_relat_1(k4_relat_1(sK0)) != k1_relat_1(sK0)
      | k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0)) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ( k2_relat_1(k4_relat_1(X0)) != k1_relat_1(X0)
          | k2_relat_1(X0) != k1_relat_1(k4_relat_1(X0)) )
        & v1_relat_1(X0) )
   => ( ( k2_relat_1(k4_relat_1(sK0)) != k1_relat_1(sK0)
        | k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0)) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) != k1_relat_1(X0)
        | k2_relat_1(X0) != k1_relat_1(k4_relat_1(X0)) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t37_relat_1.p',t37_relat_1)).

fof(f80,plain,(
    ! [X6,X7] :
      ( r2_hidden(k4_tarski(X6,X7),sK0)
      | ~ r2_hidden(k4_tarski(X7,X6),k4_relat_1(sK0))
      | ~ v1_relat_1(k4_relat_1(sK0)) ) ),
    inference(resolution,[],[f50,f72])).

fof(f72,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f47,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t37_relat_1.p',d7_relat_1)).

fof(f4920,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
    | ~ r2_hidden(sK1(k4_relat_1(sK0),k2_relat_1(sK0)),k2_relat_1(sK0)) ),
    inference(resolution,[],[f2362,f1628])).

fof(f1628,plain,(
    ! [X5] :
      ( r2_hidden(k4_tarski(sK3(k4_relat_1(sK0),X5),X5),sK0)
      | ~ r2_hidden(X5,k2_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f1627,f50])).

fof(f1627,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k2_relat_1(sK0))
      | r2_hidden(k4_tarski(sK3(k4_relat_1(sK0),X5),X5),sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f1612,f74])).

fof(f1612,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k2_relat_1(sK0))
      | r2_hidden(k4_tarski(sK3(k4_relat_1(sK0),X5),X5),sK0)
      | ~ v1_relat_1(k4_relat_1(sK0))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f230,f72])).

fof(f230,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,sK3(k4_relat_1(sK0),X0)),k4_relat_1(sK0))
      | ~ r2_hidden(X0,k2_relat_1(sK0)) ) ),
    inference(resolution,[],[f223,f68])).

fof(f68,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f223,plain,(
    ! [X2] :
      ( r2_hidden(X2,k1_relat_1(k4_relat_1(sK0)))
      | ~ r2_hidden(X2,k2_relat_1(sK0)) ) ),
    inference(resolution,[],[f132,f70])).

fof(f70,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f132,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(k4_tarski(X12,X13),sK0)
      | r2_hidden(X13,k1_relat_1(k4_relat_1(sK0))) ) ),
    inference(resolution,[],[f81,f67])).

fof(f67,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f81,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(sK0))
      | ~ r2_hidden(k4_tarski(X5,X4),sK0) ) ),
    inference(subsumption_resolution,[],[f79,f74])).

fof(f79,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(sK0))
      | ~ r2_hidden(k4_tarski(X5,X4),sK0)
      | ~ v1_relat_1(k4_relat_1(sK0)) ) ),
    inference(resolution,[],[f50,f71])).

fof(f71,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f2362,plain,(
    ! [X17] :
      ( ~ r2_hidden(k4_tarski(X17,sK1(k4_relat_1(sK0),k2_relat_1(sK0))),sK0)
      | k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f2355,f132])).

fof(f2355,plain,(
    ! [X17] :
      ( ~ r2_hidden(k4_tarski(X17,sK1(k4_relat_1(sK0),k2_relat_1(sK0))),sK0)
      | k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))
      | ~ r2_hidden(sK1(k4_relat_1(sK0),k2_relat_1(sK0)),k1_relat_1(k4_relat_1(sK0))) ) ),
    inference(resolution,[],[f126,f319])).

fof(f319,plain,(
    ! [X8] :
      ( r2_hidden(X8,k2_relat_1(sK0))
      | ~ r2_hidden(X8,k1_relat_1(k4_relat_1(sK0))) ) ),
    inference(resolution,[],[f258,f68])).

fof(f126,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,sK1(k4_relat_1(sK0),X3)),sK0)
      | ~ r2_hidden(sK1(k4_relat_1(sK0),X3),X3)
      | k1_relat_1(k4_relat_1(sK0)) = X3 ) ),
    inference(resolution,[],[f81,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( k1_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f51,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0))
    | k2_relat_1(k4_relat_1(sK0)) != k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f8038,plain,(
    ! [X0] :
      ( k2_relat_1(k4_relat_1(sK0)) = k1_relat_1(sK0)
      | ~ r2_hidden(k4_tarski(X0,sK4(k4_relat_1(sK0),k1_relat_1(sK0))),k4_relat_1(sK0)) ) ),
    inference(resolution,[],[f2606,f82])).

fof(f2606,plain,(
    ! [X9] :
      ( ~ r2_hidden(k4_tarski(sK4(k4_relat_1(sK0),k1_relat_1(sK0)),X9),sK0)
      | k2_relat_1(k4_relat_1(sK0)) = k1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f2594,f131])).

fof(f131,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(k4_tarski(X10,X11),sK0)
      | r2_hidden(X10,k2_relat_1(k4_relat_1(sK0))) ) ),
    inference(resolution,[],[f81,f69])).

fof(f2594,plain,(
    ! [X9] :
      ( ~ r2_hidden(k4_tarski(sK4(k4_relat_1(sK0),k1_relat_1(sK0)),X9),sK0)
      | k2_relat_1(k4_relat_1(sK0)) = k1_relat_1(sK0)
      | ~ r2_hidden(sK4(k4_relat_1(sK0),k1_relat_1(sK0)),k2_relat_1(k4_relat_1(sK0))) ) ),
    inference(resolution,[],[f128,f371])).

fof(f371,plain,(
    ! [X6] :
      ( r2_hidden(X6,k1_relat_1(sK0))
      | ~ r2_hidden(X6,k2_relat_1(k4_relat_1(sK0))) ) ),
    inference(resolution,[],[f259,f70])).

fof(f259,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(k4_tarski(X15,X16),k4_relat_1(sK0))
      | r2_hidden(X16,k1_relat_1(sK0)) ) ),
    inference(resolution,[],[f82,f67])).

fof(f128,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(k4_tarski(sK4(k4_relat_1(sK0),X5),X6),sK0)
      | ~ r2_hidden(sK4(k4_relat_1(sK0),X5),X5)
      | k2_relat_1(k4_relat_1(sK0)) = X5 ) ),
    inference(resolution,[],[f81,f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f8063,plain,(
    r2_hidden(k4_tarski(sK5(k4_relat_1(sK0),k1_relat_1(sK0)),sK4(k4_relat_1(sK0),k1_relat_1(sK0))),k4_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f8056,f6792])).

fof(f8056,plain,
    ( k2_relat_1(k4_relat_1(sK0)) = k1_relat_1(sK0)
    | r2_hidden(k4_tarski(sK5(k4_relat_1(sK0),k1_relat_1(sK0)),sK4(k4_relat_1(sK0),k1_relat_1(sK0))),k4_relat_1(sK0)) ),
    inference(resolution,[],[f8049,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f8049,plain,(
    ~ r2_hidden(sK4(k4_relat_1(sK0),k1_relat_1(sK0)),k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f8040,f6792])).

fof(f8040,plain,
    ( k2_relat_1(k4_relat_1(sK0)) = k1_relat_1(sK0)
    | ~ r2_hidden(sK4(k4_relat_1(sK0),k1_relat_1(sK0)),k1_relat_1(sK0)) ),
    inference(resolution,[],[f2606,f1546])).

fof(f1546,plain,(
    ! [X5] :
      ( r2_hidden(k4_tarski(X5,sK6(k4_relat_1(sK0),X5)),sK0)
      | ~ r2_hidden(X5,k1_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f1545,f50])).

fof(f1545,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k1_relat_1(sK0))
      | r2_hidden(k4_tarski(X5,sK6(k4_relat_1(sK0),X5)),sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f1530,f74])).

fof(f1530,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k1_relat_1(sK0))
      | r2_hidden(k4_tarski(X5,sK6(k4_relat_1(sK0),X5)),sK0)
      | ~ v1_relat_1(k4_relat_1(sK0))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f153,f72])).

fof(f153,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK6(k4_relat_1(sK0),X0),X0),k4_relat_1(sK0))
      | ~ r2_hidden(X0,k1_relat_1(sK0)) ) ),
    inference(resolution,[],[f148,f70])).

fof(f148,plain,(
    ! [X4] :
      ( r2_hidden(X4,k2_relat_1(k4_relat_1(sK0)))
      | ~ r2_hidden(X4,k1_relat_1(sK0)) ) ),
    inference(resolution,[],[f131,f68])).
%------------------------------------------------------------------------------
