%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t14_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:16 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 576 expanded)
%              Number of leaves         :    8 ( 152 expanded)
%              Depth                    :   21
%              Number of atoms          :  276 (3052 expanded)
%              Number of equality atoms :  117 (1464 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1764,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1760,f1729])).

fof(f1729,plain,(
    k1_funct_1(sK1,sK0) != sK6(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f1728,f997])).

fof(f997,plain,
    ( ~ r2_hidden(sK6(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1))
    | k1_funct_1(sK1,sK0) != sK6(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(equality_resolution,[],[f124])).

fof(f124,plain,(
    ! [X1] :
      ( k2_relat_1(sK1) != X1
      | k1_funct_1(sK1,sK0) != sK6(k1_funct_1(sK1,sK0),X1)
      | ~ r2_hidden(sK6(k1_funct_1(sK1,sK0),X1),X1) ) ),
    inference(superposition,[],[f44,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK6(X0,X1) != X0
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t14_funct_1.p',d1_tarski)).

fof(f44,plain,(
    k1_tarski(k1_funct_1(sK1,sK0)) != k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k1_tarski(k1_funct_1(sK1,sK0)) != k2_relat_1(sK1)
    & k1_relat_1(sK1) = k1_tarski(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
        & k1_relat_1(X1) = k1_tarski(X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k1_tarski(k1_funct_1(sK1,sK0)) != k2_relat_1(sK1)
      & k1_relat_1(sK1) = k1_tarski(sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_relat_1(X1) = k1_tarski(X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_relat_1(X1) = k1_tarski(X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_relat_1(X1) = k1_tarski(X0)
         => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_relat_1(X1) = k1_tarski(X0)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t14_funct_1.p',t14_funct_1)).

fof(f1728,plain,
    ( k1_funct_1(sK1,sK0) != sK6(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | r2_hidden(sK6(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f1727,f44])).

fof(f1727,plain,
    ( k1_funct_1(sK1,sK0) != sK6(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | k1_tarski(k1_funct_1(sK1,sK0)) = k2_relat_1(sK1)
    | r2_hidden(sK6(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f1723,f94])).

fof(f94,plain,(
    r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f93,f41])).

fof(f41,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f93,plain,
    ( r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f89,f42])).

fof(f42,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f89,plain,
    ( r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f86,f59])).

fof(f59,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK2(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1)
                  & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X5)) = X5
                    & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f32,f31,f30])).

fof(f30,plain,(
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
              ( k1_funct_1(X0,X3) != sK2(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK2(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) = X2
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t14_funct_1.p',d5_funct_1)).

fof(f86,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(superposition,[],[f63,f43])).

fof(f43,plain,(
    k1_relat_1(sK1) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1723,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | k1_funct_1(sK1,sK0) != sK6(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | k1_tarski(k1_funct_1(sK1,sK0)) = k2_relat_1(sK1)
    | r2_hidden(sK6(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    inference(superposition,[],[f997,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK6(X0,X1) = X0
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1760,plain,(
    k1_funct_1(sK1,sK0) = sK6(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f1758,f1746])).

fof(f1746,plain,(
    k1_funct_1(sK1,sK4(sK1,sK6(k1_funct_1(sK1,sK0),k2_relat_1(sK1)))) = sK6(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(resolution,[],[f1741,f72])).

fof(f72,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK1))
      | k1_funct_1(sK1,sK4(sK1,X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f66,f42])).

fof(f66,plain,(
    ! [X1] :
      ( k1_funct_1(sK1,sK4(sK1,X1)) = X1
      | ~ r2_hidden(X1,k2_relat_1(sK1))
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f41,f60])).

fof(f60,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1741,plain,(
    r2_hidden(sK6(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f1734,f44])).

fof(f1734,plain,
    ( k1_tarski(k1_funct_1(sK1,sK0)) = k2_relat_1(sK1)
    | r2_hidden(sK6(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f1733])).

fof(f1733,plain,
    ( k1_funct_1(sK1,sK0) != k1_funct_1(sK1,sK0)
    | k1_tarski(k1_funct_1(sK1,sK0)) = k2_relat_1(sK1)
    | r2_hidden(sK6(k1_funct_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    inference(superposition,[],[f1729,f55])).

fof(f1758,plain,(
    sK0 = sK4(sK1,sK6(k1_funct_1(sK1,sK0),k2_relat_1(sK1))) ),
    inference(backward_demodulation,[],[f1746,f1745])).

fof(f1745,plain,(
    sK0 = sK4(sK1,k1_funct_1(sK1,sK4(sK1,sK6(k1_funct_1(sK1,sK0),k2_relat_1(sK1))))) ),
    inference(resolution,[],[f1741,f247])).

fof(f247,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relat_1(sK1))
      | sK0 = sK4(sK1,k1_funct_1(sK1,sK4(sK1,X3))) ) ),
    inference(subsumption_resolution,[],[f246,f41])).

fof(f246,plain,(
    ! [X3] :
      ( sK0 = sK4(sK1,k1_funct_1(sK1,sK4(sK1,X3)))
      | ~ r2_hidden(X3,k2_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f239,f42])).

fof(f239,plain,(
    ! [X3] :
      ( sK0 = sK4(sK1,k1_funct_1(sK1,sK4(sK1,X3)))
      | ~ r2_hidden(X3,k2_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f163,f61])).

fof(f61,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f163,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | sK0 = sK4(sK1,k1_funct_1(sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f162,f41])).

fof(f162,plain,(
    ! [X0] :
      ( sK0 = sK4(sK1,k1_funct_1(sK1,X0))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f152,f42])).

fof(f152,plain,(
    ! [X0] :
      ( sK0 = sK4(sK1,k1_funct_1(sK1,X0))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f136,f59])).

fof(f136,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relat_1(sK1))
      | sK0 = sK4(sK1,X3) ) ),
    inference(subsumption_resolution,[],[f135,f41])).

fof(f135,plain,(
    ! [X3] :
      ( sK0 = sK4(sK1,X3)
      | ~ r2_hidden(X3,k2_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f129,f42])).

fof(f129,plain,(
    ! [X3] :
      ( sK0 = sK4(sK1,X3)
      | ~ r2_hidden(X3,k2_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f85,f61])).

fof(f85,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | sK0 = X0 ) ),
    inference(superposition,[],[f64,f43])).

fof(f64,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
