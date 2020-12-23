%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t99_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:28 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 577 expanded)
%              Number of leaves         :   11 ( 156 expanded)
%              Depth                    :   12
%              Number of atoms          :  320 (2777 expanded)
%              Number of equality atoms :   57 ( 267 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f190,plain,(
    $false ),
    inference(subsumption_resolution,[],[f189,f134])).

fof(f134,plain,(
    k1_funct_1(sK3,sK4(k8_relat_1(sK2,sK3))) != k1_funct_1(sK3,sK5(k8_relat_1(sK2,sK3))) ),
    inference(unit_resulting_resolution,[],[f48,f49,f50,f107,f125,f84,f55])).

fof(f55,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK4(X0) != sK5(X0)
            & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
            & r2_hidden(sK5(X0),k1_relat_1(X0))
            & r2_hidden(sK4(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f38,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK4(X0) != sK5(X0)
        & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
        & r2_hidden(sK5(X0),k1_relat_1(X0))
        & r2_hidden(sK4(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t99_funct_1.p',d8_funct_1)).

fof(f84,plain,(
    sK4(k8_relat_1(sK2,sK3)) != sK5(k8_relat_1(sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f75,f78,f51,f59])).

fof(f59,plain,(
    ! [X0] :
      ( sK4(X0) != sK5(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f51,plain,(
    ~ v2_funct_1(k8_relat_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ v2_funct_1(k8_relat_1(sK2,sK3))
    & v2_funct_1(sK3)
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f23,f35])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( ~ v2_funct_1(k8_relat_1(X0,X1))
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v2_funct_1(k8_relat_1(sK2,sK3))
      & v2_funct_1(sK3)
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ~ v2_funct_1(k8_relat_1(X0,X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ~ v2_funct_1(k8_relat_1(X0,X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => v2_funct_1(k8_relat_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => v2_funct_1(k8_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t99_funct_1.p',t99_funct_1)).

fof(f78,plain,(
    ! [X0] : v1_funct_1(k8_relat_1(X0,sK3)) ),
    inference(unit_resulting_resolution,[],[f48,f49,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k8_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t99_funct_1.p',fc9_funct_1)).

fof(f75,plain,(
    ! [X0] : v1_relat_1(k8_relat_1(X0,sK3)) ),
    inference(unit_resulting_resolution,[],[f48,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t99_funct_1.p',dt_k8_relat_1)).

fof(f125,plain,(
    r2_hidden(sK5(k8_relat_1(sK2,sK3)),k1_relat_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f104,f82,f62])).

fof(f62,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X6,k1_relat_1(X1))
      | r2_hidden(X6,k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( k1_funct_1(X0,sK6(X0,X1)) != k1_funct_1(X1,sK6(X0,X1))
          & r2_hidden(sK6(X0,X1),k1_relat_1(X1)) )
        | ( ( ~ r2_hidden(k1_funct_1(X0,sK7(X0,X1,X2)),X2)
            | ~ r2_hidden(sK7(X0,X1,X2),k1_relat_1(X0))
            | ~ r2_hidden(sK7(X0,X1,X2),k1_relat_1(X1)) )
          & ( ( r2_hidden(k1_funct_1(X0,sK7(X0,X1,X2)),X2)
              & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X0)) )
            | r2_hidden(sK7(X0,X1,X2),k1_relat_1(X1)) ) ) )
      & ( ( ! [X5] :
              ( k1_funct_1(X0,X5) = k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,k1_relat_1(X1)) )
          & ! [X6] :
              ( ( r2_hidden(X6,k1_relat_1(X1))
                | ~ r2_hidden(k1_funct_1(X0,X6),X2)
                | ~ r2_hidden(X6,k1_relat_1(X0)) )
              & ( ( r2_hidden(k1_funct_1(X0,X6),X2)
                  & r2_hidden(X6,k1_relat_1(X0)) )
                | ~ r2_hidden(X6,k1_relat_1(X1)) ) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f44,f46,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X0,sK6(X0,X1)) != k1_funct_1(X1,sK6(X0,X1))
        & r2_hidden(sK6(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X4),X2)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X4,k1_relat_1(X1)) )
          & ( ( r2_hidden(k1_funct_1(X0,X4),X2)
              & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X4,k1_relat_1(X1)) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK7(X0,X1,X2)),X2)
          | ~ r2_hidden(sK7(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK7(X0,X1,X2),k1_relat_1(X1)) )
        & ( ( r2_hidden(k1_funct_1(X0,sK7(X0,X1,X2)),X2)
            & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK7(X0,X1,X2),k1_relat_1(X1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ? [X4] :
            ( ( ~ r2_hidden(k1_funct_1(X0,X4),X2)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X4,k1_relat_1(X1)) )
            & ( ( r2_hidden(k1_funct_1(X0,X4),X2)
                & r2_hidden(X4,k1_relat_1(X0)) )
              | r2_hidden(X4,k1_relat_1(X1)) ) ) )
      & ( ( ! [X5] :
              ( k1_funct_1(X0,X5) = k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,k1_relat_1(X1)) )
          & ! [X6] :
              ( ( r2_hidden(X6,k1_relat_1(X1))
                | ~ r2_hidden(k1_funct_1(X0,X6),X2)
                | ~ r2_hidden(X6,k1_relat_1(X0)) )
              & ( ( r2_hidden(k1_funct_1(X0,X6),X2)
                  & r2_hidden(X6,k1_relat_1(X0)) )
                | ~ r2_hidden(X6,k1_relat_1(X1)) ) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | ? [X3] :
            ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ? [X4] :
            ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
              | ~ r2_hidden(X4,k1_relat_1(X2))
              | ~ r2_hidden(X4,k1_relat_1(X1)) )
            & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                & r2_hidden(X4,k1_relat_1(X2)) )
              | r2_hidden(X4,k1_relat_1(X1)) ) ) )
      & ( ( ! [X3] :
              ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & ! [X4] :
              ( ( r2_hidden(X4,k1_relat_1(X1))
                | ~ r2_hidden(k1_funct_1(X2,X4),X0)
                | ~ r2_hidden(X4,k1_relat_1(X2)) )
              & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                  & r2_hidden(X4,k1_relat_1(X2)) )
                | ~ r2_hidden(X4,k1_relat_1(X1)) ) ) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | ? [X3] :
            ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ? [X4] :
            ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
              | ~ r2_hidden(X4,k1_relat_1(X2))
              | ~ r2_hidden(X4,k1_relat_1(X1)) )
            & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                & r2_hidden(X4,k1_relat_1(X2)) )
              | r2_hidden(X4,k1_relat_1(X1)) ) ) )
      & ( ( ! [X3] :
              ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & ! [X4] :
              ( ( r2_hidden(X4,k1_relat_1(X1))
                | ~ r2_hidden(k1_funct_1(X2,X4),X0)
                | ~ r2_hidden(X4,k1_relat_1(X2)) )
              & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                  & r2_hidden(X4,k1_relat_1(X2)) )
                | ~ r2_hidden(X4,k1_relat_1(X1)) ) ) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ( ! [X3] :
            ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
            | ~ r2_hidden(X3,k1_relat_1(X1)) )
        & ! [X4] :
            ( r2_hidden(X4,k1_relat_1(X1))
          <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
              & r2_hidden(X4,k1_relat_1(X2)) ) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f82,plain,(
    r2_hidden(sK5(k8_relat_1(sK2,sK3)),k1_relat_1(k8_relat_1(sK2,sK3))) ),
    inference(unit_resulting_resolution,[],[f75,f78,f51,f57])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f104,plain,(
    ! [X0] : sP0(sK3,k8_relat_1(X0,sK3),X0) ),
    inference(unit_resulting_resolution,[],[f89,f74])).

fof(f74,plain,(
    ! [X2,X0] :
      ( ~ sP1(X0,k8_relat_1(X0,X2),X2)
      | sP0(X2,k8_relat_1(X0,X2),X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k8_relat_1(X0,X2) != X1
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( k8_relat_1(X0,X2) = X1
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k8_relat_1(X0,X2) != X1 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relat_1(X0,X2) = X1
      <=> sP0(X2,X1,X0) )
      | ~ sP1(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f89,plain,(
    ! [X0,X1] : sP1(X0,k8_relat_1(X1,sK3),sK3) ),
    inference(unit_resulting_resolution,[],[f75,f78,f48,f49,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP1(X0,X1,X2)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f30,f33,f32])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) ) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X3),X0)
                    & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t99_funct_1.p',t85_funct_1)).

fof(f107,plain,(
    r2_hidden(sK4(k8_relat_1(sK2,sK3)),k1_relat_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f80,f104,f62])).

fof(f80,plain,(
    r2_hidden(sK4(k8_relat_1(sK2,sK3)),k1_relat_1(k8_relat_1(sK2,sK3))) ),
    inference(unit_resulting_resolution,[],[f75,f78,f51,f56])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f50,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f189,plain,(
    k1_funct_1(sK3,sK4(k8_relat_1(sK2,sK3))) = k1_funct_1(sK3,sK5(k8_relat_1(sK2,sK3))) ),
    inference(forward_demodulation,[],[f123,f172])).

fof(f172,plain,(
    k1_funct_1(sK3,sK4(k8_relat_1(sK2,sK3))) = k1_funct_1(k8_relat_1(sK2,sK3),sK5(k8_relat_1(sK2,sK3))) ),
    inference(backward_demodulation,[],[f111,f108])).

fof(f108,plain,(
    k1_funct_1(k8_relat_1(sK2,sK3),sK4(k8_relat_1(sK2,sK3))) = k1_funct_1(k8_relat_1(sK2,sK3),sK5(k8_relat_1(sK2,sK3))) ),
    inference(unit_resulting_resolution,[],[f75,f51,f78,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f111,plain,(
    k1_funct_1(sK3,sK4(k8_relat_1(sK2,sK3))) = k1_funct_1(k8_relat_1(sK2,sK3),sK4(k8_relat_1(sK2,sK3))) ),
    inference(unit_resulting_resolution,[],[f104,f80,f65])).

fof(f65,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X5,k1_relat_1(X1))
      | k1_funct_1(X0,X5) = k1_funct_1(X1,X5) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f123,plain,(
    k1_funct_1(sK3,sK5(k8_relat_1(sK2,sK3))) = k1_funct_1(k8_relat_1(sK2,sK3),sK5(k8_relat_1(sK2,sK3))) ),
    inference(unit_resulting_resolution,[],[f104,f82,f65])).
%------------------------------------------------------------------------------
