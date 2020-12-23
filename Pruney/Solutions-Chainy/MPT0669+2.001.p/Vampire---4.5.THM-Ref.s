%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 188 expanded)
%              Number of leaves         :    9 (  47 expanded)
%              Depth                    :   18
%              Number of atoms          :  383 (1251 expanded)
%              Number of equality atoms :   29 (  81 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f80,f82,f116,f122,f128])).

fof(f128,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f73,f124])).

fof(f124,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f123,f34])).

fof(f34,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
      | ~ r2_hidden(sK0,k1_relat_1(sK2))
      | ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) )
    & ( ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
        & r2_hidden(sK0,k1_relat_1(sK2)) )
      | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) )
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
        | ~ r2_hidden(sK0,k1_relat_1(sK2))
        | ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) )
      & ( ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
          & r2_hidden(sK0,k1_relat_1(sK2)) )
        | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
        <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_funct_1)).

fof(f123,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f118,f35])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f118,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(resolution,[],[f78,f90])).

fof(f90,plain,(
    ! [X6,X2,X0] :
      ( ~ r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2)))
      | r2_hidden(X6,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f89,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_funct_1)).

fof(f89,plain,(
    ! [X6,X2,X0] :
      ( r2_hidden(X6,k1_relat_1(X2))
      | ~ r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k8_relat_1(X0,X2)) ) ),
    inference(subsumption_resolution,[],[f66,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k8_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f66,plain,(
    ! [X6,X2,X0] :
      ( r2_hidden(X6,k1_relat_1(X2))
      | ~ r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(k8_relat_1(X0,X2)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,k1_relat_1(X2))
      | ~ r2_hidden(X6,k1_relat_1(X1))
      | k8_relat_1(X0,X2) != X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X2) = X1
              | ( k1_funct_1(X2,sK5(X1,X2)) != k1_funct_1(X1,sK5(X1,X2))
                & r2_hidden(sK5(X1,X2),k1_relat_1(X1)) )
              | ( ( ~ r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))
                  | ~ r2_hidden(sK6(X0,X1,X2),k1_relat_1(X1)) )
                & ( ( r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X0)
                    & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) )
                  | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X1)) ) ) )
            & ( ( ! [X5] :
                    ( k1_funct_1(X2,X5) = k1_funct_1(X1,X5)
                    | ~ r2_hidden(X5,k1_relat_1(X1)) )
                & ! [X6] :
                    ( ( r2_hidden(X6,k1_relat_1(X1))
                      | ~ r2_hidden(k1_funct_1(X2,X6),X0)
                      | ~ r2_hidden(X6,k1_relat_1(X2)) )
                    & ( ( r2_hidden(k1_funct_1(X2,X6),X0)
                        & r2_hidden(X6,k1_relat_1(X2)) )
                      | ~ r2_hidden(X6,k1_relat_1(X1)) ) ) )
              | k8_relat_1(X0,X2) != X1 ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f28,f30,f29])).

fof(f29,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( k1_funct_1(X2,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X2,sK5(X1,X2)) != k1_funct_1(X1,sK5(X1,X2))
        & r2_hidden(sK5(X1,X2),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
            | ~ r2_hidden(X4,k1_relat_1(X2))
            | ~ r2_hidden(X4,k1_relat_1(X1)) )
          & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
              & r2_hidden(X4,k1_relat_1(X2)) )
            | r2_hidden(X4,k1_relat_1(X1)) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))
          | ~ r2_hidden(sK6(X0,X1,X2),k1_relat_1(X1)) )
        & ( ( r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X0)
            & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) )
          | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X2) = X1
              | ? [X3] :
                  ( k1_funct_1(X2,X3) != k1_funct_1(X1,X3)
                  & r2_hidden(X3,k1_relat_1(X1)) )
              | ? [X4] :
                  ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
                    | ~ r2_hidden(X4,k1_relat_1(X2))
                    | ~ r2_hidden(X4,k1_relat_1(X1)) )
                  & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                      & r2_hidden(X4,k1_relat_1(X2)) )
                    | r2_hidden(X4,k1_relat_1(X1)) ) ) )
            & ( ( ! [X5] :
                    ( k1_funct_1(X2,X5) = k1_funct_1(X1,X5)
                    | ~ r2_hidden(X5,k1_relat_1(X1)) )
                & ! [X6] :
                    ( ( r2_hidden(X6,k1_relat_1(X1))
                      | ~ r2_hidden(k1_funct_1(X2,X6),X0)
                      | ~ r2_hidden(X6,k1_relat_1(X2)) )
                    & ( ( r2_hidden(k1_funct_1(X2,X6),X0)
                        & r2_hidden(X6,k1_relat_1(X2)) )
                      | ~ r2_hidden(X6,k1_relat_1(X1)) ) ) )
              | k8_relat_1(X0,X2) != X1 ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X2) = X1
              | ? [X3] :
                  ( k1_funct_1(X2,X3) != k1_funct_1(X1,X3)
                  & r2_hidden(X3,k1_relat_1(X1)) )
              | ? [X4] :
                  ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
                    | ~ r2_hidden(X4,k1_relat_1(X2))
                    | ~ r2_hidden(X4,k1_relat_1(X1)) )
                  & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                      & r2_hidden(X4,k1_relat_1(X2)) )
                    | r2_hidden(X4,k1_relat_1(X1)) ) ) )
            & ( ( ! [X3] :
                    ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,k1_relat_1(X1)) )
                & ! [X4] :
                    ( ( r2_hidden(X4,k1_relat_1(X1))
                      | ~ r2_hidden(k1_funct_1(X2,X4),X0)
                      | ~ r2_hidden(X4,k1_relat_1(X2)) )
                    & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                        & r2_hidden(X4,k1_relat_1(X2)) )
                      | ~ r2_hidden(X4,k1_relat_1(X1)) ) ) )
              | k8_relat_1(X0,X2) != X1 ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X2) = X1
              | ? [X3] :
                  ( k1_funct_1(X2,X3) != k1_funct_1(X1,X3)
                  & r2_hidden(X3,k1_relat_1(X1)) )
              | ? [X4] :
                  ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
                    | ~ r2_hidden(X4,k1_relat_1(X2))
                    | ~ r2_hidden(X4,k1_relat_1(X1)) )
                  & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                      & r2_hidden(X4,k1_relat_1(X2)) )
                    | r2_hidden(X4,k1_relat_1(X1)) ) ) )
            & ( ( ! [X3] :
                    ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,k1_relat_1(X1)) )
                & ! [X4] :
                    ( ( r2_hidden(X4,k1_relat_1(X1))
                      | ~ r2_hidden(k1_funct_1(X2,X4),X0)
                      | ~ r2_hidden(X4,k1_relat_1(X2)) )
                    & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                        & r2_hidden(X4,k1_relat_1(X2)) )
                      | ~ r2_hidden(X4,k1_relat_1(X1)) ) ) )
              | k8_relat_1(X0,X2) != X1 ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X2,X3) = k1_funct_1(X1,X3) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) ) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X2,X3) = k1_funct_1(X1,X3) )
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X3),X0)
                    & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_1)).

fof(f78,plain,
    ( r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl7_1
  <=> r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f73,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl7_2
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f122,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | ~ spl7_1
    | spl7_3 ),
    inference(subsumption_resolution,[],[f120,f34])).

fof(f120,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl7_1
    | spl7_3 ),
    inference(subsumption_resolution,[],[f119,f35])).

fof(f119,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_1
    | spl7_3 ),
    inference(subsumption_resolution,[],[f117,f76])).

fof(f76,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl7_3
  <=> r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f117,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(resolution,[],[f78,f88])).

fof(f88,plain,(
    ! [X6,X2,X0] :
      ( ~ r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2)))
      | r2_hidden(k1_funct_1(X2,X6),X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f87,f45])).

fof(f87,plain,(
    ! [X6,X2,X0] :
      ( r2_hidden(k1_funct_1(X2,X6),X0)
      | ~ r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k8_relat_1(X0,X2)) ) ),
    inference(subsumption_resolution,[],[f65,f46])).

fof(f65,plain,(
    ! [X6,X2,X0] :
      ( r2_hidden(k1_funct_1(X2,X6),X0)
      | ~ r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(k8_relat_1(X0,X2)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X6),X0)
      | ~ r2_hidden(X6,k1_relat_1(X1))
      | k8_relat_1(X0,X2) != X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f116,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f114,f34])).

fof(f114,plain,
    ( ~ v1_relat_1(sK2)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f113,f35])).

fof(f113,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f112,f81])).

fof(f81,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f112,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f105,f79])).

fof(f79,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f105,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_1 ),
    inference(resolution,[],[f86,f70])).

fof(f70,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f86,plain,(
    ! [X6,X2,X0] :
      ( r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2)))
      | ~ r2_hidden(k1_funct_1(X2,X6),X0)
      | ~ r2_hidden(X6,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f85,f45])).

fof(f85,plain,(
    ! [X6,X2,X0] :
      ( r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2)))
      | ~ r2_hidden(k1_funct_1(X2,X6),X0)
      | ~ r2_hidden(X6,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k8_relat_1(X0,X2)) ) ),
    inference(subsumption_resolution,[],[f64,f46])).

fof(f64,plain,(
    ! [X6,X2,X0] :
      ( r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2)))
      | ~ r2_hidden(k1_funct_1(X2,X6),X0)
      | ~ r2_hidden(X6,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(k8_relat_1(X0,X2)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,k1_relat_1(X1))
      | ~ r2_hidden(k1_funct_1(X2,X6),X0)
      | ~ r2_hidden(X6,k1_relat_1(X2))
      | k8_relat_1(X0,X2) != X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f82,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f36,f72,f69])).

fof(f36,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f20])).

fof(f80,plain,
    ( spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f37,f75,f69])).

fof(f37,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f20])).

fof(f77,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f38,f75,f72,f69])).

fof(f38,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:53:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (9722)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.44  % (9722)Refutation not found, incomplete strategy% (9722)------------------------------
% 0.21/0.44  % (9722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (9722)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.44  
% 0.21/0.44  % (9722)Memory used [KB]: 10618
% 0.21/0.44  % (9722)Time elapsed: 0.039 s
% 0.21/0.44  % (9722)------------------------------
% 0.21/0.44  % (9722)------------------------------
% 0.21/0.45  % (9718)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.46  % (9706)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (9704)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (9711)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (9704)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f77,f80,f82,f116,f122,f128])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    ~spl7_1 | spl7_2),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f127])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    $false | (~spl7_1 | spl7_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f73,f124])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl7_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f123,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    v1_relat_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    (~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))) & ((r2_hidden(k1_funct_1(sK2,sK0),sK1) & r2_hidden(sK0,k1_relat_1(sK2))) | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) & v1_funct_1(X2) & v1_relat_1(X2)) => ((~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))) & ((r2_hidden(k1_funct_1(sK2,sK0),sK1) & r2_hidden(sK0,k1_relat_1(sK2))) | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((((~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.48    inference(nnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <~> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <~> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f5])).
% 0.21/0.48  fof(f5,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_funct_1)).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl7_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f118,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    v1_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl7_1),
% 0.21/0.48    inference(resolution,[],[f78,f90])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ( ! [X6,X2,X0] : (~r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2))) | r2_hidden(X6,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f89,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(k8_relat_1(X0,X1)) & v1_relat_1(k8_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(k8_relat_1(X0,X1)) & v1_relat_1(k8_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v1_funct_1(k8_relat_1(X0,X1)) & v1_relat_1(k8_relat_1(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_funct_1)).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ( ! [X6,X2,X0] : (r2_hidden(X6,k1_relat_1(X2)) | ~r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(k8_relat_1(X0,X2))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f66,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_funct_1(k8_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X6,X2,X0] : (r2_hidden(X6,k1_relat_1(X2)) | ~r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(k8_relat_1(X0,X2)) | ~v1_relat_1(k8_relat_1(X0,X2))) )),
% 0.21/0.48    inference(equality_resolution,[],[f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,k1_relat_1(X2)) | ~r2_hidden(X6,k1_relat_1(X1)) | k8_relat_1(X0,X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X2) = X1 | (k1_funct_1(X2,sK5(X1,X2)) != k1_funct_1(X1,sK5(X1,X2)) & r2_hidden(sK5(X1,X2),k1_relat_1(X1))) | ((~r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X0) | ~r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(sK6(X0,X1,X2),k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X0) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))) | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X1))))) & ((! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X1,X5) | ~r2_hidden(X5,k1_relat_1(X1))) & ! [X6] : ((r2_hidden(X6,k1_relat_1(X1)) | ~r2_hidden(k1_funct_1(X2,X6),X0) | ~r2_hidden(X6,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X6),X0) & r2_hidden(X6,k1_relat_1(X2))) | ~r2_hidden(X6,k1_relat_1(X1))))) | k8_relat_1(X0,X2) != X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f28,f30,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X2,X1] : (? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X2,sK5(X1,X2)) != k1_funct_1(X1,sK5(X1,X2)) & r2_hidden(sK5(X1,X2),k1_relat_1(X1))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X4] : ((~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2)) | ~r2_hidden(X4,k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | r2_hidden(X4,k1_relat_1(X1)))) => ((~r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X0) | ~r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(sK6(X0,X1,X2),k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X0) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))) | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X1)))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X2) = X1 | ? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,k1_relat_1(X1))) | ? [X4] : ((~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2)) | ~r2_hidden(X4,k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | r2_hidden(X4,k1_relat_1(X1))))) & ((! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X1,X5) | ~r2_hidden(X5,k1_relat_1(X1))) & ! [X6] : ((r2_hidden(X6,k1_relat_1(X1)) | ~r2_hidden(k1_funct_1(X2,X6),X0) | ~r2_hidden(X6,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X6),X0) & r2_hidden(X6,k1_relat_1(X2))) | ~r2_hidden(X6,k1_relat_1(X1))))) | k8_relat_1(X0,X2) != X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(rectify,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X2) = X1 | ? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,k1_relat_1(X1))) | ? [X4] : ((~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2)) | ~r2_hidden(X4,k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | r2_hidden(X4,k1_relat_1(X1))))) & ((! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : ((r2_hidden(X4,k1_relat_1(X1)) | ~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X4,k1_relat_1(X1))))) | k8_relat_1(X0,X2) != X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X2) = X1 | (? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,k1_relat_1(X1))) | ? [X4] : (((~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X4,k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | r2_hidden(X4,k1_relat_1(X1)))))) & ((! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : ((r2_hidden(X4,k1_relat_1(X1)) | (~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X4,k1_relat_1(X1))))) | k8_relat_1(X0,X2) != X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X2) = X1 <=> (! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : (r2_hidden(X4,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2)))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X2) = X1 <=> (! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : (r2_hidden(X4,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2)))))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (k8_relat_1(X0,X2) = X1 <=> (! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X2,X3) = k1_funct_1(X1,X3)) & ! [X4] : (r2_hidden(X4,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))))))))),
% 0.21/0.48    inference(rectify,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (k8_relat_1(X0,X2) = X1 <=> (! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X2,X3) = k1_funct_1(X1,X3)) & ! [X3] : (r2_hidden(X3,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X3),X0) & r2_hidden(X3,k1_relat_1(X2))))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_1)).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) | ~spl7_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    spl7_1 <=> r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ~r2_hidden(sK0,k1_relat_1(sK2)) | spl7_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl7_2 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    ~spl7_1 | spl7_3),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f121])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    $false | (~spl7_1 | spl7_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f120,f34])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | (~spl7_1 | spl7_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f119,f35])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_1 | spl7_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f117,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | spl7_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f75])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl7_3 <=> r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl7_1),
% 0.21/0.48    inference(resolution,[],[f78,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ( ! [X6,X2,X0] : (~r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2))) | r2_hidden(k1_funct_1(X2,X6),X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f87,f45])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ( ! [X6,X2,X0] : (r2_hidden(k1_funct_1(X2,X6),X0) | ~r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(k8_relat_1(X0,X2))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f65,f46])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X6,X2,X0] : (r2_hidden(k1_funct_1(X2,X6),X0) | ~r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(k8_relat_1(X0,X2)) | ~v1_relat_1(k8_relat_1(X0,X2))) )),
% 0.21/0.48    inference(equality_resolution,[],[f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X6,X2,X0,X1] : (r2_hidden(k1_funct_1(X2,X6),X0) | ~r2_hidden(X6,k1_relat_1(X1)) | k8_relat_1(X0,X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    spl7_1 | ~spl7_2 | ~spl7_3),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f115])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    $false | (spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f114,f34])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | (spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f113,f35])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f112,f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl7_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f72])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl7_1 | ~spl7_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f105,f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~spl7_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f75])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl7_1),
% 0.21/0.48    inference(resolution,[],[f86,f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ~r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) | spl7_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f69])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X6,X2,X0] : (r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2))) | ~r2_hidden(k1_funct_1(X2,X6),X0) | ~r2_hidden(X6,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f85,f45])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X6,X2,X0] : (r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2))) | ~r2_hidden(k1_funct_1(X2,X6),X0) | ~r2_hidden(X6,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(k8_relat_1(X0,X2))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f64,f46])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X6,X2,X0] : (r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2))) | ~r2_hidden(k1_funct_1(X2,X6),X0) | ~r2_hidden(X6,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(k8_relat_1(X0,X2)) | ~v1_relat_1(k8_relat_1(X0,X2))) )),
% 0.21/0.48    inference(equality_resolution,[],[f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,k1_relat_1(X1)) | ~r2_hidden(k1_funct_1(X2,X6),X0) | ~r2_hidden(X6,k1_relat_1(X2)) | k8_relat_1(X0,X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    spl7_1 | spl7_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f36,f72,f69])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    r2_hidden(sK0,k1_relat_1(sK2)) | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl7_1 | spl7_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f37,f75,f69])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    r2_hidden(k1_funct_1(sK2,sK0),sK1) | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ~spl7_1 | ~spl7_2 | ~spl7_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f38,f75,f72,f69])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (9704)------------------------------
% 0.21/0.48  % (9704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9704)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (9704)Memory used [KB]: 10618
% 0.21/0.48  % (9704)Time elapsed: 0.062 s
% 0.21/0.48  % (9704)------------------------------
% 0.21/0.48  % (9704)------------------------------
% 0.21/0.48  % (9714)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (9701)Success in time 0.127 s
%------------------------------------------------------------------------------
