%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 245 expanded)
%              Number of leaves         :   13 (  65 expanded)
%              Depth                    :   20
%              Number of atoms          :  434 (1549 expanded)
%              Number of equality atoms :   32 (  87 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f112,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f64,f66,f89,f104,f107,f111])).

fof(f111,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | spl5_4 ),
    inference(subsumption_resolution,[],[f109,f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
        <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_funct_1)).

fof(f109,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f108,f28])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f108,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_4 ),
    inference(resolution,[],[f103,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k8_relat_1(X1,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f75,f32])).

fof(f32,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k8_relat_1(X1,X0))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f74,f33])).

fof(f33,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k8_relat_1(X1,X0))
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k8_relat_1(X1,X0))
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f37,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f103,plain,
    ( ~ v1_funct_1(k8_relat_1(sK1,sK2))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl5_4
  <=> v1_funct_1(k8_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f107,plain,
    ( ~ spl5_4
    | spl5_3
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f106,f53,f59,f102])).

fof(f59,plain,
    ( spl5_3
  <=> r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f53,plain,
    ( spl5_1
  <=> r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f106,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ v1_funct_1(k8_relat_1(sK1,sK2))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f105,f27])).

fof(f105,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k8_relat_1(sK1,sK2))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f90,f28])).

fof(f90,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k8_relat_1(sK1,sK2))
    | ~ spl5_1 ),
    inference(resolution,[],[f62,f69])).

fof(f69,plain,(
    ! [X6,X2,X0] :
      ( ~ r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2)))
      | r2_hidden(k1_funct_1(X2,X6),X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(k8_relat_1(X0,X2)) ) ),
    inference(subsumption_resolution,[],[f50,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f50,plain,(
    ! [X6,X2,X0] :
      ( r2_hidden(k1_funct_1(X2,X6),X0)
      | ~ r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(k8_relat_1(X0,X2)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X6),X0)
      | ~ r2_hidden(X6,k1_relat_1(X1))
      | k8_relat_1(X0,X2) != X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X2) = X1
              | ( k1_funct_1(X2,sK3(X1,X2)) != k1_funct_1(X1,sK3(X1,X2))
                & r2_hidden(sK3(X1,X2),k1_relat_1(X1)) )
              | ( ( ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))
                  | ~ r2_hidden(sK4(X0,X1,X2),k1_relat_1(X1)) )
                & ( ( r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X0)
                    & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) )
                  | r2_hidden(sK4(X0,X1,X2),k1_relat_1(X1)) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f25,f24])).

fof(f24,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( k1_funct_1(X2,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X2,sK3(X1,X2)) != k1_funct_1(X1,sK3(X1,X2))
        & r2_hidden(sK3(X1,X2),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
            | ~ r2_hidden(X4,k1_relat_1(X2))
            | ~ r2_hidden(X4,k1_relat_1(X1)) )
          & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
              & r2_hidden(X4,k1_relat_1(X2)) )
            | r2_hidden(X4,k1_relat_1(X1)) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))
          | ~ r2_hidden(sK4(X0,X1,X2),k1_relat_1(X1)) )
        & ( ( r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X0)
            & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) )
          | r2_hidden(sK4(X0,X1,X2),k1_relat_1(X1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
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
    inference(rectify,[],[f5])).

fof(f5,axiom,(
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

fof(f62,plain,
    ( r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f104,plain,
    ( ~ spl5_4
    | spl5_2
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f100,f53,f56,f102])).

fof(f56,plain,
    ( spl5_2
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f100,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(k8_relat_1(sK1,sK2))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f99,f27])).

fof(f99,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k8_relat_1(sK1,sK2))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f91,f28])).

fof(f91,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k8_relat_1(sK1,sK2))
    | ~ spl5_1 ),
    inference(resolution,[],[f62,f70])).

fof(f70,plain,(
    ! [X6,X2,X0] :
      ( ~ r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2)))
      | r2_hidden(X6,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(k8_relat_1(X0,X2)) ) ),
    inference(subsumption_resolution,[],[f51,f34])).

fof(f51,plain,(
    ! [X6,X2,X0] :
      ( r2_hidden(X6,k1_relat_1(X2))
      | ~ r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(k8_relat_1(X0,X2)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,k1_relat_1(X2))
      | ~ r2_hidden(X6,k1_relat_1(X1))
      | k8_relat_1(X0,X2) != X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f89,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f87,f27])).

fof(f87,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f86,f28])).

fof(f86,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(resolution,[],[f85,f76])).

fof(f85,plain,
    ( ~ v1_funct_1(k8_relat_1(sK1,sK2))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f84,f27])).

fof(f84,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k8_relat_1(sK1,sK2))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f83,f28])).

fof(f83,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k8_relat_1(sK1,sK2))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f82,f65])).

fof(f65,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f82,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k8_relat_1(sK1,sK2))
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f77,f63])).

fof(f63,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f77,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k8_relat_1(sK1,sK2))
    | spl5_1 ),
    inference(resolution,[],[f68,f54])).

fof(f54,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f68,plain,(
    ! [X6,X2,X0] :
      ( r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2)))
      | ~ r2_hidden(k1_funct_1(X2,X6),X0)
      | ~ r2_hidden(X6,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(k8_relat_1(X0,X2)) ) ),
    inference(subsumption_resolution,[],[f49,f34])).

fof(f49,plain,(
    ! [X6,X2,X0] :
      ( r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2)))
      | ~ r2_hidden(k1_funct_1(X2,X6),X0)
      | ~ r2_hidden(X6,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(k8_relat_1(X0,X2)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,k1_relat_1(X1))
      | ~ r2_hidden(k1_funct_1(X2,X6),X0)
      | ~ r2_hidden(X6,k1_relat_1(X2))
      | k8_relat_1(X0,X2) != X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f29,f56,f53])).

fof(f29,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f30,f59,f53])).

fof(f30,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f31,f59,f56,f53])).

fof(f31,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:59:05 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.22/0.49  % (29719)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (29732)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (29719)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f61,f64,f66,f89,f104,f107,f111])).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    spl5_4),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f110])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    $false | spl5_4),
% 0.22/0.49    inference(subsumption_resolution,[],[f109,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    v1_relat_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    (~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))) & ((r2_hidden(k1_funct_1(sK2,sK0),sK1) & r2_hidden(sK0,k1_relat_1(sK2))) | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) & v1_funct_1(X2) & v1_relat_1(X2)) => ((~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))) & ((r2_hidden(k1_funct_1(sK2,sK0),sK1) & r2_hidden(sK0,k1_relat_1(sK2))) | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ? [X0,X1,X2] : ((((~r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) & ((r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2))) | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.49    inference(nnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ? [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <~> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.49    inference(flattening,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ? [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <~> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.49    inference(negated_conjecture,[],[f6])).
% 0.22/0.49  fof(f6,conjecture,(
% 0.22/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_funct_1)).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | spl5_4),
% 0.22/0.49    inference(subsumption_resolution,[],[f108,f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    v1_funct_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl5_4),
% 0.22/0.49    inference(resolution,[],[f103,f76])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_funct_1(k8_relat_1(X1,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f75,f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_funct_1(k8_relat_1(X1,X0)) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f74,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_funct_1(k8_relat_1(X1,X0)) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f73])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_funct_1(k8_relat_1(X1,X0)) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(superposition,[],[f37,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    ~v1_funct_1(k8_relat_1(sK1,sK2)) | spl5_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f102])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    spl5_4 <=> v1_funct_1(k8_relat_1(sK1,sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    ~spl5_4 | spl5_3 | ~spl5_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f106,f53,f59,f102])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    spl5_3 <=> r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    spl5_1 <=> r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~v1_funct_1(k8_relat_1(sK1,sK2)) | ~spl5_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f105,f27])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(k8_relat_1(sK1,sK2)) | ~spl5_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f90,f28])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k8_relat_1(sK1,sK2)) | ~spl5_1),
% 0.22/0.49    inference(resolution,[],[f62,f69])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    ( ! [X6,X2,X0] : (~r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2))) | r2_hidden(k1_funct_1(X2,X6),X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(k8_relat_1(X0,X2))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f50,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X6,X2,X0] : (r2_hidden(k1_funct_1(X2,X6),X0) | ~r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(k8_relat_1(X0,X2)) | ~v1_relat_1(k8_relat_1(X0,X2))) )),
% 0.22/0.49    inference(equality_resolution,[],[f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X6,X2,X0,X1] : (r2_hidden(k1_funct_1(X2,X6),X0) | ~r2_hidden(X6,k1_relat_1(X1)) | k8_relat_1(X0,X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X2) = X1 | (k1_funct_1(X2,sK3(X1,X2)) != k1_funct_1(X1,sK3(X1,X2)) & r2_hidden(sK3(X1,X2),k1_relat_1(X1))) | ((~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X0) | ~r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(sK4(X0,X1,X2),k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X0) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))) | r2_hidden(sK4(X0,X1,X2),k1_relat_1(X1))))) & ((! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X1,X5) | ~r2_hidden(X5,k1_relat_1(X1))) & ! [X6] : ((r2_hidden(X6,k1_relat_1(X1)) | ~r2_hidden(k1_funct_1(X2,X6),X0) | ~r2_hidden(X6,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X6),X0) & r2_hidden(X6,k1_relat_1(X2))) | ~r2_hidden(X6,k1_relat_1(X1))))) | k8_relat_1(X0,X2) != X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f25,f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X2,X1] : (? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X2,sK3(X1,X2)) != k1_funct_1(X1,sK3(X1,X2)) & r2_hidden(sK3(X1,X2),k1_relat_1(X1))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X2,X1,X0] : (? [X4] : ((~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2)) | ~r2_hidden(X4,k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | r2_hidden(X4,k1_relat_1(X1)))) => ((~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X0) | ~r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(sK4(X0,X1,X2),k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X0) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))) | r2_hidden(sK4(X0,X1,X2),k1_relat_1(X1)))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X2) = X1 | ? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,k1_relat_1(X1))) | ? [X4] : ((~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2)) | ~r2_hidden(X4,k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | r2_hidden(X4,k1_relat_1(X1))))) & ((! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X1,X5) | ~r2_hidden(X5,k1_relat_1(X1))) & ! [X6] : ((r2_hidden(X6,k1_relat_1(X1)) | ~r2_hidden(k1_funct_1(X2,X6),X0) | ~r2_hidden(X6,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X6),X0) & r2_hidden(X6,k1_relat_1(X2))) | ~r2_hidden(X6,k1_relat_1(X1))))) | k8_relat_1(X0,X2) != X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(rectify,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X2) = X1 | ? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,k1_relat_1(X1))) | ? [X4] : ((~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2)) | ~r2_hidden(X4,k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | r2_hidden(X4,k1_relat_1(X1))))) & ((! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : ((r2_hidden(X4,k1_relat_1(X1)) | ~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X4,k1_relat_1(X1))))) | k8_relat_1(X0,X2) != X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X2) = X1 | (? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,k1_relat_1(X1))) | ? [X4] : (((~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X4,k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | r2_hidden(X4,k1_relat_1(X1)))))) & ((! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : ((r2_hidden(X4,k1_relat_1(X1)) | (~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X4,k1_relat_1(X1))))) | k8_relat_1(X0,X2) != X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X2) = X1 <=> (! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : (r2_hidden(X4,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2)))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X2) = X1 <=> (! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : (r2_hidden(X4,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2)))))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (k8_relat_1(X0,X2) = X1 <=> (! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X2,X3) = k1_funct_1(X1,X3)) & ! [X4] : (r2_hidden(X4,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))))))))),
% 0.22/0.49    inference(rectify,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (k8_relat_1(X0,X2) = X1 <=> (! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X2,X3) = k1_funct_1(X1,X3)) & ! [X3] : (r2_hidden(X3,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X3),X0) & r2_hidden(X3,k1_relat_1(X2))))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_1)).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) | ~spl5_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f53])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    ~spl5_4 | spl5_2 | ~spl5_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f100,f53,f56,f102])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    spl5_2 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(k8_relat_1(sK1,sK2)) | ~spl5_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f99,f27])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(k8_relat_1(sK1,sK2)) | ~spl5_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f91,f28])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k8_relat_1(sK1,sK2)) | ~spl5_1),
% 0.22/0.49    inference(resolution,[],[f62,f70])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ( ! [X6,X2,X0] : (~r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2))) | r2_hidden(X6,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(k8_relat_1(X0,X2))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f51,f34])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X6,X2,X0] : (r2_hidden(X6,k1_relat_1(X2)) | ~r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(k8_relat_1(X0,X2)) | ~v1_relat_1(k8_relat_1(X0,X2))) )),
% 0.22/0.49    inference(equality_resolution,[],[f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,k1_relat_1(X2)) | ~r2_hidden(X6,k1_relat_1(X1)) | k8_relat_1(X0,X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    spl5_1 | ~spl5_2 | ~spl5_3),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f88])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    $false | (spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f87,f27])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | (spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f86,f28])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.22/0.50    inference(resolution,[],[f85,f76])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    ~v1_funct_1(k8_relat_1(sK1,sK2)) | (spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f84,f27])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | ~v1_funct_1(k8_relat_1(sK1,sK2)) | (spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f83,f28])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k8_relat_1(sK1,sK2)) | (spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f82,f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl5_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f56])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k8_relat_1(sK1,sK2)) | (spl5_1 | ~spl5_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f77,f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~spl5_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f59])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k8_relat_1(sK1,sK2)) | spl5_1),
% 0.22/0.50    inference(resolution,[],[f68,f54])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ~r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) | spl5_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f53])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X6,X2,X0] : (r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2))) | ~r2_hidden(k1_funct_1(X2,X6),X0) | ~r2_hidden(X6,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(k8_relat_1(X0,X2))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f49,f34])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X6,X2,X0] : (r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2))) | ~r2_hidden(k1_funct_1(X2,X6),X0) | ~r2_hidden(X6,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(k8_relat_1(X0,X2)) | ~v1_relat_1(k8_relat_1(X0,X2))) )),
% 0.22/0.50    inference(equality_resolution,[],[f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,k1_relat_1(X1)) | ~r2_hidden(k1_funct_1(X2,X6),X0) | ~r2_hidden(X6,k1_relat_1(X2)) | k8_relat_1(X0,X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    spl5_1 | spl5_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f29,f56,f53])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    r2_hidden(sK0,k1_relat_1(sK2)) | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    spl5_1 | spl5_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f30,f59,f53])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    r2_hidden(k1_funct_1(sK2,sK0),sK1) | r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f31,f59,f56,f53])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (29719)------------------------------
% 0.22/0.50  % (29719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (29719)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (29719)Memory used [KB]: 10618
% 0.22/0.50  % (29719)Time elapsed: 0.066 s
% 0.22/0.50  % (29719)------------------------------
% 0.22/0.50  % (29719)------------------------------
% 0.22/0.50  % (29716)Success in time 0.13 s
%------------------------------------------------------------------------------
