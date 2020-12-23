%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 103 expanded)
%              Number of leaves         :   14 (  39 expanded)
%              Depth                    :   17
%              Number of atoms          :  311 ( 497 expanded)
%              Number of equality atoms :   37 (  43 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f102,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f70,f80,f101])).

fof(f101,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | spl5_1
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f98,f78,f52,f68,f60,f56])).

fof(f56,plain,
    ( spl5_2
  <=> r2_hidden(sK2,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f60,plain,
    ( spl5_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f68,plain,
    ( spl5_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f52,plain,
    ( spl5_1
  <=> r2_hidden(k1_funct_1(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f78,plain,
    ( spl5_6
  <=> sK1 = k8_relat_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f98,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK2,k1_relat_1(sK1))
    | spl5_1
    | ~ spl5_6 ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | spl5_1
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f96,f79])).

fof(f79,plain,
    ( sK1 = k8_relat_1(sK0,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f96,plain,
    ( ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | spl5_1
    | ~ spl5_6 ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,
    ( ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | spl5_1
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f94,f79])).

fof(f94,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k8_relat_1(sK0,sK1))
    | ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | spl5_1
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f93,f79])).

fof(f93,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(k8_relat_1(sK0,sK1)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k8_relat_1(sK0,sK1))
    | ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | spl5_1 ),
    inference(resolution,[],[f49,f53])).

fof(f53,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK2),sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f49,plain,(
    ! [X6,X2,X0] :
      ( r2_hidden(k1_funct_1(X2,X6),X0)
      | ~ r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(k8_relat_1(X0,X2))
      | ~ v1_relat_1(k8_relat_1(X0,X2)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
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
    inference(rectify,[],[f4])).

fof(f4,axiom,(
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

fof(f80,plain,
    ( spl5_6
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f75,f68,f64,f78])).

fof(f64,plain,
    ( spl5_4
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f75,plain,
    ( sK1 = k8_relat_1(sK0,sK1)
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(resolution,[],[f73,f65])).

fof(f65,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f73,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(sK1,X0)
        | sK1 = k8_relat_1(X0,sK1) )
    | ~ spl5_5 ),
    inference(resolution,[],[f72,f69])).

fof(f69,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = X1
      | ~ v5_relat_1(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f32,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f70,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f27,f68])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK2),sK0)
    & r2_hidden(sK2,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v5_relat_1(sK1,sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f18,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
            & r2_hidden(X2,k1_relat_1(X1)) )
        & v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(sK1,X2),sK0)
          & r2_hidden(X2,k1_relat_1(sK1)) )
      & v1_funct_1(sK1)
      & v5_relat_1(sK1,sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ~ r2_hidden(k1_funct_1(sK1,X2),sK0)
        & r2_hidden(X2,k1_relat_1(sK1)) )
   => ( ~ r2_hidden(k1_funct_1(sK1,sK2),sK0)
      & r2_hidden(sK2,k1_relat_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
          & r2_hidden(X2,k1_relat_1(X1)) )
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
          & r2_hidden(X2,k1_relat_1(X1)) )
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v5_relat_1(X1,X0)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( r2_hidden(X2,k1_relat_1(X1))
           => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(f66,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f28,f64])).

fof(f28,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f29,f60])).

fof(f29,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f30,f56])).

fof(f30,plain,(
    r2_hidden(sK2,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f31,f52])).

fof(f31,plain,(
    ~ r2_hidden(k1_funct_1(sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:29:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (23123)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (23123)Refutation not found, incomplete strategy% (23123)------------------------------
% 0.22/0.47  % (23123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (23123)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (23123)Memory used [KB]: 10618
% 0.22/0.47  % (23123)Time elapsed: 0.050 s
% 0.22/0.47  % (23123)------------------------------
% 0.22/0.47  % (23123)------------------------------
% 0.22/0.47  % (23130)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.47  % (23128)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (23128)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f70,f80,f101])).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    ~spl5_2 | ~spl5_3 | ~spl5_5 | spl5_1 | ~spl5_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f98,f78,f52,f68,f60,f56])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    spl5_2 <=> r2_hidden(sK2,k1_relat_1(sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    spl5_3 <=> v1_funct_1(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    spl5_5 <=> v1_relat_1(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    spl5_1 <=> r2_hidden(k1_funct_1(sK1,sK2),sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    spl5_6 <=> sK1 = k8_relat_1(sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~r2_hidden(sK2,k1_relat_1(sK1)) | (spl5_1 | ~spl5_6)),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f97])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~r2_hidden(sK2,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | (spl5_1 | ~spl5_6)),
% 0.22/0.48    inference(forward_demodulation,[],[f96,f79])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    sK1 = k8_relat_1(sK0,sK1) | ~spl5_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f78])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    ~v1_funct_1(sK1) | ~r2_hidden(sK2,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~v1_relat_1(k8_relat_1(sK0,sK1)) | (spl5_1 | ~spl5_6)),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f95])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    ~v1_funct_1(sK1) | ~r2_hidden(sK2,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k8_relat_1(sK0,sK1)) | (spl5_1 | ~spl5_6)),
% 0.22/0.48    inference(forward_demodulation,[],[f94,f79])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    ~r2_hidden(sK2,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(k8_relat_1(sK0,sK1)) | ~v1_relat_1(k8_relat_1(sK0,sK1)) | (spl5_1 | ~spl5_6)),
% 0.22/0.48    inference(forward_demodulation,[],[f93,f79])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    ~r2_hidden(sK2,k1_relat_1(k8_relat_1(sK0,sK1))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(k8_relat_1(sK0,sK1)) | ~v1_relat_1(k8_relat_1(sK0,sK1)) | spl5_1),
% 0.22/0.48    inference(resolution,[],[f49,f53])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ~r2_hidden(k1_funct_1(sK1,sK2),sK0) | spl5_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f52])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X6,X2,X0] : (r2_hidden(k1_funct_1(X2,X6),X0) | ~r2_hidden(X6,k1_relat_1(k8_relat_1(X0,X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(k8_relat_1(X0,X2)) | ~v1_relat_1(k8_relat_1(X0,X2))) )),
% 0.22/0.48    inference(equality_resolution,[],[f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X6,X2,X0,X1] : (r2_hidden(k1_funct_1(X2,X6),X0) | ~r2_hidden(X6,k1_relat_1(X1)) | k8_relat_1(X0,X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X2) = X1 | (k1_funct_1(X2,sK3(X1,X2)) != k1_funct_1(X1,sK3(X1,X2)) & r2_hidden(sK3(X1,X2),k1_relat_1(X1))) | ((~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X0) | ~r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(sK4(X0,X1,X2),k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X0) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))) | r2_hidden(sK4(X0,X1,X2),k1_relat_1(X1))))) & ((! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X1,X5) | ~r2_hidden(X5,k1_relat_1(X1))) & ! [X6] : ((r2_hidden(X6,k1_relat_1(X1)) | ~r2_hidden(k1_funct_1(X2,X6),X0) | ~r2_hidden(X6,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X6),X0) & r2_hidden(X6,k1_relat_1(X2))) | ~r2_hidden(X6,k1_relat_1(X1))))) | k8_relat_1(X0,X2) != X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f25,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X2,X1] : (? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X2,sK3(X1,X2)) != k1_funct_1(X1,sK3(X1,X2)) & r2_hidden(sK3(X1,X2),k1_relat_1(X1))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X2,X1,X0] : (? [X4] : ((~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2)) | ~r2_hidden(X4,k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | r2_hidden(X4,k1_relat_1(X1)))) => ((~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X0) | ~r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(sK4(X0,X1,X2),k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X0) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))) | r2_hidden(sK4(X0,X1,X2),k1_relat_1(X1)))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X2) = X1 | ? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,k1_relat_1(X1))) | ? [X4] : ((~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2)) | ~r2_hidden(X4,k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | r2_hidden(X4,k1_relat_1(X1))))) & ((! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X1,X5) | ~r2_hidden(X5,k1_relat_1(X1))) & ! [X6] : ((r2_hidden(X6,k1_relat_1(X1)) | ~r2_hidden(k1_funct_1(X2,X6),X0) | ~r2_hidden(X6,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X6),X0) & r2_hidden(X6,k1_relat_1(X2))) | ~r2_hidden(X6,k1_relat_1(X1))))) | k8_relat_1(X0,X2) != X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(rectify,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X2) = X1 | ? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,k1_relat_1(X1))) | ? [X4] : ((~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2)) | ~r2_hidden(X4,k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | r2_hidden(X4,k1_relat_1(X1))))) & ((! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : ((r2_hidden(X4,k1_relat_1(X1)) | ~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X4,k1_relat_1(X1))))) | k8_relat_1(X0,X2) != X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X2) = X1 | (? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,k1_relat_1(X1))) | ? [X4] : (((~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X4,k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | r2_hidden(X4,k1_relat_1(X1)))))) & ((! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : ((r2_hidden(X4,k1_relat_1(X1)) | (~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X4,k1_relat_1(X1))))) | k8_relat_1(X0,X2) != X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(nnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X2) = X1 <=> (! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : (r2_hidden(X4,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2)))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X2) = X1 <=> (! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : (r2_hidden(X4,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2)))))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (k8_relat_1(X0,X2) = X1 <=> (! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X2,X3) = k1_funct_1(X1,X3)) & ! [X4] : (r2_hidden(X4,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))))))))),
% 0.22/0.48    inference(rectify,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (k8_relat_1(X0,X2) = X1 <=> (! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X2,X3) = k1_funct_1(X1,X3)) & ! [X3] : (r2_hidden(X3,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X3),X0) & r2_hidden(X3,k1_relat_1(X2))))))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_1)).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    spl5_6 | ~spl5_4 | ~spl5_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f75,f68,f64,f78])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    spl5_4 <=> v5_relat_1(sK1,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    sK1 = k8_relat_1(sK0,sK1) | (~spl5_4 | ~spl5_5)),
% 0.22/0.48    inference(resolution,[],[f73,f65])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    v5_relat_1(sK1,sK0) | ~spl5_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f64])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    ( ! [X0] : (~v5_relat_1(sK1,X0) | sK1 = k8_relat_1(X0,sK1)) ) | ~spl5_5),
% 0.22/0.48    inference(resolution,[],[f72,f69])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    v1_relat_1(sK1) | ~spl5_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f68])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = X1 | ~v5_relat_1(X1,X0)) )),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f71])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(resolution,[],[f32,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(nnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    spl5_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f27,f68])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    v1_relat_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    (~r2_hidden(k1_funct_1(sK1,sK2),sK0) & r2_hidden(sK2,k1_relat_1(sK1))) & v1_funct_1(sK1) & v5_relat_1(sK1,sK0) & v1_relat_1(sK1)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f18,f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),X0) & r2_hidden(X2,k1_relat_1(X1))) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => (? [X2] : (~r2_hidden(k1_funct_1(sK1,X2),sK0) & r2_hidden(X2,k1_relat_1(sK1))) & v1_funct_1(sK1) & v5_relat_1(sK1,sK0) & v1_relat_1(sK1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ? [X2] : (~r2_hidden(k1_funct_1(sK1,X2),sK0) & r2_hidden(X2,k1_relat_1(sK1))) => (~r2_hidden(k1_funct_1(sK1,sK2),sK0) & r2_hidden(sK2,k1_relat_1(sK1)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),X0) & r2_hidden(X2,k1_relat_1(X1))) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),X0) & r2_hidden(X2,k1_relat_1(X1))) & (v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.22/0.48    inference(negated_conjecture,[],[f5])).
% 0.22/0.48  fof(f5,conjecture,(
% 0.22/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    spl5_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f28,f64])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    v5_relat_1(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    spl5_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f29,f60])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    v1_funct_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    spl5_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f30,f56])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    r2_hidden(sK2,k1_relat_1(sK1))),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ~spl5_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f31,f52])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ~r2_hidden(k1_funct_1(sK1,sK2),sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (23128)------------------------------
% 0.22/0.48  % (23128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (23128)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (23128)Memory used [KB]: 10618
% 0.22/0.48  % (23128)Time elapsed: 0.003 s
% 0.22/0.48  % (23128)------------------------------
% 0.22/0.48  % (23128)------------------------------
% 0.22/0.48  % (23118)Success in time 0.117 s
%------------------------------------------------------------------------------
