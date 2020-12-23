%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0620+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 176 expanded)
%              Number of leaves         :   14 (  55 expanded)
%              Depth                    :   25
%              Number of atoms          :  392 (1011 expanded)
%              Number of equality atoms :  171 ( 443 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f326,plain,(
    $false ),
    inference(subsumption_resolution,[],[f325,f31])).

fof(f31,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ! [X2] :
        ( k2_relat_1(X2) != k1_tarski(sK1)
        | k1_relat_1(X2) != sK0
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
          ! [X2] :
            ( k2_relat_1(X2) != k1_tarski(X1)
            | k1_relat_1(X2) != X0
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & k1_xboole_0 != X0 )
   => ( ? [X1] :
        ! [X2] :
          ( k2_relat_1(X2) != k1_tarski(X1)
          | k1_relat_1(X2) != sK0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
      ! [X2] :
        ( k2_relat_1(X2) != k1_tarski(X1)
        | k1_relat_1(X2) != sK0
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
   => ! [X2] :
        ( k2_relat_1(X2) != k1_tarski(sK1)
        | k1_relat_1(X2) != sK0
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
        ! [X2] :
          ( k2_relat_1(X2) != k1_tarski(X1)
          | k1_relat_1(X2) != X0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => ! [X1] :
          ? [X2] :
            ( k2_relat_1(X2) = k1_tarski(X1)
            & k1_relat_1(X2) = X0
            & v1_funct_1(X2)
            & v1_relat_1(X2) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f325,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f314,f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f314,plain,(
    v1_xboole_0(sK0) ),
    inference(resolution,[],[f283,f33])).

fof(f33,plain,(
    ! [X0] : m1_subset_1(o_1_0_funct_1(X0),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(o_1_0_funct_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_1_0_funct_1)).

fof(f283,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f255,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f255,plain,(
    ! [X1] : ~ r2_hidden(X1,sK0) ),
    inference(subsumption_resolution,[],[f254,f55])).

fof(f55,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f254,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(sK1,k1_tarski(sK1)) ) ),
    inference(trivial_inequality_removal,[],[f242])).

fof(f242,plain,(
    ! [X1] :
      ( sK1 != sK1
      | sK0 != sK0
      | ~ r2_hidden(X1,sK0)
      | k1_tarski(sK1) != k1_tarski(sK1)
      | ~ r2_hidden(sK1,k1_tarski(sK1)) ) ),
    inference(superposition,[],[f80,f215])).

fof(f215,plain,(
    sK1 = sK2(sK6(sK0,sK1),k1_tarski(sK1)) ),
    inference(equality_resolution,[],[f160])).

fof(f160,plain,(
    ! [X0] :
      ( sK1 != X0
      | sK1 = sK2(sK6(sK0,X0),k1_tarski(sK1)) ) ),
    inference(equality_factoring,[],[f137])).

fof(f137,plain,(
    ! [X2] :
      ( sK2(sK6(sK0,X2),k1_tarski(sK1)) = X2
      | sK1 = sK2(sK6(sK0,X2),k1_tarski(sK1)) ) ),
    inference(resolution,[],[f121,f56])).

fof(f56,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f121,plain,(
    ! [X1] :
      ( r2_hidden(sK2(sK6(sK0,X1),k1_tarski(sK1)),k1_tarski(sK1))
      | sK2(sK6(sK0,X1),k1_tarski(sK1)) = X1 ) ),
    inference(subsumption_resolution,[],[f116,f88])).

fof(f88,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK6(sK0,X0),k1_tarski(sK1)),k1_tarski(sK1))
      | r2_hidden(sK3(sK6(sK0,X0),k1_tarski(sK1)),sK0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | r2_hidden(sK3(sK6(X0,X1),k1_tarski(sK1)),X0)
      | r2_hidden(sK2(sK6(X0,X1),k1_tarski(sK1)),k1_tarski(sK1)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(sK1) != X2
      | sK0 != X0
      | r2_hidden(sK3(sK6(X0,X1),X2),X0)
      | r2_hidden(sK2(sK6(X0,X1),X2),X2) ) ),
    inference(subsumption_resolution,[],[f64,f46])).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK6(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK6(X0,X1)) = X0
      & v1_funct_1(sK6(X0,X1))
      & v1_relat_1(sK6(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f15,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK6(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK6(X0,X1)) = X0
        & v1_funct_1(sK6(X0,X1))
        & v1_relat_1(sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | k1_tarski(sK1) != X2
      | ~ v1_relat_1(sK6(X0,X1))
      | r2_hidden(sK3(sK6(X0,X1),X2),X0)
      | r2_hidden(sK2(sK6(X0,X1),X2),X2) ) ),
    inference(subsumption_resolution,[],[f63,f47])).

fof(f47,plain,(
    ! [X0,X1] : v1_funct_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | k1_tarski(sK1) != X2
      | ~ v1_funct_1(sK6(X0,X1))
      | ~ v1_relat_1(sK6(X0,X1))
      | r2_hidden(sK3(sK6(X0,X1),X2),X0)
      | r2_hidden(sK2(sK6(X0,X1),X2),X2) ) ),
    inference(superposition,[],[f62,f48])).

fof(f48,plain,(
    ! [X0,X1] : k1_relat_1(sK6(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f30])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != sK0
      | k1_tarski(sK1) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_tarski(sK1) != X1
      | k1_relat_1(X0) != sK0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK2(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f32,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK2(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK2(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ( sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f23,f22,f21])).

fof(f21,plain,(
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

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK2(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

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

fof(f32,plain,(
    ! [X2] :
      ( k2_relat_1(X2) != k1_tarski(sK1)
      | k1_relat_1(X2) != sK0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f116,plain,(
    ! [X1] :
      ( sK2(sK6(sK0,X1),k1_tarski(sK1)) = X1
      | r2_hidden(sK2(sK6(sK0,X1),k1_tarski(sK1)),k1_tarski(sK1))
      | ~ r2_hidden(sK3(sK6(sK0,X1),k1_tarski(sK1)),sK0) ) ),
    inference(superposition,[],[f93,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK6(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f93,plain,(
    ! [X0] :
      ( sK2(sK6(sK0,X0),k1_tarski(sK1)) = k1_funct_1(sK6(sK0,X0),sK3(sK6(sK0,X0),k1_tarski(sK1)))
      | r2_hidden(sK2(sK6(sK0,X0),k1_tarski(sK1)),k1_tarski(sK1)) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK2(sK6(X0,X1),k1_tarski(sK1)) = k1_funct_1(sK6(X0,X1),sK3(sK6(X0,X1),k1_tarski(sK1)))
      | r2_hidden(sK2(sK6(X0,X1),k1_tarski(sK1)),k1_tarski(sK1)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(sK1) != X2
      | sK0 != X0
      | sK2(sK6(X0,X1),X2) = k1_funct_1(sK6(X0,X1),sK3(sK6(X0,X1),X2))
      | r2_hidden(sK2(sK6(X0,X1),X2),X2) ) ),
    inference(subsumption_resolution,[],[f67,f46])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | k1_tarski(sK1) != X2
      | ~ v1_relat_1(sK6(X0,X1))
      | sK2(sK6(X0,X1),X2) = k1_funct_1(sK6(X0,X1),sK3(sK6(X0,X1),X2))
      | r2_hidden(sK2(sK6(X0,X1),X2),X2) ) ),
    inference(subsumption_resolution,[],[f66,f47])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | k1_tarski(sK1) != X2
      | ~ v1_funct_1(sK6(X0,X1))
      | ~ v1_relat_1(sK6(X0,X1))
      | sK2(sK6(X0,X1),X2) = k1_funct_1(sK6(X0,X1),sK3(sK6(X0,X1),X2))
      | r2_hidden(sK2(sK6(X0,X1),X2),X2) ) ),
    inference(superposition,[],[f61,f48])).

fof(f61,plain,(
    ! [X2,X3] :
      ( k1_relat_1(X2) != sK0
      | k1_tarski(sK1) != X3
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | sK2(X2,X3) = k1_funct_1(X2,sK3(X2,X3))
      | r2_hidden(sK2(X2,X3),X3) ) ),
    inference(duplicate_literal_removal,[],[f58])).

fof(f58,plain,(
    ! [X2,X3] :
      ( k1_tarski(sK1) != X3
      | k1_relat_1(X2) != sK0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | sK2(X2,X3) = k1_funct_1(X2,sK3(X2,X3))
      | r2_hidden(sK2(X2,X3),X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f32,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
      | r2_hidden(sK2(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f80,plain,(
    ! [X6,X8,X7,X9] :
      ( sK2(sK6(X6,X7),X9) != X7
      | sK0 != X6
      | ~ r2_hidden(X8,X6)
      | k1_tarski(sK1) != X9
      | ~ r2_hidden(sK2(sK6(X6,X7),X9),X9) ) ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r2_hidden(X8,X6)
      | sK0 != X6
      | sK2(sK6(X6,X7),X9) != X7
      | k1_tarski(sK1) != X9
      | ~ r2_hidden(sK2(sK6(X6,X7),X9),X9)
      | ~ r2_hidden(X8,X6) ) ),
    inference(forward_demodulation,[],[f78,f48])).

fof(f78,plain,(
    ! [X6,X8,X7,X9] :
      ( sK0 != X6
      | sK2(sK6(X6,X7),X9) != X7
      | k1_tarski(sK1) != X9
      | ~ r2_hidden(X8,k1_relat_1(sK6(X6,X7)))
      | ~ r2_hidden(sK2(sK6(X6,X7),X9),X9)
      | ~ r2_hidden(X8,X6) ) ),
    inference(forward_demodulation,[],[f77,f48])).

fof(f77,plain,(
    ! [X6,X8,X7,X9] :
      ( sK2(sK6(X6,X7),X9) != X7
      | sK0 != k1_relat_1(sK6(X6,X7))
      | k1_tarski(sK1) != X9
      | ~ r2_hidden(X8,k1_relat_1(sK6(X6,X7)))
      | ~ r2_hidden(sK2(sK6(X6,X7),X9),X9)
      | ~ r2_hidden(X8,X6) ) ),
    inference(subsumption_resolution,[],[f76,f46])).

fof(f76,plain,(
    ! [X6,X8,X7,X9] :
      ( sK2(sK6(X6,X7),X9) != X7
      | sK0 != k1_relat_1(sK6(X6,X7))
      | ~ v1_relat_1(sK6(X6,X7))
      | k1_tarski(sK1) != X9
      | ~ r2_hidden(X8,k1_relat_1(sK6(X6,X7)))
      | ~ r2_hidden(sK2(sK6(X6,X7),X9),X9)
      | ~ r2_hidden(X8,X6) ) ),
    inference(subsumption_resolution,[],[f71,f47])).

fof(f71,plain,(
    ! [X6,X8,X7,X9] :
      ( sK2(sK6(X6,X7),X9) != X7
      | sK0 != k1_relat_1(sK6(X6,X7))
      | ~ v1_funct_1(sK6(X6,X7))
      | ~ v1_relat_1(sK6(X6,X7))
      | k1_tarski(sK1) != X9
      | ~ r2_hidden(X8,k1_relat_1(sK6(X6,X7)))
      | ~ r2_hidden(sK2(sK6(X6,X7),X9),X9)
      | ~ r2_hidden(X8,X6) ) ),
    inference(superposition,[],[f60,f49])).

fof(f60,plain,(
    ! [X6,X4,X5] :
      ( k1_funct_1(X4,X6) != sK2(X4,X5)
      | sK0 != k1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k1_tarski(sK1) != X5
      | ~ r2_hidden(X6,k1_relat_1(X4))
      | ~ r2_hidden(sK2(X4,X5),X5) ) ),
    inference(duplicate_literal_removal,[],[f59])).

fof(f59,plain,(
    ! [X6,X4,X5] :
      ( k1_tarski(sK1) != X5
      | sK0 != k1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k1_funct_1(X4,X6) != sK2(X4,X5)
      | ~ r2_hidden(X6,k1_relat_1(X4))
      | ~ r2_hidden(sK2(X4,X5),X5)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f32,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | k1_funct_1(X0,X3) != sK2(X0,X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(sK2(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

%------------------------------------------------------------------------------
