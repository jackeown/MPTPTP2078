%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:16 EST 2020

% Result     : Theorem 1.17s
% Output     : Refutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :  118 (2820 expanded)
%              Number of leaves         :   13 ( 749 expanded)
%              Depth                    :   32
%              Number of atoms          :  551 (20400 expanded)
%              Number of equality atoms :  243 (10691 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1794,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1777,f1672])).

fof(f1672,plain,(
    r2_hidden(sK2,sK0) ),
    inference(trivial_inequality_removal,[],[f1657])).

fof(f1657,plain,
    ( sK1 != sK1
    | r2_hidden(sK2,sK0) ),
    inference(backward_demodulation,[],[f175,f1629])).

fof(f1629,plain,(
    sK1 = k6_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f1628,f719])).

fof(f719,plain,
    ( r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0)
    | sK1 = k6_relat_1(sK0) ),
    inference(equality_resolution,[],[f455])).

fof(f455,plain,(
    ! [X0] :
      ( sK0 != X0
      | k6_relat_1(X0) = sK1
      | r2_hidden(sK3(k6_relat_1(X0),sK1),X0) ) ),
    inference(subsumption_resolution,[],[f454,f45])).

fof(f45,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f454,plain,(
    ! [X0] :
      ( sK0 != X0
      | k6_relat_1(X0) = sK1
      | r2_hidden(sK3(k6_relat_1(X0),sK1),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f452,f46])).

fof(f46,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f452,plain,(
    ! [X0] :
      ( sK0 != X0
      | k6_relat_1(X0) = sK1
      | r2_hidden(sK3(k6_relat_1(X0),sK1),X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f451,f47])).

fof(f47,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f451,plain,(
    ! [X1] :
      ( k1_relat_1(X1) != sK0
      | sK1 = X1
      | r2_hidden(sK3(X1,sK1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f106,f127])).

fof(f127,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,
    ( sK0 = k1_relat_1(sK1)
    | sK0 = k1_relat_1(sK1) ),
    inference(superposition,[],[f47,f41])).

fof(f41,plain,
    ( sK1 = k6_relat_1(sK0)
    | sK0 = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ( sK2 != k1_funct_1(sK1,sK2)
        & r2_hidden(sK2,sK0) )
      | sK0 != k1_relat_1(sK1)
      | sK1 != k6_relat_1(sK0) )
    & ( ( ! [X3] :
            ( k1_funct_1(sK1,X3) = X3
            | ~ r2_hidden(X3,sK0) )
        & sK0 = k1_relat_1(sK1) )
      | sK1 = k6_relat_1(sK0) )
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f27,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ( ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0
          | k6_relat_1(X0) != X1 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) = X1 )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ? [X2] :
            ( k1_funct_1(sK1,X2) != X2
            & r2_hidden(X2,sK0) )
        | sK0 != k1_relat_1(sK1)
        | sK1 != k6_relat_1(sK0) )
      & ( ( ! [X3] :
              ( k1_funct_1(sK1,X3) = X3
              | ~ r2_hidden(X3,sK0) )
          & sK0 = k1_relat_1(sK1) )
        | sK1 = k6_relat_1(sK0) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( k1_funct_1(sK1,X2) != X2
        & r2_hidden(X2,sK0) )
   => ( sK2 != k1_funct_1(sK1,sK2)
      & r2_hidden(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( k1_funct_1(X1,X2) != X2
            & r2_hidden(X2,X0) )
        | k1_relat_1(X1) != X0
        | k6_relat_1(X0) != X1 )
      & ( ( ! [X3] :
              ( k1_funct_1(X1,X3) = X3
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X1) = X0 )
        | k6_relat_1(X0) = X1 )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( k1_funct_1(X1,X2) != X2
            & r2_hidden(X2,X0) )
        | k1_relat_1(X1) != X0
        | k6_relat_1(X0) != X1 )
      & ( ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 )
        | k6_relat_1(X0) = X1 )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( k1_funct_1(X1,X2) != X2
            & r2_hidden(X2,X0) )
        | k1_relat_1(X1) != X0
        | k6_relat_1(X0) != X1 )
      & ( ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 )
        | k6_relat_1(X0) = X1 )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <~> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <~> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k6_relat_1(X0) = X1
        <=> ( ! [X2] :
                ( r2_hidden(X2,X0)
               => k1_funct_1(X1,X2) = X2 )
            & k1_relat_1(X1) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f106,plain,(
    ! [X1] :
      ( sK1 = X1
      | r2_hidden(sK3(X1,sK1),k1_relat_1(X1))
      | k1_relat_1(X1) != k1_relat_1(sK1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f88,f39])).

fof(f39,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f88,plain,(
    ! [X1] :
      ( sK1 = X1
      | r2_hidden(sK3(X1,sK1),k1_relat_1(X1))
      | k1_relat_1(X1) != k1_relat_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f40,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
            & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f40,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f1628,plain,
    ( sK1 = k6_relat_1(sK0)
    | ~ r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f1627,f45])).

fof(f1627,plain,
    ( sK1 = k6_relat_1(sK0)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f1626,f46])).

fof(f1626,plain,
    ( sK1 = k6_relat_1(sK0)
    | ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f1601,f47])).

fof(f1601,plain,
    ( sK0 != k1_relat_1(k6_relat_1(sK0))
    | sK1 = k6_relat_1(sK0)
    | ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f1600])).

fof(f1600,plain,
    ( sK3(k6_relat_1(sK0),sK1) != sK3(k6_relat_1(sK0),sK1)
    | sK0 != k1_relat_1(k6_relat_1(sK0))
    | sK1 = k6_relat_1(sK0)
    | ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0) ),
    inference(duplicate_literal_removal,[],[f1591])).

fof(f1591,plain,
    ( sK3(k6_relat_1(sK0),sK1) != sK3(k6_relat_1(sK0),sK1)
    | sK0 != k1_relat_1(k6_relat_1(sK0))
    | sK1 = k6_relat_1(sK0)
    | ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0)
    | sK1 = k6_relat_1(sK0)
    | ~ r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0) ),
    inference(superposition,[],[f812,f1351])).

fof(f1351,plain,(
    ! [X4] :
      ( k1_funct_1(k6_relat_1(sK0),X4) = X4
      | ~ r2_hidden(X4,sK0) ) ),
    inference(forward_demodulation,[],[f1338,f1272])).

fof(f1272,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(duplicate_literal_removal,[],[f1269])).

fof(f1269,plain,
    ( sK0 = k2_relat_1(sK1)
    | sK0 = k2_relat_1(sK1) ),
    inference(superposition,[],[f48,f1172])).

fof(f1172,plain,
    ( sK1 = k6_relat_1(sK0)
    | sK0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f1153,f775])).

fof(f775,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK1,X0),sK0)
      | k2_relat_1(sK1) = X0
      | ~ r2_hidden(sK4(sK1,X0),X0)
      | sK1 = k6_relat_1(sK0) ) ),
    inference(equality_resolution,[],[f774])).

fof(f774,plain,(
    ! [X6,X5] :
      ( sK4(sK1,X6) != X5
      | ~ r2_hidden(X5,sK0)
      | k2_relat_1(sK1) = X6
      | ~ r2_hidden(sK4(sK1,X6),X6)
      | sK1 = k6_relat_1(sK0) ) ),
    inference(duplicate_literal_removal,[],[f773])).

fof(f773,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,sK0)
      | sK4(sK1,X6) != X5
      | k2_relat_1(sK1) = X6
      | ~ r2_hidden(sK4(sK1,X6),X6)
      | ~ r2_hidden(X5,sK0)
      | sK1 = k6_relat_1(sK0) ) ),
    inference(forward_demodulation,[],[f150,f127])).

fof(f150,plain,(
    ! [X6,X5] :
      ( sK4(sK1,X6) != X5
      | k2_relat_1(sK1) = X6
      | ~ r2_hidden(X5,k1_relat_1(sK1))
      | ~ r2_hidden(sK4(sK1,X6),X6)
      | ~ r2_hidden(X5,sK0)
      | sK1 = k6_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f149,f39])).

fof(f149,plain,(
    ! [X6,X5] :
      ( sK4(sK1,X6) != X5
      | k2_relat_1(sK1) = X6
      | ~ r2_hidden(X5,k1_relat_1(sK1))
      | ~ r2_hidden(sK4(sK1,X6),X6)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X5,sK0)
      | sK1 = k6_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f134,f40])).

fof(f134,plain,(
    ! [X6,X5] :
      ( sK4(sK1,X6) != X5
      | k2_relat_1(sK1) = X6
      | ~ r2_hidden(X5,k1_relat_1(sK1))
      | ~ r2_hidden(sK4(sK1,X6),X6)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X5,sK0)
      | sK1 = k6_relat_1(sK0) ) ),
    inference(superposition,[],[f58,f42])).

fof(f42,plain,(
    ! [X3] :
      ( k1_funct_1(sK1,X3) = X3
      | ~ r2_hidden(X3,sK0)
      | sK1 = k6_relat_1(sK0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | k1_funct_1(X0,X3) != sK4(X0,X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(sK4(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK4(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
                  & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X5)) = X5
                    & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f32,f35,f34,f33])).

fof(f33,plain,(
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
              ( k1_funct_1(X0,X3) != sK4(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK4(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK4(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f1153,plain,
    ( r2_hidden(sK4(sK1,sK0),sK0)
    | sK0 = k2_relat_1(sK1)
    | sK1 = k6_relat_1(sK0) ),
    inference(factoring,[],[f727])).

fof(f727,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK1,X1),sK0)
      | k2_relat_1(sK1) = X1
      | r2_hidden(sK4(sK1,X1),X1)
      | sK1 = k6_relat_1(sK0) ) ),
    inference(duplicate_literal_removal,[],[f722])).

fof(f722,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK1,X1),sK0)
      | k2_relat_1(sK1) = X1
      | r2_hidden(sK4(sK1,X1),X1)
      | sK1 = k6_relat_1(sK0)
      | k2_relat_1(sK1) = X1
      | r2_hidden(sK4(sK1,X1),X1) ) ),
    inference(superposition,[],[f366,f720])).

fof(f720,plain,(
    ! [X1] :
      ( sK5(sK1,X1) = sK4(sK1,X1)
      | sK1 = k6_relat_1(sK0)
      | k2_relat_1(sK1) = X1
      | r2_hidden(sK4(sK1,X1),X1) ) ),
    inference(subsumption_resolution,[],[f140,f366])).

fof(f140,plain,(
    ! [X1] :
      ( sK5(sK1,X1) = sK4(sK1,X1)
      | ~ r2_hidden(sK5(sK1,X1),sK0)
      | sK1 = k6_relat_1(sK0)
      | k2_relat_1(sK1) = X1
      | r2_hidden(sK4(sK1,X1),X1) ) ),
    inference(subsumption_resolution,[],[f139,f39])).

fof(f139,plain,(
    ! [X1] :
      ( sK5(sK1,X1) = sK4(sK1,X1)
      | ~ r2_hidden(sK5(sK1,X1),sK0)
      | sK1 = k6_relat_1(sK0)
      | k2_relat_1(sK1) = X1
      | r2_hidden(sK4(sK1,X1),X1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f129,f40])).

fof(f129,plain,(
    ! [X1] :
      ( sK5(sK1,X1) = sK4(sK1,X1)
      | ~ r2_hidden(sK5(sK1,X1),sK0)
      | sK1 = k6_relat_1(sK0)
      | k2_relat_1(sK1) = X1
      | r2_hidden(sK4(sK1,X1),X1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f42,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
      | r2_hidden(sK4(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f366,plain,(
    ! [X4] :
      ( r2_hidden(sK5(sK1,X4),sK0)
      | k2_relat_1(sK1) = X4
      | r2_hidden(sK4(sK1,X4),X4) ) ),
    inference(forward_demodulation,[],[f109,f127])).

fof(f109,plain,(
    ! [X4] :
      ( k2_relat_1(sK1) = X4
      | r2_hidden(sK5(sK1,X4),k1_relat_1(sK1))
      | r2_hidden(sK4(sK1,X4),X4) ) ),
    inference(subsumption_resolution,[],[f91,f39])).

fof(f91,plain,(
    ! [X4] :
      ( k2_relat_1(sK1) = X4
      | r2_hidden(sK5(sK1,X4),k1_relat_1(sK1))
      | r2_hidden(sK4(sK1,X4),X4)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f40,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK4(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f48,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1338,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(k6_relat_1(k2_relat_1(sK1)),X4) = X4 ) ),
    inference(backward_demodulation,[],[f884,f1272])).

fof(f884,plain,(
    ! [X4] :
      ( k1_funct_1(k6_relat_1(k2_relat_1(sK1)),X4) = X4
      | ~ r2_hidden(X4,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f866,f290])).

fof(f290,plain,(
    ! [X26] :
      ( r2_hidden(sK6(sK1,X26),sK0)
      | ~ r2_hidden(X26,k2_relat_1(sK1)) ) ),
    inference(forward_demodulation,[],[f122,f127])).

fof(f122,plain,(
    ! [X26] :
      ( r2_hidden(sK6(sK1,X26),k1_relat_1(sK1))
      | ~ r2_hidden(X26,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f104,f39])).

fof(f104,plain,(
    ! [X26] :
      ( r2_hidden(sK6(sK1,X26),k1_relat_1(sK1))
      | ~ r2_hidden(X26,k2_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f40,f66])).

fof(f66,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f866,plain,(
    ! [X4] :
      ( k1_funct_1(k6_relat_1(k2_relat_1(sK1)),X4) = X4
      | ~ r2_hidden(sK6(sK1,X4),sK0)
      | ~ r2_hidden(X4,k2_relat_1(sK1)) ) ),
    inference(superposition,[],[f263,f121])).

fof(f121,plain,(
    ! [X25] :
      ( k1_funct_1(sK1,sK6(sK1,X25)) = X25
      | ~ r2_hidden(X25,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f103,f39])).

fof(f103,plain,(
    ! [X25] :
      ( k1_funct_1(sK1,sK6(sK1,X25)) = X25
      | ~ r2_hidden(X25,k2_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f40,f65])).

fof(f65,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f263,plain,(
    ! [X3] :
      ( k1_funct_1(sK1,X3) = k1_funct_1(k6_relat_1(k2_relat_1(sK1)),k1_funct_1(sK1,X3))
      | ~ r2_hidden(X3,sK0) ) ),
    inference(forward_demodulation,[],[f262,f127])).

fof(f262,plain,(
    ! [X3] :
      ( k1_funct_1(sK1,X3) = k1_funct_1(k6_relat_1(k2_relat_1(sK1)),k1_funct_1(sK1,X3))
      | ~ r2_hidden(X3,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f261,f39])).

fof(f261,plain,(
    ! [X3] :
      ( k1_funct_1(sK1,X3) = k1_funct_1(k6_relat_1(k2_relat_1(sK1)),k1_funct_1(sK1,X3))
      | ~ r2_hidden(X3,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f260,f40])).

fof(f260,plain,(
    ! [X3] :
      ( k1_funct_1(sK1,X3) = k1_funct_1(k6_relat_1(k2_relat_1(sK1)),k1_funct_1(sK1,X3))
      | ~ r2_hidden(X3,k1_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f259,f45])).

fof(f259,plain,(
    ! [X3] :
      ( k1_funct_1(sK1,X3) = k1_funct_1(k6_relat_1(k2_relat_1(sK1)),k1_funct_1(sK1,X3))
      | ~ r2_hidden(X3,k1_relat_1(sK1))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(sK1)))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f244,f46])).

fof(f244,plain,(
    ! [X3] :
      ( k1_funct_1(sK1,X3) = k1_funct_1(k6_relat_1(k2_relat_1(sK1)),k1_funct_1(sK1,X3))
      | ~ r2_hidden(X3,k1_relat_1(sK1))
      | ~ v1_funct_1(k6_relat_1(k2_relat_1(sK1)))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(sK1)))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f59,f67])).

fof(f67,plain,(
    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) ),
    inference(resolution,[],[f39,f49])).

fof(f49,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f812,plain,(
    ! [X8] :
      ( sK3(X8,sK1) != k1_funct_1(X8,sK3(X8,sK1))
      | sK0 != k1_relat_1(X8)
      | sK1 = X8
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(X8)
      | ~ r2_hidden(sK3(X8,sK1),sK0)
      | sK1 = k6_relat_1(sK0) ) ),
    inference(forward_demodulation,[],[f154,f127])).

fof(f154,plain,(
    ! [X8] :
      ( sK3(X8,sK1) != k1_funct_1(X8,sK3(X8,sK1))
      | sK1 = X8
      | k1_relat_1(sK1) != k1_relat_1(X8)
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(X8)
      | ~ r2_hidden(sK3(X8,sK1),sK0)
      | sK1 = k6_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f153,f39])).

fof(f153,plain,(
    ! [X8] :
      ( sK3(X8,sK1) != k1_funct_1(X8,sK3(X8,sK1))
      | sK1 = X8
      | k1_relat_1(sK1) != k1_relat_1(X8)
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(X8)
      | ~ r2_hidden(sK3(X8,sK1),sK0)
      | sK1 = k6_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f136,f40])).

fof(f136,plain,(
    ! [X8] :
      ( sK3(X8,sK1) != k1_funct_1(X8,sK3(X8,sK1))
      | sK1 = X8
      | k1_relat_1(sK1) != k1_relat_1(X8)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(X8)
      | ~ r2_hidden(sK3(X8,sK1),sK0)
      | sK1 = k6_relat_1(sK0) ) ),
    inference(superposition,[],[f52,f42])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f175,plain,
    ( sK1 != k6_relat_1(sK0)
    | r2_hidden(sK2,sK0) ),
    inference(trivial_inequality_removal,[],[f159])).

fof(f159,plain,
    ( sK0 != sK0
    | sK1 != k6_relat_1(sK0)
    | r2_hidden(sK2,sK0) ),
    inference(backward_demodulation,[],[f43,f127])).

fof(f43,plain,
    ( sK1 != k6_relat_1(sK0)
    | sK0 != k1_relat_1(sK1)
    | r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f1777,plain,(
    ~ r2_hidden(sK2,sK0) ),
    inference(trivial_inequality_removal,[],[f1761])).

fof(f1761,plain,
    ( sK2 != sK2
    | ~ r2_hidden(sK2,sK0) ),
    inference(superposition,[],[f1671,f1664])).

fof(f1664,plain,(
    ! [X4] :
      ( k1_funct_1(sK1,X4) = X4
      | ~ r2_hidden(X4,sK0) ) ),
    inference(backward_demodulation,[],[f1351,f1629])).

fof(f1671,plain,(
    sK2 != k1_funct_1(sK1,sK2) ),
    inference(trivial_inequality_removal,[],[f1659])).

fof(f1659,plain,
    ( sK1 != sK1
    | sK2 != k1_funct_1(sK1,sK2) ),
    inference(backward_demodulation,[],[f207,f1629])).

fof(f207,plain,
    ( sK2 != k1_funct_1(sK1,sK2)
    | sK1 != k6_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f44,f127])).

fof(f44,plain,
    ( sK2 != k1_funct_1(sK1,sK2)
    | sK0 != k1_relat_1(sK1)
    | sK1 != k6_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:58:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.36  ipcrm: permission denied for id (827392002)
% 0.12/0.36  ipcrm: permission denied for id (821264387)
% 0.12/0.36  ipcrm: permission denied for id (825196548)
% 0.12/0.36  ipcrm: permission denied for id (825229317)
% 0.12/0.36  ipcrm: permission denied for id (821329926)
% 0.12/0.36  ipcrm: permission denied for id (827424775)
% 0.12/0.36  ipcrm: permission denied for id (821395464)
% 0.12/0.37  ipcrm: permission denied for id (821461001)
% 0.12/0.37  ipcrm: permission denied for id (821493770)
% 0.12/0.37  ipcrm: permission denied for id (825327628)
% 0.12/0.37  ipcrm: permission denied for id (821559309)
% 0.12/0.37  ipcrm: permission denied for id (821592078)
% 0.12/0.37  ipcrm: permission denied for id (821624847)
% 0.12/0.37  ipcrm: permission denied for id (821657616)
% 0.12/0.38  ipcrm: permission denied for id (821690385)
% 0.12/0.38  ipcrm: permission denied for id (821723154)
% 0.12/0.38  ipcrm: permission denied for id (821755924)
% 0.12/0.38  ipcrm: permission denied for id (821788693)
% 0.12/0.38  ipcrm: permission denied for id (825425943)
% 0.12/0.38  ipcrm: permission denied for id (825458712)
% 0.12/0.38  ipcrm: permission denied for id (827555865)
% 0.12/0.39  ipcrm: permission denied for id (827621403)
% 0.12/0.39  ipcrm: permission denied for id (821985308)
% 0.12/0.39  ipcrm: permission denied for id (827654173)
% 0.12/0.39  ipcrm: permission denied for id (822050847)
% 0.12/0.39  ipcrm: permission denied for id (822083616)
% 0.12/0.39  ipcrm: permission denied for id (825655329)
% 0.12/0.40  ipcrm: permission denied for id (825688098)
% 0.19/0.40  ipcrm: permission denied for id (827719715)
% 0.19/0.40  ipcrm: permission denied for id (822181924)
% 0.19/0.40  ipcrm: permission denied for id (822214693)
% 0.19/0.40  ipcrm: permission denied for id (827752486)
% 0.19/0.40  ipcrm: permission denied for id (822280231)
% 0.19/0.40  ipcrm: permission denied for id (827785256)
% 0.19/0.40  ipcrm: permission denied for id (822345769)
% 0.19/0.41  ipcrm: permission denied for id (822411307)
% 0.19/0.41  ipcrm: permission denied for id (827850796)
% 0.19/0.41  ipcrm: permission denied for id (822476845)
% 0.19/0.41  ipcrm: permission denied for id (825884718)
% 0.19/0.41  ipcrm: permission denied for id (825917487)
% 0.19/0.41  ipcrm: permission denied for id (822575152)
% 0.19/0.41  ipcrm: permission denied for id (827883569)
% 0.19/0.41  ipcrm: permission denied for id (822673458)
% 0.19/0.42  ipcrm: permission denied for id (825983027)
% 0.19/0.42  ipcrm: permission denied for id (827916340)
% 0.19/0.42  ipcrm: permission denied for id (822771765)
% 0.19/0.42  ipcrm: permission denied for id (822804534)
% 0.19/0.42  ipcrm: permission denied for id (822870072)
% 0.19/0.42  ipcrm: permission denied for id (828014649)
% 0.19/0.42  ipcrm: permission denied for id (828047418)
% 0.19/0.42  ipcrm: permission denied for id (826179643)
% 0.19/0.43  ipcrm: permission denied for id (826212412)
% 0.19/0.43  ipcrm: permission denied for id (822968381)
% 0.19/0.43  ipcrm: permission denied for id (826245182)
% 0.19/0.43  ipcrm: permission denied for id (823033919)
% 0.19/0.43  ipcrm: permission denied for id (826277952)
% 0.19/0.43  ipcrm: permission denied for id (823099458)
% 0.19/0.43  ipcrm: permission denied for id (823132227)
% 0.19/0.44  ipcrm: permission denied for id (823164996)
% 0.19/0.44  ipcrm: permission denied for id (826343493)
% 0.19/0.44  ipcrm: permission denied for id (823230534)
% 0.19/0.44  ipcrm: permission denied for id (823263303)
% 0.19/0.44  ipcrm: permission denied for id (828178504)
% 0.19/0.44  ipcrm: permission denied for id (826409033)
% 0.19/0.44  ipcrm: permission denied for id (823394379)
% 0.19/0.45  ipcrm: permission denied for id (828211276)
% 0.19/0.45  ipcrm: permission denied for id (826507341)
% 0.19/0.45  ipcrm: permission denied for id (828244046)
% 0.19/0.45  ipcrm: permission denied for id (826572879)
% 0.19/0.45  ipcrm: permission denied for id (826605648)
% 0.19/0.45  ipcrm: permission denied for id (823623761)
% 0.19/0.45  ipcrm: permission denied for id (823656530)
% 0.19/0.45  ipcrm: permission denied for id (823689299)
% 0.19/0.46  ipcrm: permission denied for id (823722068)
% 0.19/0.46  ipcrm: permission denied for id (823754837)
% 0.19/0.46  ipcrm: permission denied for id (826638422)
% 0.19/0.46  ipcrm: permission denied for id (823820375)
% 0.19/0.46  ipcrm: permission denied for id (828276824)
% 0.19/0.46  ipcrm: permission denied for id (823853145)
% 0.19/0.46  ipcrm: permission denied for id (823885914)
% 0.19/0.46  ipcrm: permission denied for id (823918683)
% 0.19/0.47  ipcrm: permission denied for id (823951452)
% 0.19/0.47  ipcrm: permission denied for id (823984221)
% 0.19/0.47  ipcrm: permission denied for id (828309598)
% 0.19/0.47  ipcrm: permission denied for id (828342367)
% 0.19/0.47  ipcrm: permission denied for id (824082528)
% 0.19/0.47  ipcrm: permission denied for id (824115297)
% 0.19/0.47  ipcrm: permission denied for id (824148066)
% 0.19/0.47  ipcrm: permission denied for id (826769507)
% 0.19/0.48  ipcrm: permission denied for id (824213604)
% 0.19/0.48  ipcrm: permission denied for id (828375141)
% 0.19/0.48  ipcrm: permission denied for id (824279142)
% 0.19/0.48  ipcrm: permission denied for id (824311911)
% 0.19/0.48  ipcrm: permission denied for id (826867817)
% 0.19/0.48  ipcrm: permission denied for id (824410218)
% 0.19/0.48  ipcrm: permission denied for id (824442987)
% 0.19/0.49  ipcrm: permission denied for id (826900588)
% 0.19/0.49  ipcrm: permission denied for id (828440685)
% 0.19/0.49  ipcrm: permission denied for id (828473454)
% 0.19/0.49  ipcrm: permission denied for id (824541295)
% 0.19/0.49  ipcrm: permission denied for id (828506224)
% 0.19/0.49  ipcrm: permission denied for id (827031665)
% 0.19/0.49  ipcrm: permission denied for id (824639602)
% 0.19/0.49  ipcrm: permission denied for id (828538995)
% 0.19/0.50  ipcrm: permission denied for id (824737908)
% 0.19/0.50  ipcrm: permission denied for id (827097205)
% 0.19/0.50  ipcrm: permission denied for id (827129974)
% 0.19/0.50  ipcrm: permission denied for id (828604536)
% 0.19/0.50  ipcrm: permission denied for id (824868985)
% 0.19/0.50  ipcrm: permission denied for id (824901754)
% 0.19/0.50  ipcrm: permission denied for id (824934523)
% 0.19/0.51  ipcrm: permission denied for id (824967292)
% 0.19/0.51  ipcrm: permission denied for id (827228285)
% 0.19/0.51  ipcrm: permission denied for id (828637310)
% 0.19/0.51  ipcrm: permission denied for id (825065599)
% 0.83/0.61  % (13330)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.06/0.63  % (13338)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.06/0.63  % (13321)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.06/0.63  % (13319)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.06/0.63  % (13319)Refutation not found, incomplete strategy% (13319)------------------------------
% 1.06/0.63  % (13319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.06/0.63  % (13319)Termination reason: Refutation not found, incomplete strategy
% 1.06/0.63  
% 1.06/0.63  % (13319)Memory used [KB]: 10618
% 1.06/0.63  % (13319)Time elapsed: 0.064 s
% 1.06/0.63  % (13319)------------------------------
% 1.06/0.63  % (13319)------------------------------
% 1.06/0.63  % (13320)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.17/0.64  % (13322)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.17/0.65  % (13328)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.17/0.65  % (13336)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.17/0.65  % (13327)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.17/0.66  % (13333)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.17/0.66  % (13325)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.17/0.66  % (13337)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.17/0.66  % (13339)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.17/0.66  % (13331)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.17/0.66  % (13324)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.17/0.66  % (13331)Refutation not found, incomplete strategy% (13331)------------------------------
% 1.17/0.66  % (13331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.67  % (13323)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.17/0.67  % (13346)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.17/0.67  % (13335)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.17/0.67  % (13345)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.17/0.67  % (13343)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.17/0.67  % (13341)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.17/0.68  % (13326)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.17/0.68  % (13342)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.17/0.68  % (13331)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.68  
% 1.17/0.68  % (13331)Memory used [KB]: 10618
% 1.17/0.68  % (13331)Time elapsed: 0.101 s
% 1.17/0.68  % (13331)------------------------------
% 1.17/0.68  % (13331)------------------------------
% 1.17/0.68  % (13332)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.17/0.68  % (13333)Refutation not found, incomplete strategy% (13333)------------------------------
% 1.17/0.68  % (13333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.68  % (13333)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.68  
% 1.17/0.68  % (13333)Memory used [KB]: 6140
% 1.17/0.68  % (13333)Time elapsed: 0.111 s
% 1.17/0.68  % (13333)------------------------------
% 1.17/0.68  % (13333)------------------------------
% 1.17/0.68  % (13340)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.17/0.69  % (13326)Refutation not found, incomplete strategy% (13326)------------------------------
% 1.17/0.69  % (13326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.69  % (13326)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.69  
% 1.17/0.69  % (13326)Memory used [KB]: 1663
% 1.17/0.69  % (13326)Time elapsed: 0.091 s
% 1.17/0.69  % (13326)------------------------------
% 1.17/0.69  % (13326)------------------------------
% 1.17/0.69  % (13325)Refutation not found, incomplete strategy% (13325)------------------------------
% 1.17/0.69  % (13325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.69  % (13338)Refutation found. Thanks to Tanya!
% 1.17/0.69  % SZS status Theorem for theBenchmark
% 1.17/0.70  % (13325)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.70  
% 1.17/0.70  % (13325)Memory used [KB]: 10746
% 1.17/0.70  % (13325)Time elapsed: 0.130 s
% 1.17/0.70  % (13325)------------------------------
% 1.17/0.70  % (13325)------------------------------
% 1.17/0.70  % (13334)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.17/0.71  % SZS output start Proof for theBenchmark
% 1.17/0.71  fof(f1794,plain,(
% 1.17/0.71    $false),
% 1.17/0.71    inference(subsumption_resolution,[],[f1777,f1672])).
% 1.17/0.71  fof(f1672,plain,(
% 1.17/0.71    r2_hidden(sK2,sK0)),
% 1.17/0.71    inference(trivial_inequality_removal,[],[f1657])).
% 1.17/0.71  fof(f1657,plain,(
% 1.17/0.71    sK1 != sK1 | r2_hidden(sK2,sK0)),
% 1.17/0.71    inference(backward_demodulation,[],[f175,f1629])).
% 1.17/0.71  fof(f1629,plain,(
% 1.17/0.71    sK1 = k6_relat_1(sK0)),
% 1.17/0.71    inference(subsumption_resolution,[],[f1628,f719])).
% 1.17/0.71  fof(f719,plain,(
% 1.17/0.71    r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0) | sK1 = k6_relat_1(sK0)),
% 1.17/0.71    inference(equality_resolution,[],[f455])).
% 1.17/0.71  fof(f455,plain,(
% 1.17/0.71    ( ! [X0] : (sK0 != X0 | k6_relat_1(X0) = sK1 | r2_hidden(sK3(k6_relat_1(X0),sK1),X0)) )),
% 1.17/0.71    inference(subsumption_resolution,[],[f454,f45])).
% 1.17/0.71  fof(f45,plain,(
% 1.17/0.71    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.17/0.71    inference(cnf_transformation,[],[f5])).
% 1.17/0.71  fof(f5,axiom,(
% 1.17/0.71    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.17/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.17/0.71  fof(f454,plain,(
% 1.17/0.71    ( ! [X0] : (sK0 != X0 | k6_relat_1(X0) = sK1 | r2_hidden(sK3(k6_relat_1(X0),sK1),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.17/0.71    inference(subsumption_resolution,[],[f452,f46])).
% 1.17/0.71  fof(f46,plain,(
% 1.17/0.71    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.17/0.71    inference(cnf_transformation,[],[f5])).
% 1.17/0.71  fof(f452,plain,(
% 1.17/0.71    ( ! [X0] : (sK0 != X0 | k6_relat_1(X0) = sK1 | r2_hidden(sK3(k6_relat_1(X0),sK1),X0) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.17/0.71    inference(superposition,[],[f451,f47])).
% 1.17/0.71  fof(f47,plain,(
% 1.17/0.71    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.17/0.71    inference(cnf_transformation,[],[f1])).
% 1.17/0.71  fof(f1,axiom,(
% 1.17/0.71    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.17/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.17/0.71  fof(f451,plain,(
% 1.17/0.71    ( ! [X1] : (k1_relat_1(X1) != sK0 | sK1 = X1 | r2_hidden(sK3(X1,sK1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.17/0.71    inference(forward_demodulation,[],[f106,f127])).
% 1.17/0.71  fof(f127,plain,(
% 1.17/0.71    sK0 = k1_relat_1(sK1)),
% 1.17/0.71    inference(duplicate_literal_removal,[],[f123])).
% 1.17/0.71  fof(f123,plain,(
% 1.17/0.71    sK0 = k1_relat_1(sK1) | sK0 = k1_relat_1(sK1)),
% 1.17/0.71    inference(superposition,[],[f47,f41])).
% 1.17/0.71  fof(f41,plain,(
% 1.17/0.71    sK1 = k6_relat_1(sK0) | sK0 = k1_relat_1(sK1)),
% 1.17/0.71    inference(cnf_transformation,[],[f28])).
% 1.17/0.71  fof(f28,plain,(
% 1.17/0.71    ((sK2 != k1_funct_1(sK1,sK2) & r2_hidden(sK2,sK0)) | sK0 != k1_relat_1(sK1) | sK1 != k6_relat_1(sK0)) & ((! [X3] : (k1_funct_1(sK1,X3) = X3 | ~r2_hidden(X3,sK0)) & sK0 = k1_relat_1(sK1)) | sK1 = k6_relat_1(sK0)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.17/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f27,f26])).
% 1.17/0.71  fof(f26,plain,(
% 1.17/0.71    ? [X0,X1] : ((? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0 | k6_relat_1(X0) != X1) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) = X1) & v1_funct_1(X1) & v1_relat_1(X1)) => ((? [X2] : (k1_funct_1(sK1,X2) != X2 & r2_hidden(X2,sK0)) | sK0 != k1_relat_1(sK1) | sK1 != k6_relat_1(sK0)) & ((! [X3] : (k1_funct_1(sK1,X3) = X3 | ~r2_hidden(X3,sK0)) & sK0 = k1_relat_1(sK1)) | sK1 = k6_relat_1(sK0)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.17/0.71    introduced(choice_axiom,[])).
% 1.17/0.71  fof(f27,plain,(
% 1.17/0.71    ? [X2] : (k1_funct_1(sK1,X2) != X2 & r2_hidden(X2,sK0)) => (sK2 != k1_funct_1(sK1,sK2) & r2_hidden(sK2,sK0))),
% 1.17/0.71    introduced(choice_axiom,[])).
% 1.17/0.71  fof(f25,plain,(
% 1.17/0.71    ? [X0,X1] : ((? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0 | k6_relat_1(X0) != X1) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) = X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.17/0.71    inference(rectify,[],[f24])).
% 1.17/0.71  fof(f24,plain,(
% 1.17/0.71    ? [X0,X1] : ((? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0 | k6_relat_1(X0) != X1) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) = X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.17/0.71    inference(flattening,[],[f23])).
% 1.17/0.71  fof(f23,plain,(
% 1.17/0.71    ? [X0,X1] : ((((? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) | k6_relat_1(X0) != X1) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) = X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.17/0.71    inference(nnf_transformation,[],[f12])).
% 1.17/0.71  fof(f12,plain,(
% 1.17/0.71    ? [X0,X1] : ((k6_relat_1(X0) = X1 <~> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.17/0.71    inference(flattening,[],[f11])).
% 1.17/0.71  fof(f11,plain,(
% 1.17/0.71    ? [X0,X1] : ((k6_relat_1(X0) = X1 <~> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.17/0.71    inference(ennf_transformation,[],[f10])).
% 1.17/0.71  fof(f10,negated_conjecture,(
% 1.17/0.71    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 1.17/0.71    inference(negated_conjecture,[],[f9])).
% 1.17/0.71  fof(f9,conjecture,(
% 1.17/0.71    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 1.17/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 1.17/0.71  fof(f106,plain,(
% 1.17/0.71    ( ! [X1] : (sK1 = X1 | r2_hidden(sK3(X1,sK1),k1_relat_1(X1)) | k1_relat_1(X1) != k1_relat_1(sK1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.17/0.71    inference(subsumption_resolution,[],[f88,f39])).
% 1.17/0.71  fof(f39,plain,(
% 1.17/0.71    v1_relat_1(sK1)),
% 1.17/0.71    inference(cnf_transformation,[],[f28])).
% 1.17/0.71  fof(f88,plain,(
% 1.17/0.71    ( ! [X1] : (sK1 = X1 | r2_hidden(sK3(X1,sK1),k1_relat_1(X1)) | k1_relat_1(X1) != k1_relat_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.17/0.71    inference(resolution,[],[f40,f51])).
% 1.17/0.71  fof(f51,plain,(
% 1.17/0.71    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.17/0.71    inference(cnf_transformation,[],[f30])).
% 1.17/0.71  fof(f30,plain,(
% 1.17/0.71    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.17/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f29])).
% 1.17/0.71  fof(f29,plain,(
% 1.17/0.71    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))),
% 1.17/0.71    introduced(choice_axiom,[])).
% 1.17/0.71  fof(f16,plain,(
% 1.17/0.71    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.17/0.71    inference(flattening,[],[f15])).
% 1.17/0.71  fof(f15,plain,(
% 1.17/0.71    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.17/0.71    inference(ennf_transformation,[],[f8])).
% 1.17/0.71  fof(f8,axiom,(
% 1.17/0.71    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.17/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 1.17/0.71  fof(f40,plain,(
% 1.17/0.71    v1_funct_1(sK1)),
% 1.17/0.71    inference(cnf_transformation,[],[f28])).
% 1.17/0.71  fof(f1628,plain,(
% 1.17/0.71    sK1 = k6_relat_1(sK0) | ~r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0)),
% 1.17/0.71    inference(subsumption_resolution,[],[f1627,f45])).
% 1.17/0.71  fof(f1627,plain,(
% 1.17/0.71    sK1 = k6_relat_1(sK0) | ~v1_relat_1(k6_relat_1(sK0)) | ~r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0)),
% 1.17/0.71    inference(subsumption_resolution,[],[f1626,f46])).
% 1.17/0.71  fof(f1626,plain,(
% 1.17/0.71    sK1 = k6_relat_1(sK0) | ~v1_funct_1(k6_relat_1(sK0)) | ~v1_relat_1(k6_relat_1(sK0)) | ~r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0)),
% 1.17/0.71    inference(subsumption_resolution,[],[f1601,f47])).
% 1.17/0.71  fof(f1601,plain,(
% 1.17/0.71    sK0 != k1_relat_1(k6_relat_1(sK0)) | sK1 = k6_relat_1(sK0) | ~v1_funct_1(k6_relat_1(sK0)) | ~v1_relat_1(k6_relat_1(sK0)) | ~r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0)),
% 1.17/0.71    inference(trivial_inequality_removal,[],[f1600])).
% 1.17/0.71  fof(f1600,plain,(
% 1.17/0.71    sK3(k6_relat_1(sK0),sK1) != sK3(k6_relat_1(sK0),sK1) | sK0 != k1_relat_1(k6_relat_1(sK0)) | sK1 = k6_relat_1(sK0) | ~v1_funct_1(k6_relat_1(sK0)) | ~v1_relat_1(k6_relat_1(sK0)) | ~r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0)),
% 1.17/0.71    inference(duplicate_literal_removal,[],[f1591])).
% 1.17/0.71  fof(f1591,plain,(
% 1.17/0.71    sK3(k6_relat_1(sK0),sK1) != sK3(k6_relat_1(sK0),sK1) | sK0 != k1_relat_1(k6_relat_1(sK0)) | sK1 = k6_relat_1(sK0) | ~v1_funct_1(k6_relat_1(sK0)) | ~v1_relat_1(k6_relat_1(sK0)) | ~r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0) | sK1 = k6_relat_1(sK0) | ~r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0)),
% 1.17/0.71    inference(superposition,[],[f812,f1351])).
% 1.17/0.71  fof(f1351,plain,(
% 1.17/0.71    ( ! [X4] : (k1_funct_1(k6_relat_1(sK0),X4) = X4 | ~r2_hidden(X4,sK0)) )),
% 1.17/0.71    inference(forward_demodulation,[],[f1338,f1272])).
% 1.17/0.71  fof(f1272,plain,(
% 1.17/0.71    sK0 = k2_relat_1(sK1)),
% 1.17/0.71    inference(duplicate_literal_removal,[],[f1269])).
% 1.17/0.71  fof(f1269,plain,(
% 1.17/0.71    sK0 = k2_relat_1(sK1) | sK0 = k2_relat_1(sK1)),
% 1.17/0.71    inference(superposition,[],[f48,f1172])).
% 1.17/0.71  fof(f1172,plain,(
% 1.17/0.71    sK1 = k6_relat_1(sK0) | sK0 = k2_relat_1(sK1)),
% 1.17/0.71    inference(subsumption_resolution,[],[f1153,f775])).
% 1.17/0.71  fof(f775,plain,(
% 1.17/0.71    ( ! [X0] : (~r2_hidden(sK4(sK1,X0),sK0) | k2_relat_1(sK1) = X0 | ~r2_hidden(sK4(sK1,X0),X0) | sK1 = k6_relat_1(sK0)) )),
% 1.17/0.71    inference(equality_resolution,[],[f774])).
% 1.17/0.71  fof(f774,plain,(
% 1.17/0.71    ( ! [X6,X5] : (sK4(sK1,X6) != X5 | ~r2_hidden(X5,sK0) | k2_relat_1(sK1) = X6 | ~r2_hidden(sK4(sK1,X6),X6) | sK1 = k6_relat_1(sK0)) )),
% 1.17/0.71    inference(duplicate_literal_removal,[],[f773])).
% 1.17/0.71  fof(f773,plain,(
% 1.17/0.71    ( ! [X6,X5] : (~r2_hidden(X5,sK0) | sK4(sK1,X6) != X5 | k2_relat_1(sK1) = X6 | ~r2_hidden(sK4(sK1,X6),X6) | ~r2_hidden(X5,sK0) | sK1 = k6_relat_1(sK0)) )),
% 1.17/0.71    inference(forward_demodulation,[],[f150,f127])).
% 1.17/0.71  fof(f150,plain,(
% 1.17/0.71    ( ! [X6,X5] : (sK4(sK1,X6) != X5 | k2_relat_1(sK1) = X6 | ~r2_hidden(X5,k1_relat_1(sK1)) | ~r2_hidden(sK4(sK1,X6),X6) | ~r2_hidden(X5,sK0) | sK1 = k6_relat_1(sK0)) )),
% 1.17/0.71    inference(subsumption_resolution,[],[f149,f39])).
% 1.17/0.71  fof(f149,plain,(
% 1.17/0.71    ( ! [X6,X5] : (sK4(sK1,X6) != X5 | k2_relat_1(sK1) = X6 | ~r2_hidden(X5,k1_relat_1(sK1)) | ~r2_hidden(sK4(sK1,X6),X6) | ~v1_relat_1(sK1) | ~r2_hidden(X5,sK0) | sK1 = k6_relat_1(sK0)) )),
% 1.17/0.71    inference(subsumption_resolution,[],[f134,f40])).
% 1.17/0.71  fof(f134,plain,(
% 1.17/0.71    ( ! [X6,X5] : (sK4(sK1,X6) != X5 | k2_relat_1(sK1) = X6 | ~r2_hidden(X5,k1_relat_1(sK1)) | ~r2_hidden(sK4(sK1,X6),X6) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X5,sK0) | sK1 = k6_relat_1(sK0)) )),
% 1.17/0.71    inference(superposition,[],[f58,f42])).
% 1.17/0.71  fof(f42,plain,(
% 1.17/0.71    ( ! [X3] : (k1_funct_1(sK1,X3) = X3 | ~r2_hidden(X3,sK0) | sK1 = k6_relat_1(sK0)) )),
% 1.17/0.71    inference(cnf_transformation,[],[f28])).
% 1.17/0.71  fof(f58,plain,(
% 1.17/0.71    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(sK4(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.17/0.71    inference(cnf_transformation,[],[f36])).
% 1.17/0.71  fof(f36,plain,(
% 1.17/0.71    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & ((sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.17/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f32,f35,f34,f33])).
% 1.17/0.71  fof(f33,plain,(
% 1.17/0.71    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1))))),
% 1.17/0.71    introduced(choice_axiom,[])).
% 1.17/0.71  fof(f34,plain,(
% 1.17/0.71    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 1.17/0.71    introduced(choice_axiom,[])).
% 1.17/0.71  fof(f35,plain,(
% 1.17/0.71    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))))),
% 1.17/0.71    introduced(choice_axiom,[])).
% 1.17/0.71  fof(f32,plain,(
% 1.17/0.71    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.17/0.71    inference(rectify,[],[f31])).
% 1.17/0.71  fof(f31,plain,(
% 1.17/0.71    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.17/0.71    inference(nnf_transformation,[],[f18])).
% 1.17/0.71  fof(f18,plain,(
% 1.17/0.71    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.17/0.71    inference(flattening,[],[f17])).
% 1.17/0.71  fof(f17,plain,(
% 1.17/0.71    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.17/0.71    inference(ennf_transformation,[],[f4])).
% 1.17/0.71  fof(f4,axiom,(
% 1.17/0.71    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.17/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.17/0.71  fof(f1153,plain,(
% 1.17/0.71    r2_hidden(sK4(sK1,sK0),sK0) | sK0 = k2_relat_1(sK1) | sK1 = k6_relat_1(sK0)),
% 1.17/0.71    inference(factoring,[],[f727])).
% 1.17/0.71  fof(f727,plain,(
% 1.17/0.71    ( ! [X1] : (r2_hidden(sK4(sK1,X1),sK0) | k2_relat_1(sK1) = X1 | r2_hidden(sK4(sK1,X1),X1) | sK1 = k6_relat_1(sK0)) )),
% 1.17/0.71    inference(duplicate_literal_removal,[],[f722])).
% 1.17/0.71  fof(f722,plain,(
% 1.17/0.71    ( ! [X1] : (r2_hidden(sK4(sK1,X1),sK0) | k2_relat_1(sK1) = X1 | r2_hidden(sK4(sK1,X1),X1) | sK1 = k6_relat_1(sK0) | k2_relat_1(sK1) = X1 | r2_hidden(sK4(sK1,X1),X1)) )),
% 1.17/0.71    inference(superposition,[],[f366,f720])).
% 1.17/0.71  fof(f720,plain,(
% 1.17/0.71    ( ! [X1] : (sK5(sK1,X1) = sK4(sK1,X1) | sK1 = k6_relat_1(sK0) | k2_relat_1(sK1) = X1 | r2_hidden(sK4(sK1,X1),X1)) )),
% 1.17/0.71    inference(subsumption_resolution,[],[f140,f366])).
% 1.17/0.71  fof(f140,plain,(
% 1.17/0.71    ( ! [X1] : (sK5(sK1,X1) = sK4(sK1,X1) | ~r2_hidden(sK5(sK1,X1),sK0) | sK1 = k6_relat_1(sK0) | k2_relat_1(sK1) = X1 | r2_hidden(sK4(sK1,X1),X1)) )),
% 1.17/0.71    inference(subsumption_resolution,[],[f139,f39])).
% 1.17/0.71  fof(f139,plain,(
% 1.17/0.71    ( ! [X1] : (sK5(sK1,X1) = sK4(sK1,X1) | ~r2_hidden(sK5(sK1,X1),sK0) | sK1 = k6_relat_1(sK0) | k2_relat_1(sK1) = X1 | r2_hidden(sK4(sK1,X1),X1) | ~v1_relat_1(sK1)) )),
% 1.17/0.71    inference(subsumption_resolution,[],[f129,f40])).
% 1.17/0.71  fof(f129,plain,(
% 1.17/0.71    ( ! [X1] : (sK5(sK1,X1) = sK4(sK1,X1) | ~r2_hidden(sK5(sK1,X1),sK0) | sK1 = k6_relat_1(sK0) | k2_relat_1(sK1) = X1 | r2_hidden(sK4(sK1,X1),X1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.17/0.71    inference(superposition,[],[f42,f57])).
% 1.17/0.71  fof(f57,plain,(
% 1.17/0.71    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) | r2_hidden(sK4(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.17/0.71    inference(cnf_transformation,[],[f36])).
% 1.17/0.71  fof(f366,plain,(
% 1.17/0.71    ( ! [X4] : (r2_hidden(sK5(sK1,X4),sK0) | k2_relat_1(sK1) = X4 | r2_hidden(sK4(sK1,X4),X4)) )),
% 1.17/0.71    inference(forward_demodulation,[],[f109,f127])).
% 1.17/0.71  fof(f109,plain,(
% 1.17/0.71    ( ! [X4] : (k2_relat_1(sK1) = X4 | r2_hidden(sK5(sK1,X4),k1_relat_1(sK1)) | r2_hidden(sK4(sK1,X4),X4)) )),
% 1.17/0.71    inference(subsumption_resolution,[],[f91,f39])).
% 1.17/0.71  fof(f91,plain,(
% 1.17/0.71    ( ! [X4] : (k2_relat_1(sK1) = X4 | r2_hidden(sK5(sK1,X4),k1_relat_1(sK1)) | r2_hidden(sK4(sK1,X4),X4) | ~v1_relat_1(sK1)) )),
% 1.17/0.71    inference(resolution,[],[f40,f56])).
% 1.17/0.71  fof(f56,plain,(
% 1.17/0.71    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | r2_hidden(sK4(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.17/0.71    inference(cnf_transformation,[],[f36])).
% 1.17/0.71  fof(f48,plain,(
% 1.17/0.71    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.17/0.71    inference(cnf_transformation,[],[f1])).
% 1.17/0.71  fof(f1338,plain,(
% 1.17/0.71    ( ! [X4] : (~r2_hidden(X4,sK0) | k1_funct_1(k6_relat_1(k2_relat_1(sK1)),X4) = X4) )),
% 1.17/0.71    inference(backward_demodulation,[],[f884,f1272])).
% 1.17/0.71  fof(f884,plain,(
% 1.17/0.71    ( ! [X4] : (k1_funct_1(k6_relat_1(k2_relat_1(sK1)),X4) = X4 | ~r2_hidden(X4,k2_relat_1(sK1))) )),
% 1.17/0.71    inference(subsumption_resolution,[],[f866,f290])).
% 1.17/0.71  fof(f290,plain,(
% 1.17/0.71    ( ! [X26] : (r2_hidden(sK6(sK1,X26),sK0) | ~r2_hidden(X26,k2_relat_1(sK1))) )),
% 1.17/0.71    inference(forward_demodulation,[],[f122,f127])).
% 1.17/0.71  fof(f122,plain,(
% 1.17/0.71    ( ! [X26] : (r2_hidden(sK6(sK1,X26),k1_relat_1(sK1)) | ~r2_hidden(X26,k2_relat_1(sK1))) )),
% 1.17/0.71    inference(subsumption_resolution,[],[f104,f39])).
% 1.17/0.71  fof(f104,plain,(
% 1.17/0.71    ( ! [X26] : (r2_hidden(sK6(sK1,X26),k1_relat_1(sK1)) | ~r2_hidden(X26,k2_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 1.17/0.71    inference(resolution,[],[f40,f66])).
% 1.17/0.71  fof(f66,plain,(
% 1.17/0.71    ( ! [X0,X5] : (r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.17/0.71    inference(equality_resolution,[],[f53])).
% 1.17/0.71  fof(f53,plain,(
% 1.17/0.71    ( ! [X0,X5,X1] : (r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.17/0.71    inference(cnf_transformation,[],[f36])).
% 1.17/0.71  fof(f866,plain,(
% 1.17/0.71    ( ! [X4] : (k1_funct_1(k6_relat_1(k2_relat_1(sK1)),X4) = X4 | ~r2_hidden(sK6(sK1,X4),sK0) | ~r2_hidden(X4,k2_relat_1(sK1))) )),
% 1.17/0.71    inference(superposition,[],[f263,f121])).
% 1.17/0.71  fof(f121,plain,(
% 1.17/0.71    ( ! [X25] : (k1_funct_1(sK1,sK6(sK1,X25)) = X25 | ~r2_hidden(X25,k2_relat_1(sK1))) )),
% 1.17/0.71    inference(subsumption_resolution,[],[f103,f39])).
% 1.17/0.71  fof(f103,plain,(
% 1.17/0.71    ( ! [X25] : (k1_funct_1(sK1,sK6(sK1,X25)) = X25 | ~r2_hidden(X25,k2_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 1.17/0.71    inference(resolution,[],[f40,f65])).
% 1.17/0.71  fof(f65,plain,(
% 1.17/0.71    ( ! [X0,X5] : (k1_funct_1(X0,sK6(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.17/0.71    inference(equality_resolution,[],[f54])).
% 1.17/0.71  fof(f54,plain,(
% 1.17/0.71    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK6(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.17/0.71    inference(cnf_transformation,[],[f36])).
% 1.17/0.71  fof(f263,plain,(
% 1.17/0.71    ( ! [X3] : (k1_funct_1(sK1,X3) = k1_funct_1(k6_relat_1(k2_relat_1(sK1)),k1_funct_1(sK1,X3)) | ~r2_hidden(X3,sK0)) )),
% 1.17/0.71    inference(forward_demodulation,[],[f262,f127])).
% 1.17/0.71  fof(f262,plain,(
% 1.17/0.71    ( ! [X3] : (k1_funct_1(sK1,X3) = k1_funct_1(k6_relat_1(k2_relat_1(sK1)),k1_funct_1(sK1,X3)) | ~r2_hidden(X3,k1_relat_1(sK1))) )),
% 1.17/0.71    inference(subsumption_resolution,[],[f261,f39])).
% 1.17/0.71  fof(f261,plain,(
% 1.17/0.71    ( ! [X3] : (k1_funct_1(sK1,X3) = k1_funct_1(k6_relat_1(k2_relat_1(sK1)),k1_funct_1(sK1,X3)) | ~r2_hidden(X3,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 1.17/0.71    inference(subsumption_resolution,[],[f260,f40])).
% 1.17/0.71  fof(f260,plain,(
% 1.17/0.71    ( ! [X3] : (k1_funct_1(sK1,X3) = k1_funct_1(k6_relat_1(k2_relat_1(sK1)),k1_funct_1(sK1,X3)) | ~r2_hidden(X3,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.17/0.71    inference(subsumption_resolution,[],[f259,f45])).
% 1.17/0.71  fof(f259,plain,(
% 1.17/0.71    ( ! [X3] : (k1_funct_1(sK1,X3) = k1_funct_1(k6_relat_1(k2_relat_1(sK1)),k1_funct_1(sK1,X3)) | ~r2_hidden(X3,k1_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(k2_relat_1(sK1))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.17/0.71    inference(subsumption_resolution,[],[f244,f46])).
% 1.17/0.71  fof(f244,plain,(
% 1.17/0.71    ( ! [X3] : (k1_funct_1(sK1,X3) = k1_funct_1(k6_relat_1(k2_relat_1(sK1)),k1_funct_1(sK1,X3)) | ~r2_hidden(X3,k1_relat_1(sK1)) | ~v1_funct_1(k6_relat_1(k2_relat_1(sK1))) | ~v1_relat_1(k6_relat_1(k2_relat_1(sK1))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.17/0.71    inference(superposition,[],[f59,f67])).
% 1.17/0.71  fof(f67,plain,(
% 1.17/0.71    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))),
% 1.17/0.71    inference(resolution,[],[f39,f49])).
% 1.17/0.71  fof(f49,plain,(
% 1.17/0.71    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.17/0.71    inference(cnf_transformation,[],[f13])).
% 1.17/0.71  fof(f13,plain,(
% 1.17/0.71    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.17/0.71    inference(ennf_transformation,[],[f3])).
% 1.17/0.71  fof(f3,axiom,(
% 1.17/0.71    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.17/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 1.17/0.71  fof(f59,plain,(
% 1.17/0.71    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.17/0.71    inference(cnf_transformation,[],[f20])).
% 1.17/0.71  fof(f20,plain,(
% 1.17/0.71    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.17/0.71    inference(flattening,[],[f19])).
% 1.17/0.71  fof(f19,plain,(
% 1.17/0.71    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.17/0.71    inference(ennf_transformation,[],[f7])).
% 1.17/0.71  fof(f7,axiom,(
% 1.17/0.71    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 1.17/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 1.17/0.71  fof(f812,plain,(
% 1.17/0.71    ( ! [X8] : (sK3(X8,sK1) != k1_funct_1(X8,sK3(X8,sK1)) | sK0 != k1_relat_1(X8) | sK1 = X8 | ~v1_funct_1(X8) | ~v1_relat_1(X8) | ~r2_hidden(sK3(X8,sK1),sK0) | sK1 = k6_relat_1(sK0)) )),
% 1.17/0.71    inference(forward_demodulation,[],[f154,f127])).
% 1.17/0.71  fof(f154,plain,(
% 1.17/0.71    ( ! [X8] : (sK3(X8,sK1) != k1_funct_1(X8,sK3(X8,sK1)) | sK1 = X8 | k1_relat_1(sK1) != k1_relat_1(X8) | ~v1_funct_1(X8) | ~v1_relat_1(X8) | ~r2_hidden(sK3(X8,sK1),sK0) | sK1 = k6_relat_1(sK0)) )),
% 1.17/0.71    inference(subsumption_resolution,[],[f153,f39])).
% 1.17/0.71  fof(f153,plain,(
% 1.17/0.71    ( ! [X8] : (sK3(X8,sK1) != k1_funct_1(X8,sK3(X8,sK1)) | sK1 = X8 | k1_relat_1(sK1) != k1_relat_1(X8) | ~v1_relat_1(sK1) | ~v1_funct_1(X8) | ~v1_relat_1(X8) | ~r2_hidden(sK3(X8,sK1),sK0) | sK1 = k6_relat_1(sK0)) )),
% 1.17/0.71    inference(subsumption_resolution,[],[f136,f40])).
% 1.17/0.71  fof(f136,plain,(
% 1.17/0.71    ( ! [X8] : (sK3(X8,sK1) != k1_funct_1(X8,sK3(X8,sK1)) | sK1 = X8 | k1_relat_1(sK1) != k1_relat_1(X8) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(X8) | ~v1_relat_1(X8) | ~r2_hidden(sK3(X8,sK1),sK0) | sK1 = k6_relat_1(sK0)) )),
% 1.17/0.71    inference(superposition,[],[f52,f42])).
% 1.17/0.71  fof(f52,plain,(
% 1.17/0.71    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.17/0.71    inference(cnf_transformation,[],[f30])).
% 1.17/0.71  fof(f175,plain,(
% 1.17/0.71    sK1 != k6_relat_1(sK0) | r2_hidden(sK2,sK0)),
% 1.17/0.71    inference(trivial_inequality_removal,[],[f159])).
% 1.17/0.71  fof(f159,plain,(
% 1.17/0.71    sK0 != sK0 | sK1 != k6_relat_1(sK0) | r2_hidden(sK2,sK0)),
% 1.17/0.71    inference(backward_demodulation,[],[f43,f127])).
% 1.17/0.71  fof(f43,plain,(
% 1.17/0.71    sK1 != k6_relat_1(sK0) | sK0 != k1_relat_1(sK1) | r2_hidden(sK2,sK0)),
% 1.17/0.71    inference(cnf_transformation,[],[f28])).
% 1.17/0.71  fof(f1777,plain,(
% 1.17/0.71    ~r2_hidden(sK2,sK0)),
% 1.17/0.71    inference(trivial_inequality_removal,[],[f1761])).
% 1.17/0.71  fof(f1761,plain,(
% 1.17/0.71    sK2 != sK2 | ~r2_hidden(sK2,sK0)),
% 1.17/0.71    inference(superposition,[],[f1671,f1664])).
% 1.17/0.71  fof(f1664,plain,(
% 1.17/0.71    ( ! [X4] : (k1_funct_1(sK1,X4) = X4 | ~r2_hidden(X4,sK0)) )),
% 1.17/0.71    inference(backward_demodulation,[],[f1351,f1629])).
% 1.17/0.71  fof(f1671,plain,(
% 1.17/0.71    sK2 != k1_funct_1(sK1,sK2)),
% 1.17/0.71    inference(trivial_inequality_removal,[],[f1659])).
% 1.17/0.71  fof(f1659,plain,(
% 1.17/0.71    sK1 != sK1 | sK2 != k1_funct_1(sK1,sK2)),
% 1.17/0.71    inference(backward_demodulation,[],[f207,f1629])).
% 1.17/0.71  fof(f207,plain,(
% 1.17/0.71    sK2 != k1_funct_1(sK1,sK2) | sK1 != k6_relat_1(sK0)),
% 1.17/0.71    inference(subsumption_resolution,[],[f44,f127])).
% 1.17/0.71  fof(f44,plain,(
% 1.17/0.71    sK2 != k1_funct_1(sK1,sK2) | sK0 != k1_relat_1(sK1) | sK1 != k6_relat_1(sK0)),
% 1.17/0.71    inference(cnf_transformation,[],[f28])).
% 1.17/0.71  % SZS output end Proof for theBenchmark
% 1.17/0.71  % (13338)------------------------------
% 1.17/0.71  % (13338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.71  % (13338)Termination reason: Refutation
% 1.17/0.71  
% 1.17/0.71  % (13338)Memory used [KB]: 2302
% 1.17/0.71  % (13338)Time elapsed: 0.126 s
% 1.17/0.71  % (13338)------------------------------
% 1.17/0.71  % (13338)------------------------------
% 1.17/0.71  % (13094)Success in time 0.356 s
%------------------------------------------------------------------------------
