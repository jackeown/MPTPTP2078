%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:16 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
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
fof(f1216,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1199,f1128])).

fof(f1128,plain,(
    r2_hidden(sK2,sK0) ),
    inference(trivial_inequality_removal,[],[f1115])).

fof(f1115,plain,
    ( sK1 != sK1
    | r2_hidden(sK2,sK0) ),
    inference(backward_demodulation,[],[f150,f1087])).

fof(f1087,plain,(
    sK1 = k6_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f1086,f478])).

fof(f478,plain,
    ( r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0)
    | sK1 = k6_relat_1(sK0) ),
    inference(equality_resolution,[],[f290])).

fof(f290,plain,(
    ! [X0] :
      ( sK0 != X0
      | k6_relat_1(X0) = sK1
      | r2_hidden(sK3(k6_relat_1(X0),sK1),X0) ) ),
    inference(subsumption_resolution,[],[f289,f43])).

fof(f43,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f289,plain,(
    ! [X0] :
      ( sK0 != X0
      | k6_relat_1(X0) = sK1
      | r2_hidden(sK3(k6_relat_1(X0),sK1),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f287,f44])).

fof(f44,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f287,plain,(
    ! [X0] :
      ( sK0 != X0
      | k6_relat_1(X0) = sK1
      | r2_hidden(sK3(k6_relat_1(X0),sK1),X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f286,f45])).

fof(f45,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f286,plain,(
    ! [X1] :
      ( k1_relat_1(X1) != sK0
      | sK1 = X1
      | r2_hidden(sK3(X1,sK1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f92,f108])).

fof(f108,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,
    ( sK0 = k1_relat_1(sK1)
    | sK0 = k1_relat_1(sK1) ),
    inference(superposition,[],[f45,f39])).

fof(f39,plain,
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

fof(f92,plain,(
    ! [X1] :
      ( sK1 = X1
      | r2_hidden(sK3(X1,sK1),k1_relat_1(X1))
      | k1_relat_1(X1) != k1_relat_1(sK1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f79,f37])).

fof(f37,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    ! [X1] :
      ( sK1 = X1
      | r2_hidden(sK3(X1,sK1),k1_relat_1(X1))
      | k1_relat_1(X1) != k1_relat_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f38,f49])).

fof(f49,plain,(
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

fof(f38,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f1086,plain,
    ( sK1 = k6_relat_1(sK0)
    | ~ r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f1085,f43])).

fof(f1085,plain,
    ( sK1 = k6_relat_1(sK0)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f1084,f44])).

fof(f1084,plain,
    ( sK1 = k6_relat_1(sK0)
    | ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f1063,f45])).

fof(f1063,plain,
    ( sK0 != k1_relat_1(k6_relat_1(sK0))
    | sK1 = k6_relat_1(sK0)
    | ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f1062])).

fof(f1062,plain,
    ( sK3(k6_relat_1(sK0),sK1) != sK3(k6_relat_1(sK0),sK1)
    | sK0 != k1_relat_1(k6_relat_1(sK0))
    | sK1 = k6_relat_1(sK0)
    | ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0) ),
    inference(duplicate_literal_removal,[],[f1053])).

fof(f1053,plain,
    ( sK3(k6_relat_1(sK0),sK1) != sK3(k6_relat_1(sK0),sK1)
    | sK0 != k1_relat_1(k6_relat_1(sK0))
    | sK1 = k6_relat_1(sK0)
    | ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0)
    | sK1 = k6_relat_1(sK0)
    | ~ r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0) ),
    inference(superposition,[],[f471,f852])).

fof(f852,plain,(
    ! [X4] :
      ( k1_funct_1(k6_relat_1(sK0),X4) = X4
      | ~ r2_hidden(X4,sK0) ) ),
    inference(forward_demodulation,[],[f838,f802])).

fof(f802,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(duplicate_literal_removal,[],[f799])).

fof(f799,plain,
    ( sK0 = k2_relat_1(sK1)
    | sK0 = k2_relat_1(sK1) ),
    inference(superposition,[],[f46,f770])).

fof(f770,plain,
    ( sK1 = k6_relat_1(sK0)
    | sK0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f715,f463])).

fof(f463,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK1,X0),sK0)
      | k2_relat_1(sK1) = X0
      | ~ r2_hidden(sK4(sK1,X0),X0)
      | sK1 = k6_relat_1(sK0) ) ),
    inference(equality_resolution,[],[f462])).

fof(f462,plain,(
    ! [X2,X3] :
      ( sK4(sK1,X3) != X2
      | ~ r2_hidden(X2,sK0)
      | k2_relat_1(sK1) = X3
      | ~ r2_hidden(sK4(sK1,X3),X3)
      | sK1 = k6_relat_1(sK0) ) ),
    inference(duplicate_literal_removal,[],[f461])).

fof(f461,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK0)
      | sK4(sK1,X3) != X2
      | k2_relat_1(sK1) = X3
      | ~ r2_hidden(sK4(sK1,X3),X3)
      | ~ r2_hidden(X2,sK0)
      | sK1 = k6_relat_1(sK0) ) ),
    inference(forward_demodulation,[],[f128,f108])).

fof(f128,plain,(
    ! [X2,X3] :
      ( sK4(sK1,X3) != X2
      | k2_relat_1(sK1) = X3
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ r2_hidden(sK4(sK1,X3),X3)
      | ~ r2_hidden(X2,sK0)
      | sK1 = k6_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f127,f37])).

fof(f127,plain,(
    ! [X2,X3] :
      ( sK4(sK1,X3) != X2
      | k2_relat_1(sK1) = X3
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ r2_hidden(sK4(sK1,X3),X3)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X2,sK0)
      | sK1 = k6_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f114,f38])).

fof(f114,plain,(
    ! [X2,X3] :
      ( sK4(sK1,X3) != X2
      | k2_relat_1(sK1) = X3
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ r2_hidden(sK4(sK1,X3),X3)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X2,sK0)
      | sK1 = k6_relat_1(sK0) ) ),
    inference(superposition,[],[f56,f40])).

fof(f40,plain,(
    ! [X3] :
      ( k1_funct_1(sK1,X3) = X3
      | ~ r2_hidden(X3,sK0)
      | sK1 = k6_relat_1(sK0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
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

fof(f715,plain,
    ( r2_hidden(sK4(sK1,sK0),sK0)
    | sK0 = k2_relat_1(sK1)
    | sK1 = k6_relat_1(sK0) ),
    inference(factoring,[],[f454])).

fof(f454,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK1,X1),sK0)
      | k2_relat_1(sK1) = X1
      | r2_hidden(sK4(sK1,X1),X1)
      | sK1 = k6_relat_1(sK0) ) ),
    inference(duplicate_literal_removal,[],[f449])).

fof(f449,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK1,X1),sK0)
      | k2_relat_1(sK1) = X1
      | r2_hidden(sK4(sK1,X1),X1)
      | sK1 = k6_relat_1(sK0)
      | k2_relat_1(sK1) = X1
      | r2_hidden(sK4(sK1,X1),X1) ) ),
    inference(superposition,[],[f248,f447])).

fof(f447,plain,(
    ! [X1] :
      ( sK5(sK1,X1) = sK4(sK1,X1)
      | sK1 = k6_relat_1(sK0)
      | k2_relat_1(sK1) = X1
      | r2_hidden(sK4(sK1,X1),X1) ) ),
    inference(subsumption_resolution,[],[f120,f248])).

fof(f120,plain,(
    ! [X1] :
      ( sK5(sK1,X1) = sK4(sK1,X1)
      | ~ r2_hidden(sK5(sK1,X1),sK0)
      | sK1 = k6_relat_1(sK0)
      | k2_relat_1(sK1) = X1
      | r2_hidden(sK4(sK1,X1),X1) ) ),
    inference(subsumption_resolution,[],[f119,f37])).

fof(f119,plain,(
    ! [X1] :
      ( sK5(sK1,X1) = sK4(sK1,X1)
      | ~ r2_hidden(sK5(sK1,X1),sK0)
      | sK1 = k6_relat_1(sK0)
      | k2_relat_1(sK1) = X1
      | r2_hidden(sK4(sK1,X1),X1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f110,f38])).

fof(f110,plain,(
    ! [X1] :
      ( sK5(sK1,X1) = sK4(sK1,X1)
      | ~ r2_hidden(sK5(sK1,X1),sK0)
      | sK1 = k6_relat_1(sK0)
      | k2_relat_1(sK1) = X1
      | r2_hidden(sK4(sK1,X1),X1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f40,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
      | r2_hidden(sK4(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f248,plain,(
    ! [X4] :
      ( r2_hidden(sK5(sK1,X4),sK0)
      | k2_relat_1(sK1) = X4
      | r2_hidden(sK4(sK1,X4),X4) ) ),
    inference(forward_demodulation,[],[f95,f108])).

fof(f95,plain,(
    ! [X4] :
      ( k2_relat_1(sK1) = X4
      | r2_hidden(sK5(sK1,X4),k1_relat_1(sK1))
      | r2_hidden(sK4(sK1,X4),X4) ) ),
    inference(subsumption_resolution,[],[f82,f37])).

fof(f82,plain,(
    ! [X4] :
      ( k2_relat_1(sK1) = X4
      | r2_hidden(sK5(sK1,X4),k1_relat_1(sK1))
      | r2_hidden(sK4(sK1,X4),X4)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f38,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK4(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f46,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f838,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(k6_relat_1(k2_relat_1(sK1)),X4) = X4 ) ),
    inference(backward_demodulation,[],[f558,f802])).

fof(f558,plain,(
    ! [X4] :
      ( k1_funct_1(k6_relat_1(k2_relat_1(sK1)),X4) = X4
      | ~ r2_hidden(X4,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f541,f229])).

fof(f229,plain,(
    ! [X15] :
      ( r2_hidden(sK6(sK1,X15),sK0)
      | ~ r2_hidden(X15,k2_relat_1(sK1)) ) ),
    inference(forward_demodulation,[],[f103,f108])).

fof(f103,plain,(
    ! [X15] :
      ( r2_hidden(sK6(sK1,X15),k1_relat_1(sK1))
      | ~ r2_hidden(X15,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f90,f37])).

fof(f90,plain,(
    ! [X15] :
      ( r2_hidden(sK6(sK1,X15),k1_relat_1(sK1))
      | ~ r2_hidden(X15,k2_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f38,f62])).

fof(f62,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f541,plain,(
    ! [X4] :
      ( k1_funct_1(k6_relat_1(k2_relat_1(sK1)),X4) = X4
      | ~ r2_hidden(sK6(sK1,X4),sK0)
      | ~ r2_hidden(X4,k2_relat_1(sK1)) ) ),
    inference(superposition,[],[f201,f102])).

fof(f102,plain,(
    ! [X14] :
      ( k1_funct_1(sK1,sK6(sK1,X14)) = X14
      | ~ r2_hidden(X14,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f89,f37])).

fof(f89,plain,(
    ! [X14] :
      ( k1_funct_1(sK1,sK6(sK1,X14)) = X14
      | ~ r2_hidden(X14,k2_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f38,f61])).

fof(f61,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f201,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) = k1_funct_1(k6_relat_1(k2_relat_1(sK1)),k1_funct_1(sK1,X0))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(forward_demodulation,[],[f200,f108])).

fof(f200,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) = k1_funct_1(k6_relat_1(k2_relat_1(sK1)),k1_funct_1(sK1,X0))
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f199,f37])).

fof(f199,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) = k1_funct_1(k6_relat_1(k2_relat_1(sK1)),k1_funct_1(sK1,X0))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f198,f38])).

fof(f198,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) = k1_funct_1(k6_relat_1(k2_relat_1(sK1)),k1_funct_1(sK1,X0))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f197,f43])).

fof(f197,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) = k1_funct_1(k6_relat_1(k2_relat_1(sK1)),k1_funct_1(sK1,X0))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(sK1)))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f188,f44])).

fof(f188,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) = k1_funct_1(k6_relat_1(k2_relat_1(sK1)),k1_funct_1(sK1,X0))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(k6_relat_1(k2_relat_1(sK1)))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(sK1)))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f58,f63])).

fof(f63,plain,(
    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) ),
    inference(resolution,[],[f37,f47])).

fof(f47,plain,(
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

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f471,plain,(
    ! [X5] :
      ( sK3(X5,sK1) != k1_funct_1(X5,sK3(X5,sK1))
      | sK0 != k1_relat_1(X5)
      | sK1 = X5
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5)
      | ~ r2_hidden(sK3(X5,sK1),sK0)
      | sK1 = k6_relat_1(sK0) ) ),
    inference(forward_demodulation,[],[f132,f108])).

fof(f132,plain,(
    ! [X5] :
      ( sK3(X5,sK1) != k1_funct_1(X5,sK3(X5,sK1))
      | sK1 = X5
      | k1_relat_1(sK1) != k1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5)
      | ~ r2_hidden(sK3(X5,sK1),sK0)
      | sK1 = k6_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f131,f37])).

fof(f131,plain,(
    ! [X5] :
      ( sK3(X5,sK1) != k1_funct_1(X5,sK3(X5,sK1))
      | sK1 = X5
      | k1_relat_1(sK1) != k1_relat_1(X5)
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5)
      | ~ r2_hidden(sK3(X5,sK1),sK0)
      | sK1 = k6_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f116,f38])).

fof(f116,plain,(
    ! [X5] :
      ( sK3(X5,sK1) != k1_funct_1(X5,sK3(X5,sK1))
      | sK1 = X5
      | k1_relat_1(sK1) != k1_relat_1(X5)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5)
      | ~ r2_hidden(sK3(X5,sK1),sK0)
      | sK1 = k6_relat_1(sK0) ) ),
    inference(superposition,[],[f50,f40])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f150,plain,
    ( sK1 != k6_relat_1(sK0)
    | r2_hidden(sK2,sK0) ),
    inference(trivial_inequality_removal,[],[f137])).

fof(f137,plain,
    ( sK0 != sK0
    | sK1 != k6_relat_1(sK0)
    | r2_hidden(sK2,sK0) ),
    inference(backward_demodulation,[],[f41,f108])).

fof(f41,plain,
    ( sK1 != k6_relat_1(sK0)
    | sK0 != k1_relat_1(sK1)
    | r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f1199,plain,(
    ~ r2_hidden(sK2,sK0) ),
    inference(trivial_inequality_removal,[],[f1184])).

fof(f1184,plain,
    ( sK2 != sK2
    | ~ r2_hidden(sK2,sK0) ),
    inference(superposition,[],[f1127,f1121])).

fof(f1121,plain,(
    ! [X4] :
      ( k1_funct_1(sK1,X4) = X4
      | ~ r2_hidden(X4,sK0) ) ),
    inference(backward_demodulation,[],[f852,f1087])).

fof(f1127,plain,(
    sK2 != k1_funct_1(sK1,sK2) ),
    inference(trivial_inequality_removal,[],[f1117])).

fof(f1117,plain,
    ( sK1 != sK1
    | sK2 != k1_funct_1(sK1,sK2) ),
    inference(backward_demodulation,[],[f176,f1087])).

fof(f176,plain,
    ( sK2 != k1_funct_1(sK1,sK2)
    | sK1 != k6_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f42,f108])).

fof(f42,plain,
    ( sK2 != k1_funct_1(sK1,sK2)
    | sK0 != k1_relat_1(sK1)
    | sK1 != k6_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:29:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (1505)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.54  % (1518)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.54  % (1512)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.54  % (1517)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.54  % (1504)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.54  % (1515)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (1509)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.54  % (1526)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.55  % (1520)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.55  % (1516)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.55  % (1508)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.55  % (1523)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.55  % (1525)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.55  % (1507)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.55  % (1510)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.55  % (1513)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.55  % (1509)Refutation not found, incomplete strategy% (1509)------------------------------
% 0.21/0.55  % (1509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1514)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.56  % (1524)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.56  % (1515)Refutation not found, incomplete strategy% (1515)------------------------------
% 0.21/0.56  % (1515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (1521)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.57  % (1515)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (1515)Memory used [KB]: 6140
% 0.21/0.57  % (1515)Time elapsed: 0.133 s
% 0.21/0.57  % (1515)------------------------------
% 0.21/0.57  % (1515)------------------------------
% 0.21/0.57  % (1527)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.61/0.57  % (1509)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.57  
% 1.61/0.57  % (1509)Memory used [KB]: 1663
% 1.61/0.57  % (1509)Time elapsed: 0.118 s
% 1.61/0.57  % (1509)------------------------------
% 1.61/0.57  % (1509)------------------------------
% 1.61/0.57  % (1513)Refutation not found, incomplete strategy% (1513)------------------------------
% 1.61/0.57  % (1513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (1513)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.57  
% 1.61/0.57  % (1513)Memory used [KB]: 10618
% 1.61/0.57  % (1513)Time elapsed: 0.142 s
% 1.61/0.57  % (1513)------------------------------
% 1.61/0.57  % (1513)------------------------------
% 1.61/0.58  % (1502)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.61/0.58  % (1503)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.61/0.58  % (1502)Refutation not found, incomplete strategy% (1502)------------------------------
% 1.61/0.58  % (1502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (1502)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.58  
% 1.61/0.58  % (1502)Memory used [KB]: 10618
% 1.61/0.58  % (1502)Time elapsed: 0.153 s
% 1.61/0.58  % (1502)------------------------------
% 1.61/0.58  % (1502)------------------------------
% 1.61/0.58  % (1506)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.61/0.58  % (1520)Refutation found. Thanks to Tanya!
% 1.61/0.58  % SZS status Theorem for theBenchmark
% 1.61/0.58  % SZS output start Proof for theBenchmark
% 1.61/0.58  fof(f1216,plain,(
% 1.61/0.58    $false),
% 1.61/0.58    inference(subsumption_resolution,[],[f1199,f1128])).
% 1.61/0.58  fof(f1128,plain,(
% 1.61/0.58    r2_hidden(sK2,sK0)),
% 1.61/0.58    inference(trivial_inequality_removal,[],[f1115])).
% 1.61/0.58  fof(f1115,plain,(
% 1.61/0.58    sK1 != sK1 | r2_hidden(sK2,sK0)),
% 1.61/0.58    inference(backward_demodulation,[],[f150,f1087])).
% 1.61/0.58  fof(f1087,plain,(
% 1.61/0.58    sK1 = k6_relat_1(sK0)),
% 1.61/0.58    inference(subsumption_resolution,[],[f1086,f478])).
% 1.61/0.58  fof(f478,plain,(
% 1.61/0.58    r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0) | sK1 = k6_relat_1(sK0)),
% 1.61/0.58    inference(equality_resolution,[],[f290])).
% 1.61/0.58  fof(f290,plain,(
% 1.61/0.58    ( ! [X0] : (sK0 != X0 | k6_relat_1(X0) = sK1 | r2_hidden(sK3(k6_relat_1(X0),sK1),X0)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f289,f43])).
% 1.61/0.58  fof(f43,plain,(
% 1.61/0.58    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.61/0.58    inference(cnf_transformation,[],[f5])).
% 1.61/0.58  fof(f5,axiom,(
% 1.61/0.58    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.61/0.58  fof(f289,plain,(
% 1.61/0.58    ( ! [X0] : (sK0 != X0 | k6_relat_1(X0) = sK1 | r2_hidden(sK3(k6_relat_1(X0),sK1),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f287,f44])).
% 1.61/0.58  fof(f44,plain,(
% 1.61/0.58    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.61/0.58    inference(cnf_transformation,[],[f5])).
% 1.61/0.58  fof(f287,plain,(
% 1.61/0.58    ( ! [X0] : (sK0 != X0 | k6_relat_1(X0) = sK1 | r2_hidden(sK3(k6_relat_1(X0),sK1),X0) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.61/0.58    inference(superposition,[],[f286,f45])).
% 1.61/0.58  fof(f45,plain,(
% 1.61/0.58    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.61/0.58    inference(cnf_transformation,[],[f1])).
% 1.61/0.58  fof(f1,axiom,(
% 1.61/0.58    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.61/0.58  fof(f286,plain,(
% 1.61/0.58    ( ! [X1] : (k1_relat_1(X1) != sK0 | sK1 = X1 | r2_hidden(sK3(X1,sK1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.61/0.58    inference(forward_demodulation,[],[f92,f108])).
% 1.61/0.58  fof(f108,plain,(
% 1.61/0.58    sK0 = k1_relat_1(sK1)),
% 1.61/0.58    inference(duplicate_literal_removal,[],[f104])).
% 1.61/0.58  fof(f104,plain,(
% 1.61/0.58    sK0 = k1_relat_1(sK1) | sK0 = k1_relat_1(sK1)),
% 1.61/0.58    inference(superposition,[],[f45,f39])).
% 1.61/0.58  fof(f39,plain,(
% 1.61/0.58    sK1 = k6_relat_1(sK0) | sK0 = k1_relat_1(sK1)),
% 1.61/0.58    inference(cnf_transformation,[],[f28])).
% 1.61/0.58  fof(f28,plain,(
% 1.61/0.58    ((sK2 != k1_funct_1(sK1,sK2) & r2_hidden(sK2,sK0)) | sK0 != k1_relat_1(sK1) | sK1 != k6_relat_1(sK0)) & ((! [X3] : (k1_funct_1(sK1,X3) = X3 | ~r2_hidden(X3,sK0)) & sK0 = k1_relat_1(sK1)) | sK1 = k6_relat_1(sK0)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.61/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f27,f26])).
% 1.61/0.58  fof(f26,plain,(
% 1.61/0.58    ? [X0,X1] : ((? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0 | k6_relat_1(X0) != X1) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) = X1) & v1_funct_1(X1) & v1_relat_1(X1)) => ((? [X2] : (k1_funct_1(sK1,X2) != X2 & r2_hidden(X2,sK0)) | sK0 != k1_relat_1(sK1) | sK1 != k6_relat_1(sK0)) & ((! [X3] : (k1_funct_1(sK1,X3) = X3 | ~r2_hidden(X3,sK0)) & sK0 = k1_relat_1(sK1)) | sK1 = k6_relat_1(sK0)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.61/0.58    introduced(choice_axiom,[])).
% 1.61/0.58  fof(f27,plain,(
% 1.61/0.58    ? [X2] : (k1_funct_1(sK1,X2) != X2 & r2_hidden(X2,sK0)) => (sK2 != k1_funct_1(sK1,sK2) & r2_hidden(sK2,sK0))),
% 1.61/0.58    introduced(choice_axiom,[])).
% 1.61/0.58  fof(f25,plain,(
% 1.61/0.58    ? [X0,X1] : ((? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0 | k6_relat_1(X0) != X1) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) = X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.61/0.58    inference(rectify,[],[f24])).
% 1.61/0.58  fof(f24,plain,(
% 1.61/0.58    ? [X0,X1] : ((? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0 | k6_relat_1(X0) != X1) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) = X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.61/0.58    inference(flattening,[],[f23])).
% 1.61/0.58  fof(f23,plain,(
% 1.61/0.58    ? [X0,X1] : ((((? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) | k6_relat_1(X0) != X1) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) = X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.61/0.58    inference(nnf_transformation,[],[f12])).
% 1.61/0.58  fof(f12,plain,(
% 1.61/0.58    ? [X0,X1] : ((k6_relat_1(X0) = X1 <~> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.61/0.58    inference(flattening,[],[f11])).
% 1.61/0.58  fof(f11,plain,(
% 1.61/0.58    ? [X0,X1] : ((k6_relat_1(X0) = X1 <~> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.61/0.58    inference(ennf_transformation,[],[f10])).
% 1.61/0.58  fof(f10,negated_conjecture,(
% 1.61/0.58    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 1.61/0.58    inference(negated_conjecture,[],[f9])).
% 1.61/0.58  fof(f9,conjecture,(
% 1.61/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 1.61/0.58  fof(f92,plain,(
% 1.61/0.58    ( ! [X1] : (sK1 = X1 | r2_hidden(sK3(X1,sK1),k1_relat_1(X1)) | k1_relat_1(X1) != k1_relat_1(sK1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f79,f37])).
% 1.61/0.58  fof(f37,plain,(
% 1.61/0.58    v1_relat_1(sK1)),
% 1.61/0.58    inference(cnf_transformation,[],[f28])).
% 1.61/0.58  fof(f79,plain,(
% 1.61/0.58    ( ! [X1] : (sK1 = X1 | r2_hidden(sK3(X1,sK1),k1_relat_1(X1)) | k1_relat_1(X1) != k1_relat_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.61/0.58    inference(resolution,[],[f38,f49])).
% 1.61/0.58  fof(f49,plain,(
% 1.61/0.58    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f30])).
% 1.61/0.58  fof(f30,plain,(
% 1.61/0.58    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.61/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f29])).
% 1.61/0.58  fof(f29,plain,(
% 1.61/0.58    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))),
% 1.61/0.58    introduced(choice_axiom,[])).
% 1.61/0.58  fof(f16,plain,(
% 1.61/0.58    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.61/0.58    inference(flattening,[],[f15])).
% 1.61/0.58  fof(f15,plain,(
% 1.61/0.58    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.61/0.58    inference(ennf_transformation,[],[f8])).
% 1.61/0.58  fof(f8,axiom,(
% 1.61/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 1.61/0.58  fof(f38,plain,(
% 1.61/0.58    v1_funct_1(sK1)),
% 1.61/0.58    inference(cnf_transformation,[],[f28])).
% 1.61/0.58  fof(f1086,plain,(
% 1.61/0.58    sK1 = k6_relat_1(sK0) | ~r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0)),
% 1.61/0.58    inference(subsumption_resolution,[],[f1085,f43])).
% 1.61/0.58  fof(f1085,plain,(
% 1.61/0.58    sK1 = k6_relat_1(sK0) | ~v1_relat_1(k6_relat_1(sK0)) | ~r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0)),
% 1.61/0.58    inference(subsumption_resolution,[],[f1084,f44])).
% 1.61/0.58  fof(f1084,plain,(
% 1.61/0.58    sK1 = k6_relat_1(sK0) | ~v1_funct_1(k6_relat_1(sK0)) | ~v1_relat_1(k6_relat_1(sK0)) | ~r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0)),
% 1.61/0.58    inference(subsumption_resolution,[],[f1063,f45])).
% 1.61/0.58  fof(f1063,plain,(
% 1.61/0.58    sK0 != k1_relat_1(k6_relat_1(sK0)) | sK1 = k6_relat_1(sK0) | ~v1_funct_1(k6_relat_1(sK0)) | ~v1_relat_1(k6_relat_1(sK0)) | ~r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0)),
% 1.61/0.58    inference(trivial_inequality_removal,[],[f1062])).
% 1.61/0.58  fof(f1062,plain,(
% 1.61/0.58    sK3(k6_relat_1(sK0),sK1) != sK3(k6_relat_1(sK0),sK1) | sK0 != k1_relat_1(k6_relat_1(sK0)) | sK1 = k6_relat_1(sK0) | ~v1_funct_1(k6_relat_1(sK0)) | ~v1_relat_1(k6_relat_1(sK0)) | ~r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0)),
% 1.61/0.58    inference(duplicate_literal_removal,[],[f1053])).
% 1.61/0.58  fof(f1053,plain,(
% 1.61/0.58    sK3(k6_relat_1(sK0),sK1) != sK3(k6_relat_1(sK0),sK1) | sK0 != k1_relat_1(k6_relat_1(sK0)) | sK1 = k6_relat_1(sK0) | ~v1_funct_1(k6_relat_1(sK0)) | ~v1_relat_1(k6_relat_1(sK0)) | ~r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0) | sK1 = k6_relat_1(sK0) | ~r2_hidden(sK3(k6_relat_1(sK0),sK1),sK0)),
% 1.61/0.58    inference(superposition,[],[f471,f852])).
% 1.61/0.58  fof(f852,plain,(
% 1.61/0.58    ( ! [X4] : (k1_funct_1(k6_relat_1(sK0),X4) = X4 | ~r2_hidden(X4,sK0)) )),
% 1.61/0.58    inference(forward_demodulation,[],[f838,f802])).
% 1.61/0.58  fof(f802,plain,(
% 1.61/0.58    sK0 = k2_relat_1(sK1)),
% 1.61/0.58    inference(duplicate_literal_removal,[],[f799])).
% 1.61/0.58  fof(f799,plain,(
% 1.61/0.58    sK0 = k2_relat_1(sK1) | sK0 = k2_relat_1(sK1)),
% 1.61/0.58    inference(superposition,[],[f46,f770])).
% 1.61/0.58  fof(f770,plain,(
% 1.61/0.58    sK1 = k6_relat_1(sK0) | sK0 = k2_relat_1(sK1)),
% 1.61/0.58    inference(subsumption_resolution,[],[f715,f463])).
% 1.61/0.58  fof(f463,plain,(
% 1.61/0.58    ( ! [X0] : (~r2_hidden(sK4(sK1,X0),sK0) | k2_relat_1(sK1) = X0 | ~r2_hidden(sK4(sK1,X0),X0) | sK1 = k6_relat_1(sK0)) )),
% 1.61/0.58    inference(equality_resolution,[],[f462])).
% 1.61/0.58  fof(f462,plain,(
% 1.61/0.58    ( ! [X2,X3] : (sK4(sK1,X3) != X2 | ~r2_hidden(X2,sK0) | k2_relat_1(sK1) = X3 | ~r2_hidden(sK4(sK1,X3),X3) | sK1 = k6_relat_1(sK0)) )),
% 1.61/0.58    inference(duplicate_literal_removal,[],[f461])).
% 1.61/0.58  fof(f461,plain,(
% 1.61/0.58    ( ! [X2,X3] : (~r2_hidden(X2,sK0) | sK4(sK1,X3) != X2 | k2_relat_1(sK1) = X3 | ~r2_hidden(sK4(sK1,X3),X3) | ~r2_hidden(X2,sK0) | sK1 = k6_relat_1(sK0)) )),
% 1.61/0.58    inference(forward_demodulation,[],[f128,f108])).
% 1.61/0.58  fof(f128,plain,(
% 1.61/0.58    ( ! [X2,X3] : (sK4(sK1,X3) != X2 | k2_relat_1(sK1) = X3 | ~r2_hidden(X2,k1_relat_1(sK1)) | ~r2_hidden(sK4(sK1,X3),X3) | ~r2_hidden(X2,sK0) | sK1 = k6_relat_1(sK0)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f127,f37])).
% 1.61/0.58  fof(f127,plain,(
% 1.61/0.58    ( ! [X2,X3] : (sK4(sK1,X3) != X2 | k2_relat_1(sK1) = X3 | ~r2_hidden(X2,k1_relat_1(sK1)) | ~r2_hidden(sK4(sK1,X3),X3) | ~v1_relat_1(sK1) | ~r2_hidden(X2,sK0) | sK1 = k6_relat_1(sK0)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f114,f38])).
% 1.61/0.58  fof(f114,plain,(
% 1.61/0.58    ( ! [X2,X3] : (sK4(sK1,X3) != X2 | k2_relat_1(sK1) = X3 | ~r2_hidden(X2,k1_relat_1(sK1)) | ~r2_hidden(sK4(sK1,X3),X3) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X2,sK0) | sK1 = k6_relat_1(sK0)) )),
% 1.61/0.58    inference(superposition,[],[f56,f40])).
% 1.61/0.58  fof(f40,plain,(
% 1.61/0.58    ( ! [X3] : (k1_funct_1(sK1,X3) = X3 | ~r2_hidden(X3,sK0) | sK1 = k6_relat_1(sK0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f28])).
% 1.61/0.58  fof(f56,plain,(
% 1.61/0.58    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(sK4(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f36])).
% 1.61/0.58  fof(f36,plain,(
% 1.61/0.58    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & ((sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.61/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f32,f35,f34,f33])).
% 1.61/0.58  fof(f33,plain,(
% 1.61/0.58    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1))))),
% 1.61/0.58    introduced(choice_axiom,[])).
% 1.61/0.58  fof(f34,plain,(
% 1.61/0.58    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 1.61/0.58    introduced(choice_axiom,[])).
% 1.61/0.58  fof(f35,plain,(
% 1.61/0.58    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))))),
% 1.61/0.58    introduced(choice_axiom,[])).
% 1.61/0.58  fof(f32,plain,(
% 1.61/0.58    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.61/0.58    inference(rectify,[],[f31])).
% 1.61/0.58  fof(f31,plain,(
% 1.61/0.58    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.61/0.58    inference(nnf_transformation,[],[f18])).
% 1.61/0.58  fof(f18,plain,(
% 1.61/0.58    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.61/0.58    inference(flattening,[],[f17])).
% 1.61/0.58  fof(f17,plain,(
% 1.61/0.58    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.61/0.58    inference(ennf_transformation,[],[f4])).
% 1.61/0.58  fof(f4,axiom,(
% 1.61/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.61/0.58  fof(f715,plain,(
% 1.61/0.58    r2_hidden(sK4(sK1,sK0),sK0) | sK0 = k2_relat_1(sK1) | sK1 = k6_relat_1(sK0)),
% 1.61/0.58    inference(factoring,[],[f454])).
% 1.61/0.58  fof(f454,plain,(
% 1.61/0.58    ( ! [X1] : (r2_hidden(sK4(sK1,X1),sK0) | k2_relat_1(sK1) = X1 | r2_hidden(sK4(sK1,X1),X1) | sK1 = k6_relat_1(sK0)) )),
% 1.61/0.58    inference(duplicate_literal_removal,[],[f449])).
% 1.61/0.58  fof(f449,plain,(
% 1.61/0.58    ( ! [X1] : (r2_hidden(sK4(sK1,X1),sK0) | k2_relat_1(sK1) = X1 | r2_hidden(sK4(sK1,X1),X1) | sK1 = k6_relat_1(sK0) | k2_relat_1(sK1) = X1 | r2_hidden(sK4(sK1,X1),X1)) )),
% 1.61/0.58    inference(superposition,[],[f248,f447])).
% 1.61/0.58  fof(f447,plain,(
% 1.61/0.58    ( ! [X1] : (sK5(sK1,X1) = sK4(sK1,X1) | sK1 = k6_relat_1(sK0) | k2_relat_1(sK1) = X1 | r2_hidden(sK4(sK1,X1),X1)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f120,f248])).
% 1.61/0.58  fof(f120,plain,(
% 1.61/0.58    ( ! [X1] : (sK5(sK1,X1) = sK4(sK1,X1) | ~r2_hidden(sK5(sK1,X1),sK0) | sK1 = k6_relat_1(sK0) | k2_relat_1(sK1) = X1 | r2_hidden(sK4(sK1,X1),X1)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f119,f37])).
% 1.61/0.58  fof(f119,plain,(
% 1.61/0.58    ( ! [X1] : (sK5(sK1,X1) = sK4(sK1,X1) | ~r2_hidden(sK5(sK1,X1),sK0) | sK1 = k6_relat_1(sK0) | k2_relat_1(sK1) = X1 | r2_hidden(sK4(sK1,X1),X1) | ~v1_relat_1(sK1)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f110,f38])).
% 1.61/0.58  fof(f110,plain,(
% 1.61/0.58    ( ! [X1] : (sK5(sK1,X1) = sK4(sK1,X1) | ~r2_hidden(sK5(sK1,X1),sK0) | sK1 = k6_relat_1(sK0) | k2_relat_1(sK1) = X1 | r2_hidden(sK4(sK1,X1),X1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.61/0.58    inference(superposition,[],[f40,f55])).
% 1.61/0.58  fof(f55,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) | r2_hidden(sK4(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f36])).
% 1.61/0.58  fof(f248,plain,(
% 1.61/0.58    ( ! [X4] : (r2_hidden(sK5(sK1,X4),sK0) | k2_relat_1(sK1) = X4 | r2_hidden(sK4(sK1,X4),X4)) )),
% 1.61/0.58    inference(forward_demodulation,[],[f95,f108])).
% 1.61/0.58  fof(f95,plain,(
% 1.61/0.58    ( ! [X4] : (k2_relat_1(sK1) = X4 | r2_hidden(sK5(sK1,X4),k1_relat_1(sK1)) | r2_hidden(sK4(sK1,X4),X4)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f82,f37])).
% 1.61/0.58  fof(f82,plain,(
% 1.61/0.58    ( ! [X4] : (k2_relat_1(sK1) = X4 | r2_hidden(sK5(sK1,X4),k1_relat_1(sK1)) | r2_hidden(sK4(sK1,X4),X4) | ~v1_relat_1(sK1)) )),
% 1.61/0.58    inference(resolution,[],[f38,f54])).
% 1.61/0.58  fof(f54,plain,(
% 1.61/0.58    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | r2_hidden(sK4(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f36])).
% 1.61/0.58  fof(f46,plain,(
% 1.61/0.58    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.61/0.58    inference(cnf_transformation,[],[f1])).
% 1.61/0.58  fof(f838,plain,(
% 1.61/0.58    ( ! [X4] : (~r2_hidden(X4,sK0) | k1_funct_1(k6_relat_1(k2_relat_1(sK1)),X4) = X4) )),
% 1.61/0.58    inference(backward_demodulation,[],[f558,f802])).
% 1.61/0.58  fof(f558,plain,(
% 1.61/0.58    ( ! [X4] : (k1_funct_1(k6_relat_1(k2_relat_1(sK1)),X4) = X4 | ~r2_hidden(X4,k2_relat_1(sK1))) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f541,f229])).
% 1.61/0.58  fof(f229,plain,(
% 1.61/0.58    ( ! [X15] : (r2_hidden(sK6(sK1,X15),sK0) | ~r2_hidden(X15,k2_relat_1(sK1))) )),
% 1.61/0.58    inference(forward_demodulation,[],[f103,f108])).
% 1.61/0.58  fof(f103,plain,(
% 1.61/0.58    ( ! [X15] : (r2_hidden(sK6(sK1,X15),k1_relat_1(sK1)) | ~r2_hidden(X15,k2_relat_1(sK1))) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f90,f37])).
% 1.61/0.58  fof(f90,plain,(
% 1.61/0.58    ( ! [X15] : (r2_hidden(sK6(sK1,X15),k1_relat_1(sK1)) | ~r2_hidden(X15,k2_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 1.61/0.58    inference(resolution,[],[f38,f62])).
% 1.61/0.58  fof(f62,plain,(
% 1.61/0.58    ( ! [X0,X5] : (r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.61/0.58    inference(equality_resolution,[],[f51])).
% 1.61/0.58  fof(f51,plain,(
% 1.61/0.58    ( ! [X0,X5,X1] : (r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f36])).
% 1.61/0.58  fof(f541,plain,(
% 1.61/0.58    ( ! [X4] : (k1_funct_1(k6_relat_1(k2_relat_1(sK1)),X4) = X4 | ~r2_hidden(sK6(sK1,X4),sK0) | ~r2_hidden(X4,k2_relat_1(sK1))) )),
% 1.61/0.58    inference(superposition,[],[f201,f102])).
% 1.61/0.58  fof(f102,plain,(
% 1.61/0.58    ( ! [X14] : (k1_funct_1(sK1,sK6(sK1,X14)) = X14 | ~r2_hidden(X14,k2_relat_1(sK1))) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f89,f37])).
% 1.61/0.58  fof(f89,plain,(
% 1.61/0.58    ( ! [X14] : (k1_funct_1(sK1,sK6(sK1,X14)) = X14 | ~r2_hidden(X14,k2_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 1.61/0.58    inference(resolution,[],[f38,f61])).
% 1.61/0.58  fof(f61,plain,(
% 1.61/0.58    ( ! [X0,X5] : (k1_funct_1(X0,sK6(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.61/0.58    inference(equality_resolution,[],[f52])).
% 1.61/0.58  fof(f52,plain,(
% 1.61/0.58    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK6(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f36])).
% 1.61/0.58  fof(f201,plain,(
% 1.61/0.58    ( ! [X0] : (k1_funct_1(sK1,X0) = k1_funct_1(k6_relat_1(k2_relat_1(sK1)),k1_funct_1(sK1,X0)) | ~r2_hidden(X0,sK0)) )),
% 1.61/0.58    inference(forward_demodulation,[],[f200,f108])).
% 1.61/0.58  fof(f200,plain,(
% 1.61/0.58    ( ! [X0] : (k1_funct_1(sK1,X0) = k1_funct_1(k6_relat_1(k2_relat_1(sK1)),k1_funct_1(sK1,X0)) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f199,f37])).
% 1.61/0.58  fof(f199,plain,(
% 1.61/0.58    ( ! [X0] : (k1_funct_1(sK1,X0) = k1_funct_1(k6_relat_1(k2_relat_1(sK1)),k1_funct_1(sK1,X0)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f198,f38])).
% 1.61/0.58  fof(f198,plain,(
% 1.61/0.58    ( ! [X0] : (k1_funct_1(sK1,X0) = k1_funct_1(k6_relat_1(k2_relat_1(sK1)),k1_funct_1(sK1,X0)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f197,f43])).
% 1.61/0.58  fof(f197,plain,(
% 1.61/0.58    ( ! [X0] : (k1_funct_1(sK1,X0) = k1_funct_1(k6_relat_1(k2_relat_1(sK1)),k1_funct_1(sK1,X0)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(k2_relat_1(sK1))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f188,f44])).
% 1.61/0.58  fof(f188,plain,(
% 1.61/0.58    ( ! [X0] : (k1_funct_1(sK1,X0) = k1_funct_1(k6_relat_1(k2_relat_1(sK1)),k1_funct_1(sK1,X0)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(k6_relat_1(k2_relat_1(sK1))) | ~v1_relat_1(k6_relat_1(k2_relat_1(sK1))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.61/0.58    inference(superposition,[],[f58,f63])).
% 1.61/0.58  fof(f63,plain,(
% 1.61/0.58    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))),
% 1.61/0.58    inference(resolution,[],[f37,f47])).
% 1.61/0.58  fof(f47,plain,(
% 1.61/0.58    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f13])).
% 1.61/0.58  fof(f13,plain,(
% 1.61/0.58    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.61/0.58    inference(ennf_transformation,[],[f3])).
% 1.61/0.58  fof(f3,axiom,(
% 1.61/0.58    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 1.61/0.58  fof(f58,plain,(
% 1.61/0.58    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f22])).
% 1.61/0.58  fof(f22,plain,(
% 1.61/0.58    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.61/0.58    inference(flattening,[],[f21])).
% 1.61/0.58  fof(f21,plain,(
% 1.61/0.58    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.61/0.58    inference(ennf_transformation,[],[f7])).
% 1.61/0.58  fof(f7,axiom,(
% 1.61/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 1.61/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 1.61/0.58  fof(f471,plain,(
% 1.61/0.58    ( ! [X5] : (sK3(X5,sK1) != k1_funct_1(X5,sK3(X5,sK1)) | sK0 != k1_relat_1(X5) | sK1 = X5 | ~v1_funct_1(X5) | ~v1_relat_1(X5) | ~r2_hidden(sK3(X5,sK1),sK0) | sK1 = k6_relat_1(sK0)) )),
% 1.61/0.58    inference(forward_demodulation,[],[f132,f108])).
% 1.61/0.58  fof(f132,plain,(
% 1.61/0.58    ( ! [X5] : (sK3(X5,sK1) != k1_funct_1(X5,sK3(X5,sK1)) | sK1 = X5 | k1_relat_1(sK1) != k1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(X5) | ~r2_hidden(sK3(X5,sK1),sK0) | sK1 = k6_relat_1(sK0)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f131,f37])).
% 1.61/0.58  fof(f131,plain,(
% 1.61/0.58    ( ! [X5] : (sK3(X5,sK1) != k1_funct_1(X5,sK3(X5,sK1)) | sK1 = X5 | k1_relat_1(sK1) != k1_relat_1(X5) | ~v1_relat_1(sK1) | ~v1_funct_1(X5) | ~v1_relat_1(X5) | ~r2_hidden(sK3(X5,sK1),sK0) | sK1 = k6_relat_1(sK0)) )),
% 1.61/0.58    inference(subsumption_resolution,[],[f116,f38])).
% 1.61/0.58  fof(f116,plain,(
% 1.61/0.58    ( ! [X5] : (sK3(X5,sK1) != k1_funct_1(X5,sK3(X5,sK1)) | sK1 = X5 | k1_relat_1(sK1) != k1_relat_1(X5) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(X5) | ~v1_relat_1(X5) | ~r2_hidden(sK3(X5,sK1),sK0) | sK1 = k6_relat_1(sK0)) )),
% 1.61/0.58    inference(superposition,[],[f50,f40])).
% 1.61/0.58  fof(f50,plain,(
% 1.61/0.58    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.61/0.58    inference(cnf_transformation,[],[f30])).
% 1.61/0.58  fof(f150,plain,(
% 1.61/0.58    sK1 != k6_relat_1(sK0) | r2_hidden(sK2,sK0)),
% 1.61/0.58    inference(trivial_inequality_removal,[],[f137])).
% 1.61/0.58  fof(f137,plain,(
% 1.61/0.58    sK0 != sK0 | sK1 != k6_relat_1(sK0) | r2_hidden(sK2,sK0)),
% 1.61/0.58    inference(backward_demodulation,[],[f41,f108])).
% 1.61/0.58  fof(f41,plain,(
% 1.61/0.58    sK1 != k6_relat_1(sK0) | sK0 != k1_relat_1(sK1) | r2_hidden(sK2,sK0)),
% 1.61/0.58    inference(cnf_transformation,[],[f28])).
% 1.61/0.58  fof(f1199,plain,(
% 1.61/0.58    ~r2_hidden(sK2,sK0)),
% 1.61/0.58    inference(trivial_inequality_removal,[],[f1184])).
% 1.61/0.58  fof(f1184,plain,(
% 1.61/0.58    sK2 != sK2 | ~r2_hidden(sK2,sK0)),
% 1.61/0.58    inference(superposition,[],[f1127,f1121])).
% 1.61/0.58  fof(f1121,plain,(
% 1.61/0.58    ( ! [X4] : (k1_funct_1(sK1,X4) = X4 | ~r2_hidden(X4,sK0)) )),
% 1.61/0.58    inference(backward_demodulation,[],[f852,f1087])).
% 1.61/0.58  fof(f1127,plain,(
% 1.61/0.58    sK2 != k1_funct_1(sK1,sK2)),
% 1.61/0.58    inference(trivial_inequality_removal,[],[f1117])).
% 1.61/0.58  fof(f1117,plain,(
% 1.61/0.58    sK1 != sK1 | sK2 != k1_funct_1(sK1,sK2)),
% 1.61/0.58    inference(backward_demodulation,[],[f176,f1087])).
% 1.61/0.58  fof(f176,plain,(
% 1.61/0.58    sK2 != k1_funct_1(sK1,sK2) | sK1 != k6_relat_1(sK0)),
% 1.61/0.58    inference(subsumption_resolution,[],[f42,f108])).
% 1.61/0.58  fof(f42,plain,(
% 1.61/0.58    sK2 != k1_funct_1(sK1,sK2) | sK0 != k1_relat_1(sK1) | sK1 != k6_relat_1(sK0)),
% 1.61/0.58    inference(cnf_transformation,[],[f28])).
% 1.61/0.58  % SZS output end Proof for theBenchmark
% 1.61/0.58  % (1520)------------------------------
% 1.61/0.58  % (1520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (1520)Termination reason: Refutation
% 1.61/0.58  
% 1.61/0.58  % (1520)Memory used [KB]: 2046
% 1.61/0.58  % (1520)Time elapsed: 0.139 s
% 1.61/0.58  % (1520)------------------------------
% 1.61/0.58  % (1520)------------------------------
% 1.61/0.58  % (1501)Success in time 0.219 s
%------------------------------------------------------------------------------
