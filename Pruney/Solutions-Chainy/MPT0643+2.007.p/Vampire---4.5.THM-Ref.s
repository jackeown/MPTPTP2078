%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:40 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 356 expanded)
%              Number of leaves         :   10 ( 109 expanded)
%              Depth                    :   29
%              Number of atoms          :  406 (3318 expanded)
%              Number of equality atoms :  154 (1393 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f310,plain,(
    $false ),
    inference(subsumption_resolution,[],[f309,f79])).

fof(f79,plain,(
    sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f78,f34])).

fof(f34,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k6_relat_1(sK0) != sK2
    & sK1 = k5_relat_1(sK2,sK1)
    & v2_funct_1(sK1)
    & r1_tarski(k2_relat_1(sK2),sK0)
    & sK0 = k1_relat_1(sK2)
    & sK0 = k1_relat_1(sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k6_relat_1(X0) != X2
            & k5_relat_1(X2,X1) = X1
            & v2_funct_1(X1)
            & r1_tarski(k2_relat_1(X2),X0)
            & k1_relat_1(X2) = X0
            & k1_relat_1(X1) = X0
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k6_relat_1(sK0) != X2
          & sK1 = k5_relat_1(X2,sK1)
          & v2_funct_1(sK1)
          & r1_tarski(k2_relat_1(X2),sK0)
          & k1_relat_1(X2) = sK0
          & sK0 = k1_relat_1(sK1)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( k6_relat_1(sK0) != X2
        & sK1 = k5_relat_1(X2,sK1)
        & v2_funct_1(sK1)
        & r1_tarski(k2_relat_1(X2),sK0)
        & k1_relat_1(X2) = sK0
        & sK0 = k1_relat_1(sK1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k6_relat_1(sK0) != sK2
      & sK1 = k5_relat_1(sK2,sK1)
      & v2_funct_1(sK1)
      & r1_tarski(k2_relat_1(sK2),sK0)
      & sK0 = k1_relat_1(sK2)
      & sK0 = k1_relat_1(sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k6_relat_1(X0) != X2
          & k5_relat_1(X2,X1) = X1
          & v2_funct_1(X1)
          & r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X0
          & k1_relat_1(X1) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( k5_relat_1(X2,X1) = X1
                & v2_funct_1(X1)
                & r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X0
                & k1_relat_1(X1) = X0 )
             => k6_relat_1(X0) = X2 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k5_relat_1(X2,X1) = X1
              & v2_funct_1(X1)
              & r1_tarski(k2_relat_1(X2),X0)
              & k1_relat_1(X2) = X0
              & k1_relat_1(X1) = X0 )
           => k6_relat_1(X0) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).

fof(f78,plain,
    ( sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f77,f35])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,
    ( sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f74,f41])).

fof(f41,plain,(
    k6_relat_1(sK0) != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f74,plain,
    ( sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2))
    | k6_relat_1(sK0) = sK2
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f54,f37])).

fof(f37,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    ! [X1] :
      ( sK3(k1_relat_1(X1),X1) != k1_funct_1(X1,sK3(k1_relat_1(X1),X1))
      | k6_relat_1(k1_relat_1(X1)) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1))
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1))
            & r2_hidden(sK3(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f309,plain,(
    sK3(sK0,sK2) = k1_funct_1(sK2,sK3(sK0,sK2)) ),
    inference(trivial_inequality_removal,[],[f305])).

fof(f305,plain,
    ( k1_funct_1(sK1,sK3(sK0,sK2)) != k1_funct_1(sK1,sK3(sK0,sK2))
    | sK3(sK0,sK2) = k1_funct_1(sK2,sK3(sK0,sK2)) ),
    inference(resolution,[],[f303,f72])).

fof(f72,plain,(
    r2_hidden(sK3(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f71,f34])).

fof(f71,plain,
    ( r2_hidden(sK3(sK0,sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f70,f35])).

fof(f70,plain,
    ( r2_hidden(sK3(sK0,sK2),sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f67,f41])).

fof(f67,plain,
    ( r2_hidden(sK3(sK0,sK2),sK0)
    | k6_relat_1(sK0) = sK2
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f55,f37])).

fof(f55,plain,(
    ! [X1] :
      ( r2_hidden(sK3(k1_relat_1(X1),X1),k1_relat_1(X1))
      | k6_relat_1(k1_relat_1(X1)) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK3(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f303,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2))
      | k1_funct_1(sK2,sK3(sK0,sK2)) = X0 ) ),
    inference(subsumption_resolution,[],[f302,f72])).

fof(f302,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK0,sK2),sK0)
      | k1_funct_1(sK2,sK3(sK0,sK2)) = X0
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(forward_demodulation,[],[f301,f37])).

fof(f301,plain,(
    ! [X0] :
      ( k1_funct_1(sK2,sK3(sK0,sK2)) = X0
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2))
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(sK3(sK0,sK2),k1_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f300,f34])).

fof(f300,plain,(
    ! [X0] :
      ( k1_funct_1(sK2,sK3(sK0,sK2)) = X0
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2))
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(sK3(sK0,sK2),k1_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f298,f35])).

fof(f298,plain,(
    ! [X0] :
      ( k1_funct_1(sK2,sK3(sK0,sK2)) = X0
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2))
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(sK3(sK0,sK2),k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f297,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f297,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),k2_relat_1(sK2))
      | k1_funct_1(sK2,sK3(sK0,sK2)) = X0
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f264,f38])).

fof(f38,plain,(
    r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f264,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2))
      | k1_funct_1(sK2,sK3(sK0,sK2)) = X0
      | ~ r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),X1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f105,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f105,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),sK0)
      | ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2))
      | k1_funct_1(sK2,sK3(sK0,sK2)) = X0 ) ),
    inference(forward_demodulation,[],[f104,f36])).

fof(f36,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f104,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2))
      | k1_funct_1(sK2,sK3(sK0,sK2)) = X0
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(forward_demodulation,[],[f103,f36])).

fof(f103,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2))
      | k1_funct_1(sK2,sK3(sK0,sK2)) = X0
      | ~ r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),k1_relat_1(sK1))
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f102,f32])).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f102,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2))
      | k1_funct_1(sK2,sK3(sK0,sK2)) = X0
      | ~ r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),k1_relat_1(sK1))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f101,f33])).

fof(f33,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f101,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2))
      | k1_funct_1(sK2,sK3(sK0,sK2)) = X0
      | ~ r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),k1_relat_1(sK1))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f98,f39])).

fof(f39,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f98,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2))
      | k1_funct_1(sK2,sK3(sK0,sK2)) = X0
      | ~ r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),k1_relat_1(sK1))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v2_funct_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f47,f94])).

fof(f94,plain,(
    k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) = k1_funct_1(sK1,sK3(sK0,sK2)) ),
    inference(resolution,[],[f92,f72])).

fof(f92,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | k1_funct_1(sK1,k1_funct_1(sK2,X1)) = k1_funct_1(sK1,X1) ) ),
    inference(forward_demodulation,[],[f91,f40])).

fof(f40,plain,(
    sK1 = k5_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f91,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | k1_funct_1(k5_relat_1(sK2,sK1),X1) = k1_funct_1(sK1,k1_funct_1(sK2,X1)) ) ),
    inference(forward_demodulation,[],[f90,f36])).

fof(f90,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK1))
      | k1_funct_1(k5_relat_1(sK2,sK1),X1) = k1_funct_1(sK1,k1_funct_1(sK2,X1)) ) ),
    inference(forward_demodulation,[],[f89,f40])).

fof(f89,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k5_relat_1(sK2,sK1)))
      | k1_funct_1(k5_relat_1(sK2,sK1),X1) = k1_funct_1(sK1,k1_funct_1(sK2,X1)) ) ),
    inference(subsumption_resolution,[],[f87,f34])).

fof(f87,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k5_relat_1(sK2,sK1)))
      | ~ v1_relat_1(sK2)
      | k1_funct_1(k5_relat_1(sK2,sK1),X1) = k1_funct_1(sK1,k1_funct_1(sK2,X1)) ) ),
    inference(resolution,[],[f84,f35])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,sK1)))
      | ~ v1_relat_1(X1)
      | k1_funct_1(k5_relat_1(X1,sK1),X0) = k1_funct_1(sK1,k1_funct_1(X1,X0)) ) ),
    inference(subsumption_resolution,[],[f82,f32])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X1,sK1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k5_relat_1(X1,sK1),X0) = k1_funct_1(sK1,k1_funct_1(X1,X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f46,f33])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(f47,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f29,f30])).

fof(f30,plain,(
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

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:11:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (25285)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (25301)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (25309)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.46/0.57  % (25285)Refutation found. Thanks to Tanya!
% 1.46/0.57  % SZS status Theorem for theBenchmark
% 1.46/0.57  % SZS output start Proof for theBenchmark
% 1.46/0.57  fof(f310,plain,(
% 1.46/0.57    $false),
% 1.46/0.57    inference(subsumption_resolution,[],[f309,f79])).
% 1.46/0.57  fof(f79,plain,(
% 1.46/0.57    sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2))),
% 1.46/0.57    inference(subsumption_resolution,[],[f78,f34])).
% 1.46/0.57  fof(f34,plain,(
% 1.46/0.57    v1_relat_1(sK2)),
% 1.46/0.57    inference(cnf_transformation,[],[f22])).
% 1.46/0.57  fof(f22,plain,(
% 1.46/0.57    (k6_relat_1(sK0) != sK2 & sK1 = k5_relat_1(sK2,sK1) & v2_funct_1(sK1) & r1_tarski(k2_relat_1(sK2),sK0) & sK0 = k1_relat_1(sK2) & sK0 = k1_relat_1(sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.46/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f21,f20])).
% 1.46/0.57  fof(f20,plain,(
% 1.46/0.57    ? [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k6_relat_1(sK0) != X2 & sK1 = k5_relat_1(X2,sK1) & v2_funct_1(sK1) & r1_tarski(k2_relat_1(X2),sK0) & k1_relat_1(X2) = sK0 & sK0 = k1_relat_1(sK1) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.46/0.57    introduced(choice_axiom,[])).
% 1.46/0.57  fof(f21,plain,(
% 1.46/0.57    ? [X2] : (k6_relat_1(sK0) != X2 & sK1 = k5_relat_1(X2,sK1) & v2_funct_1(sK1) & r1_tarski(k2_relat_1(X2),sK0) & k1_relat_1(X2) = sK0 & sK0 = k1_relat_1(sK1) & v1_funct_1(X2) & v1_relat_1(X2)) => (k6_relat_1(sK0) != sK2 & sK1 = k5_relat_1(sK2,sK1) & v2_funct_1(sK1) & r1_tarski(k2_relat_1(sK2),sK0) & sK0 = k1_relat_1(sK2) & sK0 = k1_relat_1(sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.46/0.57    introduced(choice_axiom,[])).
% 1.46/0.57  fof(f10,plain,(
% 1.46/0.57    ? [X0,X1] : (? [X2] : (k6_relat_1(X0) != X2 & k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.46/0.57    inference(flattening,[],[f9])).
% 1.46/0.57  fof(f9,plain,(
% 1.46/0.57    ? [X0,X1] : (? [X2] : ((k6_relat_1(X0) != X2 & (k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0)) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.46/0.57    inference(ennf_transformation,[],[f7])).
% 1.46/0.57  fof(f7,negated_conjecture,(
% 1.46/0.57    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 1.46/0.57    inference(negated_conjecture,[],[f6])).
% 1.46/0.57  fof(f6,conjecture,(
% 1.46/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X2,X1) = X1 & v2_funct_1(X1) & r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => k6_relat_1(X0) = X2)))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).
% 1.46/0.57  fof(f78,plain,(
% 1.46/0.57    sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2)) | ~v1_relat_1(sK2)),
% 1.46/0.57    inference(subsumption_resolution,[],[f77,f35])).
% 1.46/0.57  fof(f35,plain,(
% 1.46/0.57    v1_funct_1(sK2)),
% 1.46/0.57    inference(cnf_transformation,[],[f22])).
% 1.46/0.57  fof(f77,plain,(
% 1.46/0.57    sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.46/0.57    inference(subsumption_resolution,[],[f74,f41])).
% 1.46/0.57  fof(f41,plain,(
% 1.46/0.57    k6_relat_1(sK0) != sK2),
% 1.46/0.57    inference(cnf_transformation,[],[f22])).
% 1.46/0.57  fof(f74,plain,(
% 1.46/0.57    sK3(sK0,sK2) != k1_funct_1(sK2,sK3(sK0,sK2)) | k6_relat_1(sK0) = sK2 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.46/0.57    inference(superposition,[],[f54,f37])).
% 1.46/0.57  fof(f37,plain,(
% 1.46/0.57    sK0 = k1_relat_1(sK2)),
% 1.46/0.57    inference(cnf_transformation,[],[f22])).
% 1.46/0.57  fof(f54,plain,(
% 1.46/0.57    ( ! [X1] : (sK3(k1_relat_1(X1),X1) != k1_funct_1(X1,sK3(k1_relat_1(X1),X1)) | k6_relat_1(k1_relat_1(X1)) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.46/0.57    inference(equality_resolution,[],[f45])).
% 1.46/0.57  fof(f45,plain,(
% 1.46/0.57    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1)) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f27])).
% 1.46/0.57  fof(f27,plain,(
% 1.46/0.57    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.46/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).
% 1.46/0.57  fof(f26,plain,(
% 1.46/0.57    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (sK3(X0,X1) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 1.46/0.57    introduced(choice_axiom,[])).
% 1.46/0.57  fof(f25,plain,(
% 1.46/0.57    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.46/0.57    inference(rectify,[],[f24])).
% 1.46/0.57  fof(f24,plain,(
% 1.46/0.57    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.46/0.57    inference(flattening,[],[f23])).
% 1.46/0.57  fof(f23,plain,(
% 1.46/0.57    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.46/0.57    inference(nnf_transformation,[],[f12])).
% 1.46/0.57  fof(f12,plain,(
% 1.46/0.57    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.46/0.57    inference(flattening,[],[f11])).
% 1.46/0.57  fof(f11,plain,(
% 1.46/0.57    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.46/0.57    inference(ennf_transformation,[],[f5])).
% 1.46/0.57  fof(f5,axiom,(
% 1.46/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 1.46/0.57  fof(f309,plain,(
% 1.46/0.57    sK3(sK0,sK2) = k1_funct_1(sK2,sK3(sK0,sK2))),
% 1.46/0.57    inference(trivial_inequality_removal,[],[f305])).
% 1.46/0.57  fof(f305,plain,(
% 1.46/0.57    k1_funct_1(sK1,sK3(sK0,sK2)) != k1_funct_1(sK1,sK3(sK0,sK2)) | sK3(sK0,sK2) = k1_funct_1(sK2,sK3(sK0,sK2))),
% 1.46/0.57    inference(resolution,[],[f303,f72])).
% 1.46/0.57  fof(f72,plain,(
% 1.46/0.57    r2_hidden(sK3(sK0,sK2),sK0)),
% 1.46/0.57    inference(subsumption_resolution,[],[f71,f34])).
% 1.46/0.57  fof(f71,plain,(
% 1.46/0.57    r2_hidden(sK3(sK0,sK2),sK0) | ~v1_relat_1(sK2)),
% 1.46/0.57    inference(subsumption_resolution,[],[f70,f35])).
% 1.46/0.57  fof(f70,plain,(
% 1.46/0.57    r2_hidden(sK3(sK0,sK2),sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.46/0.57    inference(subsumption_resolution,[],[f67,f41])).
% 1.46/0.57  fof(f67,plain,(
% 1.46/0.57    r2_hidden(sK3(sK0,sK2),sK0) | k6_relat_1(sK0) = sK2 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.46/0.57    inference(superposition,[],[f55,f37])).
% 1.46/0.57  fof(f55,plain,(
% 1.46/0.57    ( ! [X1] : (r2_hidden(sK3(k1_relat_1(X1),X1),k1_relat_1(X1)) | k6_relat_1(k1_relat_1(X1)) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.46/0.57    inference(equality_resolution,[],[f44])).
% 1.46/0.57  fof(f44,plain,(
% 1.46/0.57    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK3(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f27])).
% 1.46/0.57  fof(f303,plain,(
% 1.46/0.57    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2)) | k1_funct_1(sK2,sK3(sK0,sK2)) = X0) )),
% 1.46/0.57    inference(subsumption_resolution,[],[f302,f72])).
% 1.46/0.57  fof(f302,plain,(
% 1.46/0.57    ( ! [X0] : (~r2_hidden(sK3(sK0,sK2),sK0) | k1_funct_1(sK2,sK3(sK0,sK2)) = X0 | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2)) | ~r2_hidden(X0,sK0)) )),
% 1.46/0.57    inference(forward_demodulation,[],[f301,f37])).
% 1.46/0.57  fof(f301,plain,(
% 1.46/0.57    ( ! [X0] : (k1_funct_1(sK2,sK3(sK0,sK2)) = X0 | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2)) | ~r2_hidden(X0,sK0) | ~r2_hidden(sK3(sK0,sK2),k1_relat_1(sK2))) )),
% 1.46/0.57    inference(subsumption_resolution,[],[f300,f34])).
% 1.46/0.57  fof(f300,plain,(
% 1.46/0.57    ( ! [X0] : (k1_funct_1(sK2,sK3(sK0,sK2)) = X0 | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2)) | ~r2_hidden(X0,sK0) | ~r2_hidden(sK3(sK0,sK2),k1_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 1.46/0.57    inference(subsumption_resolution,[],[f298,f35])).
% 1.46/0.57  fof(f298,plain,(
% 1.46/0.57    ( ! [X0] : (k1_funct_1(sK2,sK3(sK0,sK2)) = X0 | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2)) | ~r2_hidden(X0,sK0) | ~r2_hidden(sK3(sK0,sK2),k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.46/0.57    inference(resolution,[],[f297,f53])).
% 1.46/0.57  fof(f53,plain,(
% 1.46/0.57    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f19])).
% 1.46/0.57  fof(f19,plain,(
% 1.46/0.57    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.46/0.57    inference(flattening,[],[f18])).
% 1.46/0.57  fof(f18,plain,(
% 1.46/0.57    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.46/0.57    inference(ennf_transformation,[],[f3])).
% 1.46/0.57  fof(f3,axiom,(
% 1.46/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 1.46/0.57  fof(f297,plain,(
% 1.46/0.57    ( ! [X0] : (~r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),k2_relat_1(sK2)) | k1_funct_1(sK2,sK3(sK0,sK2)) = X0 | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2)) | ~r2_hidden(X0,sK0)) )),
% 1.46/0.57    inference(resolution,[],[f264,f38])).
% 1.46/0.57  fof(f38,plain,(
% 1.46/0.57    r1_tarski(k2_relat_1(sK2),sK0)),
% 1.46/0.57    inference(cnf_transformation,[],[f22])).
% 1.46/0.57  fof(f264,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~r1_tarski(X1,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2)) | k1_funct_1(sK2,sK3(sK0,sK2)) = X0 | ~r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),X1) | ~r2_hidden(X0,sK0)) )),
% 1.46/0.57    inference(resolution,[],[f105,f52])).
% 1.46/0.57  fof(f52,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f17])).
% 1.46/0.57  fof(f17,plain,(
% 1.46/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.46/0.57    inference(ennf_transformation,[],[f8])).
% 1.46/0.57  fof(f8,plain,(
% 1.46/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.46/0.57    inference(unused_predicate_definition_removal,[],[f1])).
% 1.46/0.57  fof(f1,axiom,(
% 1.46/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.46/0.57  fof(f105,plain,(
% 1.46/0.57    ( ! [X0] : (~r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),sK0) | ~r2_hidden(X0,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2)) | k1_funct_1(sK2,sK3(sK0,sK2)) = X0) )),
% 1.46/0.57    inference(forward_demodulation,[],[f104,f36])).
% 1.46/0.57  fof(f36,plain,(
% 1.46/0.57    sK0 = k1_relat_1(sK1)),
% 1.46/0.57    inference(cnf_transformation,[],[f22])).
% 1.46/0.57  fof(f104,plain,(
% 1.46/0.57    ( ! [X0] : (~r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2)) | k1_funct_1(sK2,sK3(sK0,sK2)) = X0 | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 1.46/0.57    inference(forward_demodulation,[],[f103,f36])).
% 1.46/0.57  fof(f103,plain,(
% 1.46/0.57    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2)) | k1_funct_1(sK2,sK3(sK0,sK2)) = X0 | ~r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 1.46/0.57    inference(subsumption_resolution,[],[f102,f32])).
% 1.46/0.57  fof(f32,plain,(
% 1.46/0.57    v1_relat_1(sK1)),
% 1.46/0.57    inference(cnf_transformation,[],[f22])).
% 1.46/0.57  fof(f102,plain,(
% 1.46/0.57    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2)) | k1_funct_1(sK2,sK3(sK0,sK2)) = X0 | ~r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 1.46/0.57    inference(subsumption_resolution,[],[f101,f33])).
% 1.46/0.57  fof(f33,plain,(
% 1.46/0.57    v1_funct_1(sK1)),
% 1.46/0.57    inference(cnf_transformation,[],[f22])).
% 1.46/0.57  fof(f101,plain,(
% 1.46/0.57    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2)) | k1_funct_1(sK2,sK3(sK0,sK2)) = X0 | ~r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.46/0.57    inference(subsumption_resolution,[],[f98,f39])).
% 1.46/0.57  fof(f39,plain,(
% 1.46/0.57    v2_funct_1(sK1)),
% 1.46/0.57    inference(cnf_transformation,[],[f22])).
% 1.46/0.57  fof(f98,plain,(
% 1.46/0.57    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK3(sK0,sK2)) | k1_funct_1(sK2,sK3(sK0,sK2)) = X0 | ~r2_hidden(k1_funct_1(sK2,sK3(sK0,sK2)),k1_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.46/0.57    inference(superposition,[],[f47,f94])).
% 1.46/0.57  fof(f94,plain,(
% 1.46/0.57    k1_funct_1(sK1,k1_funct_1(sK2,sK3(sK0,sK2))) = k1_funct_1(sK1,sK3(sK0,sK2))),
% 1.46/0.57    inference(resolution,[],[f92,f72])).
% 1.46/0.57  fof(f92,plain,(
% 1.46/0.57    ( ! [X1] : (~r2_hidden(X1,sK0) | k1_funct_1(sK1,k1_funct_1(sK2,X1)) = k1_funct_1(sK1,X1)) )),
% 1.46/0.57    inference(forward_demodulation,[],[f91,f40])).
% 1.46/0.57  fof(f40,plain,(
% 1.46/0.57    sK1 = k5_relat_1(sK2,sK1)),
% 1.46/0.57    inference(cnf_transformation,[],[f22])).
% 1.46/0.57  fof(f91,plain,(
% 1.46/0.57    ( ! [X1] : (~r2_hidden(X1,sK0) | k1_funct_1(k5_relat_1(sK2,sK1),X1) = k1_funct_1(sK1,k1_funct_1(sK2,X1))) )),
% 1.46/0.57    inference(forward_demodulation,[],[f90,f36])).
% 1.46/0.57  fof(f90,plain,(
% 1.46/0.57    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | k1_funct_1(k5_relat_1(sK2,sK1),X1) = k1_funct_1(sK1,k1_funct_1(sK2,X1))) )),
% 1.46/0.57    inference(forward_demodulation,[],[f89,f40])).
% 1.46/0.57  fof(f89,plain,(
% 1.46/0.57    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(k5_relat_1(sK2,sK1))) | k1_funct_1(k5_relat_1(sK2,sK1),X1) = k1_funct_1(sK1,k1_funct_1(sK2,X1))) )),
% 1.46/0.57    inference(subsumption_resolution,[],[f87,f34])).
% 1.46/0.57  fof(f87,plain,(
% 1.46/0.57    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(k5_relat_1(sK2,sK1))) | ~v1_relat_1(sK2) | k1_funct_1(k5_relat_1(sK2,sK1),X1) = k1_funct_1(sK1,k1_funct_1(sK2,X1))) )),
% 1.46/0.57    inference(resolution,[],[f84,f35])).
% 1.46/0.57  fof(f84,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X1,sK1))) | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(X1,sK1),X0) = k1_funct_1(sK1,k1_funct_1(X1,X0))) )),
% 1.46/0.57    inference(subsumption_resolution,[],[f82,f32])).
% 1.46/0.57  fof(f82,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X1,sK1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_funct_1(k5_relat_1(X1,sK1),X0) = k1_funct_1(sK1,k1_funct_1(X1,X0)) | ~v1_relat_1(sK1)) )),
% 1.46/0.57    inference(resolution,[],[f46,f33])).
% 1.46/0.57  fof(f46,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~v1_relat_1(X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f14])).
% 1.46/0.57  fof(f14,plain,(
% 1.46/0.57    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.46/0.57    inference(flattening,[],[f13])).
% 1.46/0.57  fof(f13,plain,(
% 1.46/0.57    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.46/0.57    inference(ennf_transformation,[],[f4])).
% 1.46/0.57  fof(f4,axiom,(
% 1.46/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).
% 1.46/0.57  fof(f47,plain,(
% 1.46/0.57    ( ! [X4,X0,X3] : (k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | X3 = X4 | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f31])).
% 1.46/0.57  fof(f31,plain,(
% 1.46/0.57    ! [X0] : (((v2_funct_1(X0) | (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f29,f30])).
% 1.46/0.57  fof(f30,plain,(
% 1.46/0.57    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK4(X0) != sK5(X0) & k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) & r2_hidden(sK5(X0),k1_relat_1(X0)) & r2_hidden(sK4(X0),k1_relat_1(X0))))),
% 1.46/0.57    introduced(choice_axiom,[])).
% 1.46/0.57  fof(f29,plain,(
% 1.46/0.57    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.57    inference(rectify,[],[f28])).
% 1.46/0.57  fof(f28,plain,(
% 1.46/0.57    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.57    inference(nnf_transformation,[],[f16])).
% 1.46/0.57  fof(f16,plain,(
% 1.46/0.57    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.57    inference(flattening,[],[f15])).
% 1.46/0.57  fof(f15,plain,(
% 1.46/0.57    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.46/0.57    inference(ennf_transformation,[],[f2])).
% 1.46/0.57  fof(f2,axiom,(
% 1.46/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
% 1.46/0.57  % SZS output end Proof for theBenchmark
% 1.46/0.57  % (25285)------------------------------
% 1.46/0.57  % (25285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % (25285)Termination reason: Refutation
% 1.46/0.57  
% 1.46/0.57  % (25285)Memory used [KB]: 6524
% 1.46/0.57  % (25285)Time elapsed: 0.144 s
% 1.46/0.57  % (25285)------------------------------
% 1.46/0.57  % (25285)------------------------------
% 1.46/0.58  % (25272)Success in time 0.208 s
%------------------------------------------------------------------------------
