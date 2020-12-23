%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:11 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 120 expanded)
%              Number of leaves         :   10 (  29 expanded)
%              Depth                    :   14
%              Number of atoms          :  258 ( 497 expanded)
%              Number of equality atoms :   74 ( 123 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f207,plain,(
    $false ),
    inference(subsumption_resolution,[],[f206,f33])).

fof(f33,plain,(
    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    & r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
        & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
      & r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
         => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

fof(f206,plain,(
    k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(forward_demodulation,[],[f201,f109])).

fof(f109,plain,(
    sK0 = k1_funct_1(k6_relat_1(sK1),sK0) ),
    inference(resolution,[],[f103,f68])).

fof(f68,plain,(
    r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f66,f32])).

fof(f32,plain,(
    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1)))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f46,f30])).

fof(f30,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k1_funct_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(resolution,[],[f80,f57])).

fof(f57,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0) ) ),
    inference(subsumption_resolution,[],[f53,f34])).

fof(f34,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f53,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | X4 != X5
      | ~ r2_hidden(X4,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK3(X0,X1) != sK4(X0,X1)
              | ~ r2_hidden(sK3(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
            & ( ( sK3(X0,X1) = sK4(X0,X1)
                & r2_hidden(sK3(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK3(X0,X1) != sK4(X0,X1)
          | ~ r2_hidden(sK3(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & ( ( sK3(X0,X1) = sK4(X0,X1)
            & r2_hidden(sK3(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).

fof(f80,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k6_relat_1(X4))
      | k1_funct_1(k6_relat_1(X4),X2) = X3 ) ),
    inference(subsumption_resolution,[],[f78,f34])).

fof(f78,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k6_relat_1(X4))
      | k1_funct_1(k6_relat_1(X4),X2) = X3
      | ~ v1_relat_1(k6_relat_1(X4)) ) ),
    inference(resolution,[],[f50,f35])).

fof(f35,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f201,plain,(
    k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)) ),
    inference(resolution,[],[f132,f68])).

fof(f132,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,X1)
      | k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k7_relat_1(sK2,X1),X2) ) ),
    inference(forward_demodulation,[],[f131,f36])).

fof(f36,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f131,plain,(
    ! [X2,X1] :
      ( k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k7_relat_1(sK2,X1),X2)
      | ~ r2_hidden(X2,k1_relat_1(k6_relat_1(X1))) ) ),
    inference(forward_demodulation,[],[f130,f64])).

fof(f64,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2) ),
    inference(resolution,[],[f38,f30])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f130,plain,(
    ! [X2,X1] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(X1),sK2),X2) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2))
      | ~ r2_hidden(X2,k1_relat_1(k6_relat_1(X1))) ) ),
    inference(subsumption_resolution,[],[f128,f34])).

fof(f128,plain,(
    ! [X2,X1] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(X1),sK2),X2) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2))
      | ~ r2_hidden(X2,k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(resolution,[],[f97,f35])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k1_funct_1(k5_relat_1(X1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f95,f30])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k5_relat_1(X1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(X1,X0))
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f45,f31])).

fof(f31,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:29:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (1220050944)
% 0.14/0.37  ipcrm: permission denied for id (1222180866)
% 0.14/0.37  ipcrm: permission denied for id (1222213635)
% 0.14/0.38  ipcrm: permission denied for id (1222246404)
% 0.14/0.38  ipcrm: permission denied for id (1222279173)
% 0.14/0.38  ipcrm: permission denied for id (1225588744)
% 0.14/0.38  ipcrm: permission denied for id (1225621513)
% 0.14/0.38  ipcrm: permission denied for id (1222443018)
% 0.22/0.38  ipcrm: permission denied for id (1222475787)
% 0.22/0.38  ipcrm: permission denied for id (1222508556)
% 0.22/0.39  ipcrm: permission denied for id (1222541325)
% 0.22/0.39  ipcrm: permission denied for id (1225654286)
% 0.22/0.39  ipcrm: permission denied for id (1225687055)
% 0.22/0.39  ipcrm: permission denied for id (1225752593)
% 0.22/0.39  ipcrm: permission denied for id (1225785362)
% 0.22/0.39  ipcrm: permission denied for id (1222737939)
% 0.22/0.39  ipcrm: permission denied for id (1225850901)
% 0.22/0.40  ipcrm: permission denied for id (1222869014)
% 0.22/0.40  ipcrm: permission denied for id (1222901783)
% 0.22/0.40  ipcrm: permission denied for id (1222934552)
% 0.22/0.40  ipcrm: permission denied for id (1222967321)
% 0.22/0.40  ipcrm: permission denied for id (1223000090)
% 0.22/0.40  ipcrm: permission denied for id (1223032859)
% 0.22/0.40  ipcrm: permission denied for id (1225883676)
% 0.22/0.40  ipcrm: permission denied for id (1225916445)
% 0.22/0.40  ipcrm: permission denied for id (1223131166)
% 0.22/0.41  ipcrm: permission denied for id (1225949215)
% 0.22/0.41  ipcrm: permission denied for id (1225981984)
% 0.22/0.41  ipcrm: permission denied for id (1223229473)
% 0.22/0.41  ipcrm: permission denied for id (1223262242)
% 0.22/0.41  ipcrm: permission denied for id (1223360549)
% 0.22/0.42  ipcrm: permission denied for id (1223491625)
% 0.22/0.42  ipcrm: permission denied for id (1220706347)
% 0.22/0.42  ipcrm: permission denied for id (1223557164)
% 0.22/0.42  ipcrm: permission denied for id (1223589933)
% 0.22/0.42  ipcrm: permission denied for id (1223622702)
% 0.22/0.42  ipcrm: permission denied for id (1220771887)
% 0.22/0.42  ipcrm: permission denied for id (1223655472)
% 0.22/0.42  ipcrm: permission denied for id (1220804657)
% 0.22/0.43  ipcrm: permission denied for id (1226211378)
% 0.22/0.43  ipcrm: permission denied for id (1220837427)
% 0.22/0.43  ipcrm: permission denied for id (1220870197)
% 0.22/0.43  ipcrm: permission denied for id (1226309687)
% 0.22/0.43  ipcrm: permission denied for id (1223819320)
% 0.22/0.43  ipcrm: permission denied for id (1220935737)
% 0.22/0.43  ipcrm: permission denied for id (1220968506)
% 0.22/0.43  ipcrm: permission denied for id (1223852091)
% 0.22/0.44  ipcrm: permission denied for id (1221001276)
% 0.22/0.44  ipcrm: permission denied for id (1221034045)
% 0.22/0.44  ipcrm: permission denied for id (1221066816)
% 0.22/0.44  ipcrm: permission denied for id (1221099586)
% 0.22/0.44  ipcrm: permission denied for id (1223983171)
% 0.22/0.44  ipcrm: permission denied for id (1221132356)
% 0.22/0.44  ipcrm: permission denied for id (1224015941)
% 0.22/0.45  ipcrm: permission denied for id (1226440774)
% 0.22/0.45  ipcrm: permission denied for id (1224081479)
% 0.22/0.45  ipcrm: permission denied for id (1221165129)
% 0.22/0.45  ipcrm: permission denied for id (1224147018)
% 0.22/0.45  ipcrm: permission denied for id (1221197900)
% 0.22/0.45  ipcrm: permission denied for id (1224212557)
% 0.22/0.45  ipcrm: permission denied for id (1221230670)
% 0.22/0.45  ipcrm: permission denied for id (1221263439)
% 0.22/0.46  ipcrm: permission denied for id (1224278097)
% 0.22/0.46  ipcrm: permission denied for id (1226571858)
% 0.22/0.46  ipcrm: permission denied for id (1224343635)
% 0.22/0.46  ipcrm: permission denied for id (1226637396)
% 0.22/0.46  ipcrm: permission denied for id (1226702934)
% 0.22/0.46  ipcrm: permission denied for id (1221394519)
% 0.22/0.46  ipcrm: permission denied for id (1224474712)
% 0.22/0.47  ipcrm: permission denied for id (1224540250)
% 0.22/0.47  ipcrm: permission denied for id (1221525598)
% 0.22/0.47  ipcrm: permission denied for id (1221558368)
% 0.22/0.47  ipcrm: permission denied for id (1226899553)
% 0.22/0.48  ipcrm: permission denied for id (1221591140)
% 0.22/0.48  ipcrm: permission denied for id (1224802405)
% 0.22/0.48  ipcrm: permission denied for id (1221623910)
% 0.22/0.48  ipcrm: permission denied for id (1224835175)
% 0.22/0.48  ipcrm: permission denied for id (1224867944)
% 0.22/0.48  ipcrm: permission denied for id (1226997865)
% 0.22/0.48  ipcrm: permission denied for id (1221689450)
% 0.22/0.48  ipcrm: permission denied for id (1221722219)
% 0.22/0.49  ipcrm: permission denied for id (1221754989)
% 0.22/0.49  ipcrm: permission denied for id (1221787759)
% 0.22/0.49  ipcrm: permission denied for id (1227128945)
% 0.22/0.49  ipcrm: permission denied for id (1227161714)
% 0.22/0.49  ipcrm: permission denied for id (1225130099)
% 0.22/0.49  ipcrm: permission denied for id (1227194484)
% 0.22/0.50  ipcrm: permission denied for id (1227260022)
% 0.22/0.50  ipcrm: permission denied for id (1225261175)
% 0.22/0.50  ipcrm: permission denied for id (1225293944)
% 0.22/0.50  ipcrm: permission denied for id (1227292793)
% 0.22/0.50  ipcrm: permission denied for id (1227325562)
% 0.22/0.50  ipcrm: permission denied for id (1225392251)
% 0.22/0.51  ipcrm: permission denied for id (1222082685)
% 0.22/0.51  ipcrm: permission denied for id (1225457790)
% 0.22/0.51  ipcrm: permission denied for id (1222115455)
% 0.36/0.61  % (26258)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.36/0.62  % (26247)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.36/0.62  % (26261)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.37/0.63  % (26269)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.37/0.63  % (26253)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.37/0.63  % (26266)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.37/0.64  % (26254)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.37/0.65  % (26262)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.37/0.66  % (26249)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.37/0.66  % (26271)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.37/0.66  % (26263)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.37/0.66  % (26260)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.37/0.67  % (26263)Refutation found. Thanks to Tanya!
% 0.37/0.67  % SZS status Theorem for theBenchmark
% 0.37/0.67  % (26255)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.37/0.67  % (26252)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.37/0.67  % (26264)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.37/0.67  % (26250)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.37/0.67  % SZS output start Proof for theBenchmark
% 0.37/0.67  fof(f207,plain,(
% 0.37/0.67    $false),
% 0.37/0.67    inference(subsumption_resolution,[],[f206,f33])).
% 0.37/0.67  fof(f33,plain,(
% 0.37/0.67    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)),
% 0.37/0.67    inference(cnf_transformation,[],[f20])).
% 0.37/0.67  fof(f20,plain,(
% 0.37/0.67    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) & r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.37/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f19])).
% 0.37/0.67  fof(f19,plain,(
% 0.37/0.67    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) & r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.37/0.67    introduced(choice_axiom,[])).
% 0.37/0.67  fof(f11,plain,(
% 0.37/0.67    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.37/0.67    inference(flattening,[],[f10])).
% 0.37/0.67  fof(f10,plain,(
% 0.37/0.67    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0) & r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.37/0.67    inference(ennf_transformation,[],[f9])).
% 0.37/0.67  fof(f9,negated_conjecture,(
% 0.37/0.67    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 0.37/0.67    inference(negated_conjecture,[],[f8])).
% 0.37/0.67  fof(f8,conjecture,(
% 0.37/0.67    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).
% 0.37/0.67  fof(f206,plain,(
% 0.37/0.67    k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0)),
% 0.37/0.67    inference(forward_demodulation,[],[f201,f109])).
% 0.37/0.67  fof(f109,plain,(
% 0.37/0.67    sK0 = k1_funct_1(k6_relat_1(sK1),sK0)),
% 0.37/0.67    inference(resolution,[],[f103,f68])).
% 0.37/0.67  fof(f68,plain,(
% 0.37/0.67    r2_hidden(sK0,sK1)),
% 0.37/0.67    inference(resolution,[],[f66,f32])).
% 0.37/0.67  fof(f32,plain,(
% 0.37/0.67    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))),
% 0.37/0.67    inference(cnf_transformation,[],[f20])).
% 0.37/0.67  fof(f66,plain,(
% 0.37/0.67    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1))) | r2_hidden(X0,X1)) )),
% 0.37/0.67    inference(resolution,[],[f46,f30])).
% 0.37/0.67  fof(f30,plain,(
% 0.37/0.67    v1_relat_1(sK2)),
% 0.37/0.67    inference(cnf_transformation,[],[f20])).
% 0.37/0.67  fof(f46,plain,(
% 0.37/0.67    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,X1)) )),
% 0.37/0.67    inference(cnf_transformation,[],[f27])).
% 0.37/0.67  fof(f27,plain,(
% 0.37/0.67    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.37/0.67    inference(flattening,[],[f26])).
% 0.37/0.67  fof(f26,plain,(
% 0.37/0.67    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.37/0.67    inference(nnf_transformation,[],[f16])).
% 0.37/0.67  fof(f16,plain,(
% 0.37/0.67    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.37/0.67    inference(ennf_transformation,[],[f3])).
% 0.37/0.67  fof(f3,axiom,(
% 0.37/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 0.37/0.67  fof(f103,plain,(
% 0.37/0.67    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k1_funct_1(k6_relat_1(X0),X1) = X1) )),
% 0.37/0.67    inference(resolution,[],[f80,f57])).
% 0.37/0.67  fof(f57,plain,(
% 0.37/0.67    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0)) | ~r2_hidden(X5,X0)) )),
% 0.37/0.67    inference(subsumption_resolution,[],[f53,f34])).
% 0.37/0.67  fof(f34,plain,(
% 0.37/0.67    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.37/0.67    inference(cnf_transformation,[],[f5])).
% 0.37/0.67  fof(f5,axiom,(
% 0.37/0.67    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.37/0.67  fof(f53,plain,(
% 0.37/0.67    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0)) | ~r2_hidden(X5,X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.37/0.67    inference(equality_resolution,[],[f52])).
% 0.37/0.67  fof(f52,plain,(
% 0.37/0.67    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,X5),X1) | ~r2_hidden(X5,X0) | k6_relat_1(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.37/0.67    inference(equality_resolution,[],[f41])).
% 0.37/0.67  fof(f41,plain,(
% 0.37/0.67    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0) | k6_relat_1(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.37/0.67    inference(cnf_transformation,[],[f25])).
% 0.37/0.67  fof(f25,plain,(
% 0.37/0.67    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ((sK3(X0,X1) != sK4(X0,X1) | ~r2_hidden(sK3(X0,X1),X0) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & ((sK3(X0,X1) = sK4(X0,X1) & r2_hidden(sK3(X0,X1),X0)) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 0.37/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f24])).
% 0.37/0.67  fof(f24,plain,(
% 0.37/0.67    ! [X1,X0] : (? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1))) => ((sK3(X0,X1) != sK4(X0,X1) | ~r2_hidden(sK3(X0,X1),X0) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & ((sK3(X0,X1) = sK4(X0,X1) & r2_hidden(sK3(X0,X1),X0)) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1))))),
% 0.37/0.67    introduced(choice_axiom,[])).
% 0.37/0.67  fof(f23,plain,(
% 0.37/0.67    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 0.37/0.67    inference(rectify,[],[f22])).
% 0.37/0.67  fof(f22,plain,(
% 0.37/0.67    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | X2 != X3 | ~r2_hidden(X2,X0)) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 0.37/0.67    inference(flattening,[],[f21])).
% 0.37/0.67  fof(f21,plain,(
% 0.37/0.67    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : (((X2 != X3 | ~r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | (X2 != X3 | ~r2_hidden(X2,X0))) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 0.37/0.67    inference(nnf_transformation,[],[f13])).
% 0.37/0.67  fof(f13,plain,(
% 0.37/0.67    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))) | ~v1_relat_1(X1))),
% 0.37/0.67    inference(ennf_transformation,[],[f1])).
% 0.37/0.67  fof(f1,axiom,(
% 0.37/0.67    ! [X0,X1] : (v1_relat_1(X1) => (k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).
% 0.37/0.67  fof(f80,plain,(
% 0.37/0.67    ( ! [X4,X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k6_relat_1(X4)) | k1_funct_1(k6_relat_1(X4),X2) = X3) )),
% 0.37/0.67    inference(subsumption_resolution,[],[f78,f34])).
% 0.37/0.67  fof(f78,plain,(
% 0.37/0.67    ( ! [X4,X2,X3] : (~r2_hidden(k4_tarski(X2,X3),k6_relat_1(X4)) | k1_funct_1(k6_relat_1(X4),X2) = X3 | ~v1_relat_1(k6_relat_1(X4))) )),
% 0.37/0.67    inference(resolution,[],[f50,f35])).
% 0.37/0.67  fof(f35,plain,(
% 0.37/0.67    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.37/0.67    inference(cnf_transformation,[],[f5])).
% 0.37/0.67  fof(f50,plain,(
% 0.37/0.67    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.37/0.67    inference(cnf_transformation,[],[f29])).
% 0.37/0.67  fof(f29,plain,(
% 0.37/0.67    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.37/0.67    inference(flattening,[],[f28])).
% 0.37/0.67  fof(f28,plain,(
% 0.37/0.67    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.37/0.67    inference(nnf_transformation,[],[f18])).
% 0.37/0.67  fof(f18,plain,(
% 0.37/0.67    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.37/0.67    inference(flattening,[],[f17])).
% 0.37/0.67  fof(f17,plain,(
% 0.37/0.67    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.37/0.67    inference(ennf_transformation,[],[f7])).
% 0.37/0.67  fof(f7,axiom,(
% 0.37/0.67    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.37/0.67  fof(f201,plain,(
% 0.37/0.67    k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0))),
% 0.37/0.67    inference(resolution,[],[f132,f68])).
% 0.37/0.67  fof(f132,plain,(
% 0.37/0.67    ( ! [X2,X1] : (~r2_hidden(X2,X1) | k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k7_relat_1(sK2,X1),X2)) )),
% 0.37/0.67    inference(forward_demodulation,[],[f131,f36])).
% 0.37/0.67  fof(f36,plain,(
% 0.37/0.67    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.37/0.67    inference(cnf_transformation,[],[f2])).
% 0.37/0.67  fof(f2,axiom,(
% 0.37/0.67    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.37/0.67  fof(f131,plain,(
% 0.37/0.67    ( ! [X2,X1] : (k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2)) = k1_funct_1(k7_relat_1(sK2,X1),X2) | ~r2_hidden(X2,k1_relat_1(k6_relat_1(X1)))) )),
% 0.37/0.67    inference(forward_demodulation,[],[f130,f64])).
% 0.37/0.67  fof(f64,plain,(
% 0.37/0.67    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)) )),
% 0.37/0.67    inference(resolution,[],[f38,f30])).
% 0.37/0.67  fof(f38,plain,(
% 0.37/0.67    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.37/0.67    inference(cnf_transformation,[],[f12])).
% 0.37/0.67  fof(f12,plain,(
% 0.37/0.67    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.37/0.67    inference(ennf_transformation,[],[f4])).
% 0.37/0.67  fof(f4,axiom,(
% 0.37/0.67    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.37/0.67  fof(f130,plain,(
% 0.37/0.67    ( ! [X2,X1] : (k1_funct_1(k5_relat_1(k6_relat_1(X1),sK2),X2) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2)) | ~r2_hidden(X2,k1_relat_1(k6_relat_1(X1)))) )),
% 0.37/0.67    inference(subsumption_resolution,[],[f128,f34])).
% 0.37/0.67  fof(f128,plain,(
% 0.37/0.67    ( ! [X2,X1] : (k1_funct_1(k5_relat_1(k6_relat_1(X1),sK2),X2) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(X1),X2)) | ~r2_hidden(X2,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.37/0.67    inference(resolution,[],[f97,f35])).
% 0.37/0.67  fof(f97,plain,(
% 0.37/0.67    ( ! [X0,X1] : (~v1_funct_1(X1) | k1_funct_1(k5_relat_1(X1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.37/0.67    inference(subsumption_resolution,[],[f95,f30])).
% 0.37/0.67  fof(f95,plain,(
% 0.37/0.67    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,sK2),X0) = k1_funct_1(sK2,k1_funct_1(X1,X0)) | ~v1_relat_1(sK2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.37/0.67    inference(resolution,[],[f45,f31])).
% 0.37/0.67  fof(f31,plain,(
% 0.37/0.67    v1_funct_1(sK2)),
% 0.37/0.67    inference(cnf_transformation,[],[f20])).
% 0.37/0.67  fof(f45,plain,(
% 0.37/0.67    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.37/0.67    inference(cnf_transformation,[],[f15])).
% 0.37/0.67  fof(f15,plain,(
% 0.37/0.67    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.37/0.67    inference(flattening,[],[f14])).
% 0.37/0.67  fof(f14,plain,(
% 0.37/0.67    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.37/0.67    inference(ennf_transformation,[],[f6])).
% 0.37/0.67  fof(f6,axiom,(
% 0.37/0.67    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.37/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).
% 0.37/0.67  % SZS output end Proof for theBenchmark
% 0.37/0.67  % (26263)------------------------------
% 0.37/0.67  % (26263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.67  % (26263)Termination reason: Refutation
% 0.37/0.67  
% 0.37/0.67  % (26263)Memory used [KB]: 1791
% 0.37/0.67  % (26263)Time elapsed: 0.114 s
% 0.37/0.67  % (26263)------------------------------
% 0.37/0.67  % (26263)------------------------------
% 0.37/0.68  % (26113)Success in time 0.312 s
%------------------------------------------------------------------------------
