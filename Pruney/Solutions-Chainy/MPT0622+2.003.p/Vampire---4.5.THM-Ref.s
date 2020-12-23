%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:01 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 266 expanded)
%              Number of leaves         :   10 (  82 expanded)
%              Depth                    :   27
%              Number of atoms          :  366 (2044 expanded)
%              Number of equality atoms :  184 (1075 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f168,plain,(
    $false ),
    inference(subsumption_resolution,[],[f167,f27])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK1 != sK2
    & k1_tarski(sK0) = k2_relat_1(sK2)
    & k1_tarski(sK0) = k2_relat_1(sK1)
    & k1_relat_1(sK1) = k1_relat_1(sK2)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & k1_tarski(X0) = k2_relat_1(X2)
            & k1_tarski(X0) = k2_relat_1(X1)
            & k1_relat_1(X1) = k1_relat_1(X2)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( sK1 != X2
          & k2_relat_1(X2) = k1_tarski(sK0)
          & k1_tarski(sK0) = k2_relat_1(sK1)
          & k1_relat_1(X2) = k1_relat_1(sK1)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( sK1 != X2
        & k2_relat_1(X2) = k1_tarski(sK0)
        & k1_tarski(sK0) = k2_relat_1(sK1)
        & k1_relat_1(X2) = k1_relat_1(sK1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( sK1 != sK2
      & k1_tarski(sK0) = k2_relat_1(sK2)
      & k1_tarski(sK0) = k2_relat_1(sK1)
      & k1_relat_1(sK1) = k1_relat_1(sK2)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k1_tarski(X0) = k2_relat_1(X2)
          & k1_tarski(X0) = k2_relat_1(X1)
          & k1_relat_1(X1) = k1_relat_1(X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k1_tarski(X0) = k2_relat_1(X2)
          & k1_tarski(X0) = k2_relat_1(X1)
          & k1_relat_1(X1) = k1_relat_1(X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( k1_tarski(X0) = k2_relat_1(X2)
                & k1_tarski(X0) = k2_relat_1(X1)
                & k1_relat_1(X1) = k1_relat_1(X2) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k1_tarski(X0) = k2_relat_1(X2)
              & k1_tarski(X0) = k2_relat_1(X1)
              & k1_relat_1(X1) = k1_relat_1(X2) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_1)).

fof(f167,plain,(
    ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f166,f28])).

fof(f28,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f166,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f165,f34])).

fof(f34,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f19])).

fof(f165,plain,
    ( sK1 = sK2
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(trivial_inequality_removal,[],[f164])).

fof(f164,plain,
    ( sK1 = sK2
    | k1_relat_1(sK1) != k1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f146,f83])).

fof(f83,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK2,X0),k1_relat_1(sK1))
      | sK2 = X0
      | k1_relat_1(X0) != k1_relat_1(sK1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f82,f29])).

fof(f29,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f82,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK2,X0),k1_relat_1(sK1))
      | sK2 = X0
      | k1_relat_1(X0) != k1_relat_1(sK1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f81,f30])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f81,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK2,X0),k1_relat_1(sK1))
      | sK2 = X0
      | k1_relat_1(X0) != k1_relat_1(sK1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f36,f31])).

fof(f31,plain,(
    k1_relat_1(sK1) = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
            & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(f146,plain,(
    ~ r2_hidden(sK3(sK2,sK1),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f145,f27])).

fof(f145,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK3(sK2,sK1),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f144,f28])).

fof(f144,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK3(sK2,sK1),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f143,f34])).

fof(f143,plain,
    ( sK1 = sK2
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK3(sK2,sK1),k1_relat_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f141])).

fof(f141,plain,
    ( sK0 != sK0
    | k1_relat_1(sK1) != k1_relat_1(sK1)
    | sK1 = sK2
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK3(sK2,sK1),k1_relat_1(sK1)) ),
    inference(superposition,[],[f110,f79])).

fof(f79,plain,(
    ! [X1] :
      ( sK0 = k1_funct_1(sK1,X1)
      | ~ r2_hidden(X1,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f77,f64])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK1,X0),k1_tarski(sK0))
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f63,f27])).

fof(f63,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK1,X0),k1_tarski(sK0))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f61,f28])).

fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK1,X0),k1_tarski(sK0))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f39,f32])).

fof(f32,plain,(
    k1_tarski(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X0))
      | X0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X0))
      | X0 = X1
      | X0 = X1 ) ),
    inference(superposition,[],[f72,f35])).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

% (6913)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_tarski(X0,X1))
      | X0 = X2
      | X1 = X2 ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_tarski(X0,X1))
      | X0 = X2
      | X0 = X2
      | X1 = X2 ) ),
    inference(superposition,[],[f56,f38])).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k1_enumset1(X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f110,plain,(
    ! [X2] :
      ( sK0 != k1_funct_1(X2,sK3(sK2,X2))
      | k1_relat_1(X2) != k1_relat_1(sK1)
      | sK2 = X2
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f109,f83])).

fof(f109,plain,(
    ! [X2] :
      ( k1_relat_1(X2) != k1_relat_1(sK1)
      | sK0 != k1_funct_1(X2,sK3(sK2,X2))
      | sK2 = X2
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(sK3(sK2,X2),k1_relat_1(sK1)) ) ),
    inference(forward_demodulation,[],[f108,f31])).

fof(f108,plain,(
    ! [X2] :
      ( sK0 != k1_funct_1(X2,sK3(sK2,X2))
      | sK2 = X2
      | k1_relat_1(X2) != k1_relat_1(sK2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(sK3(sK2,X2),k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f107,f29])).

fof(f107,plain,(
    ! [X2] :
      ( sK0 != k1_funct_1(X2,sK3(sK2,X2))
      | sK2 = X2
      | k1_relat_1(X2) != k1_relat_1(sK2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(sK3(sK2,X2),k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f101,f30])).

fof(f101,plain,(
    ! [X2] :
      ( sK0 != k1_funct_1(X2,sK3(sK2,X2))
      | sK2 = X2
      | k1_relat_1(X2) != k1_relat_1(sK2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(sK3(sK2,X2),k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f37,f80])).

fof(f80,plain,(
    ! [X2] :
      ( sK0 = k1_funct_1(sK2,X2)
      | ~ r2_hidden(X2,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f77,f67])).

fof(f67,plain,(
    ! [X1] :
      ( r2_hidden(k1_funct_1(sK2,X1),k1_tarski(sK0))
      | ~ r2_hidden(X1,k1_relat_1(sK1)) ) ),
    inference(forward_demodulation,[],[f66,f31])).

fof(f66,plain,(
    ! [X1] :
      ( r2_hidden(k1_funct_1(sK2,X1),k1_tarski(sK0))
      | ~ r2_hidden(X1,k1_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f65,f29])).

fof(f65,plain,(
    ! [X1] :
      ( r2_hidden(k1_funct_1(sK2,X1),k1_tarski(sK0))
      | ~ r2_hidden(X1,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f62,f30])).

fof(f62,plain,(
    ! [X1] :
      ( r2_hidden(k1_funct_1(sK2,X1),k1_tarski(sK0))
      | ~ r2_hidden(X1,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f39,f33])).

fof(f33,plain,(
    k1_tarski(sK0) = k2_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
      | X0 = X1
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.07  % Command    : run_vampire %s %d
% 0.08/0.26  % Computer   : n004.cluster.edu
% 0.08/0.26  % Model      : x86_64 x86_64
% 0.08/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.26  % Memory     : 8042.1875MB
% 0.08/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.26  % CPULimit   : 60
% 0.08/0.26  % WCLimit    : 600
% 0.08/0.26  % DateTime   : Tue Dec  1 11:12:23 EST 2020
% 0.08/0.26  % CPUTime    : 
% 0.12/0.38  % (6909)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.12/0.39  % (6909)Refutation found. Thanks to Tanya!
% 0.12/0.39  % SZS status Theorem for theBenchmark
% 0.12/0.40  % (6904)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.12/0.40  % (6902)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.12/0.40  % SZS output start Proof for theBenchmark
% 0.12/0.40  fof(f168,plain,(
% 0.12/0.40    $false),
% 0.12/0.40    inference(subsumption_resolution,[],[f167,f27])).
% 0.12/0.40  fof(f27,plain,(
% 0.12/0.40    v1_relat_1(sK1)),
% 0.12/0.40    inference(cnf_transformation,[],[f19])).
% 0.12/0.40  fof(f19,plain,(
% 0.12/0.40    (sK1 != sK2 & k1_tarski(sK0) = k2_relat_1(sK2) & k1_tarski(sK0) = k2_relat_1(sK1) & k1_relat_1(sK1) = k1_relat_1(sK2) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.12/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18,f17])).
% 0.12/0.40  fof(f17,plain,(
% 0.12/0.40    ? [X0,X1] : (? [X2] : (X1 != X2 & k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (sK1 != X2 & k2_relat_1(X2) = k1_tarski(sK0) & k1_tarski(sK0) = k2_relat_1(sK1) & k1_relat_1(X2) = k1_relat_1(sK1) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.12/0.40    introduced(choice_axiom,[])).
% 0.12/0.40  fof(f18,plain,(
% 0.12/0.40    ? [X2] : (sK1 != X2 & k2_relat_1(X2) = k1_tarski(sK0) & k1_tarski(sK0) = k2_relat_1(sK1) & k1_relat_1(X2) = k1_relat_1(sK1) & v1_funct_1(X2) & v1_relat_1(X2)) => (sK1 != sK2 & k1_tarski(sK0) = k2_relat_1(sK2) & k1_tarski(sK0) = k2_relat_1(sK1) & k1_relat_1(sK1) = k1_relat_1(sK2) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.12/0.40    introduced(choice_axiom,[])).
% 0.12/0.40  fof(f11,plain,(
% 0.12/0.40    ? [X0,X1] : (? [X2] : (X1 != X2 & k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.12/0.40    inference(flattening,[],[f10])).
% 0.12/0.40  fof(f10,plain,(
% 0.12/0.40    ? [X0,X1] : (? [X2] : ((X1 != X2 & (k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.12/0.40    inference(ennf_transformation,[],[f9])).
% 0.12/0.40  fof(f9,negated_conjecture,(
% 0.12/0.40    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2)) => X1 = X2)))),
% 0.12/0.40    inference(negated_conjecture,[],[f8])).
% 0.12/0.40  fof(f8,conjecture,(
% 0.12/0.40    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2)) => X1 = X2)))),
% 0.12/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_1)).
% 0.12/0.40  fof(f167,plain,(
% 0.12/0.40    ~v1_relat_1(sK1)),
% 0.12/0.40    inference(subsumption_resolution,[],[f166,f28])).
% 0.12/0.40  fof(f28,plain,(
% 0.12/0.40    v1_funct_1(sK1)),
% 0.12/0.40    inference(cnf_transformation,[],[f19])).
% 0.12/0.40  fof(f166,plain,(
% 0.12/0.40    ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.12/0.40    inference(subsumption_resolution,[],[f165,f34])).
% 0.12/0.40  fof(f34,plain,(
% 0.12/0.40    sK1 != sK2),
% 0.12/0.40    inference(cnf_transformation,[],[f19])).
% 0.12/0.40  fof(f165,plain,(
% 0.12/0.40    sK1 = sK2 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.12/0.40    inference(trivial_inequality_removal,[],[f164])).
% 0.12/0.40  fof(f164,plain,(
% 0.12/0.40    sK1 = sK2 | k1_relat_1(sK1) != k1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.12/0.40    inference(resolution,[],[f146,f83])).
% 0.12/0.40  fof(f83,plain,(
% 0.12/0.40    ( ! [X0] : (r2_hidden(sK3(sK2,X0),k1_relat_1(sK1)) | sK2 = X0 | k1_relat_1(X0) != k1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.12/0.40    inference(subsumption_resolution,[],[f82,f29])).
% 0.12/0.40  fof(f29,plain,(
% 0.12/0.40    v1_relat_1(sK2)),
% 0.12/0.40    inference(cnf_transformation,[],[f19])).
% 0.12/0.40  fof(f82,plain,(
% 0.12/0.40    ( ! [X0] : (r2_hidden(sK3(sK2,X0),k1_relat_1(sK1)) | sK2 = X0 | k1_relat_1(X0) != k1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) )),
% 0.12/0.40    inference(subsumption_resolution,[],[f81,f30])).
% 0.12/0.40  fof(f30,plain,(
% 0.12/0.40    v1_funct_1(sK2)),
% 0.12/0.40    inference(cnf_transformation,[],[f19])).
% 0.12/0.40  fof(f81,plain,(
% 0.12/0.40    ( ! [X0] : (r2_hidden(sK3(sK2,X0),k1_relat_1(sK1)) | sK2 = X0 | k1_relat_1(X0) != k1_relat_1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.12/0.40    inference(superposition,[],[f36,f31])).
% 0.12/0.40  fof(f31,plain,(
% 0.12/0.40    k1_relat_1(sK1) = k1_relat_1(sK2)),
% 0.12/0.40    inference(cnf_transformation,[],[f19])).
% 0.12/0.40  fof(f36,plain,(
% 0.12/0.40    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | X0 = X1 | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.12/0.40    inference(cnf_transformation,[],[f21])).
% 0.12/0.40  fof(f21,plain,(
% 0.12/0.40    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.12/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f20])).
% 0.12/0.40  fof(f20,plain,(
% 0.12/0.40    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))),
% 0.12/0.40    introduced(choice_axiom,[])).
% 0.12/0.40  fof(f13,plain,(
% 0.12/0.40    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.12/0.40    inference(flattening,[],[f12])).
% 0.12/0.40  fof(f12,plain,(
% 0.12/0.40    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.12/0.40    inference(ennf_transformation,[],[f7])).
% 0.12/0.40  fof(f7,axiom,(
% 0.12/0.40    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) => X0 = X1)))),
% 0.12/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 0.12/0.40  fof(f146,plain,(
% 0.12/0.40    ~r2_hidden(sK3(sK2,sK1),k1_relat_1(sK1))),
% 0.12/0.40    inference(subsumption_resolution,[],[f145,f27])).
% 0.12/0.40  fof(f145,plain,(
% 0.12/0.40    ~v1_relat_1(sK1) | ~r2_hidden(sK3(sK2,sK1),k1_relat_1(sK1))),
% 0.12/0.40    inference(subsumption_resolution,[],[f144,f28])).
% 0.12/0.40  fof(f144,plain,(
% 0.12/0.40    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(sK3(sK2,sK1),k1_relat_1(sK1))),
% 0.12/0.40    inference(subsumption_resolution,[],[f143,f34])).
% 0.12/0.40  fof(f143,plain,(
% 0.12/0.40    sK1 = sK2 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(sK3(sK2,sK1),k1_relat_1(sK1))),
% 0.12/0.40    inference(trivial_inequality_removal,[],[f141])).
% 0.12/0.40  fof(f141,plain,(
% 0.12/0.40    sK0 != sK0 | k1_relat_1(sK1) != k1_relat_1(sK1) | sK1 = sK2 | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(sK3(sK2,sK1),k1_relat_1(sK1))),
% 0.12/0.40    inference(superposition,[],[f110,f79])).
% 0.12/0.40  fof(f79,plain,(
% 0.12/0.40    ( ! [X1] : (sK0 = k1_funct_1(sK1,X1) | ~r2_hidden(X1,k1_relat_1(sK1))) )),
% 0.12/0.40    inference(resolution,[],[f77,f64])).
% 0.12/0.40  fof(f64,plain,(
% 0.12/0.40    ( ! [X0] : (r2_hidden(k1_funct_1(sK1,X0),k1_tarski(sK0)) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 0.12/0.40    inference(subsumption_resolution,[],[f63,f27])).
% 0.12/0.40  fof(f63,plain,(
% 0.12/0.40    ( ! [X0] : (r2_hidden(k1_funct_1(sK1,X0),k1_tarski(sK0)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.12/0.40    inference(subsumption_resolution,[],[f61,f28])).
% 0.12/0.40  fof(f61,plain,(
% 0.12/0.40    ( ! [X0] : (r2_hidden(k1_funct_1(sK1,X0),k1_tarski(sK0)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.12/0.40    inference(superposition,[],[f39,f32])).
% 0.12/0.40  fof(f32,plain,(
% 0.12/0.40    k1_tarski(sK0) = k2_relat_1(sK1)),
% 0.12/0.40    inference(cnf_transformation,[],[f19])).
% 0.12/0.40  fof(f39,plain,(
% 0.12/0.40    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.12/0.40    inference(cnf_transformation,[],[f15])).
% 0.12/0.40  fof(f15,plain,(
% 0.12/0.40    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.12/0.40    inference(flattening,[],[f14])).
% 0.12/0.40  fof(f14,plain,(
% 0.12/0.40    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.12/0.40    inference(ennf_transformation,[],[f6])).
% 0.12/0.40  fof(f6,axiom,(
% 0.12/0.40    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.12/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 0.12/0.40  fof(f77,plain,(
% 0.12/0.40    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X0)) | X0 = X1) )),
% 0.12/0.40    inference(duplicate_literal_removal,[],[f76])).
% 0.12/0.40  fof(f76,plain,(
% 0.12/0.40    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X0)) | X0 = X1 | X0 = X1) )),
% 0.12/0.40    inference(superposition,[],[f72,f35])).
% 0.12/0.40  fof(f35,plain,(
% 0.12/0.40    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.12/0.40    inference(cnf_transformation,[],[f2])).
% 0.12/0.40  fof(f2,axiom,(
% 0.12/0.40    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.12/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.12/0.40  % (6913)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.12/0.40  fof(f72,plain,(
% 0.12/0.40    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_tarski(X0,X1)) | X0 = X2 | X1 = X2) )),
% 0.12/0.40    inference(duplicate_literal_removal,[],[f71])).
% 0.12/0.40  fof(f71,plain,(
% 0.12/0.40    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_tarski(X0,X1)) | X0 = X2 | X0 = X2 | X1 = X2) )),
% 0.12/0.40    inference(superposition,[],[f56,f38])).
% 0.12/0.40  fof(f38,plain,(
% 0.12/0.40    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.12/0.40    inference(cnf_transformation,[],[f3])).
% 0.12/0.40  fof(f3,axiom,(
% 0.12/0.40    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.12/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.12/0.40  fof(f56,plain,(
% 0.12/0.40    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k1_enumset1(X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 0.12/0.40    inference(equality_resolution,[],[f42])).
% 0.12/0.40  fof(f42,plain,(
% 0.12/0.40    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.12/0.40    inference(cnf_transformation,[],[f26])).
% 0.12/0.40  fof(f26,plain,(
% 0.12/0.40    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.12/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 0.12/0.40  fof(f25,plain,(
% 0.12/0.40    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 0.12/0.40    introduced(choice_axiom,[])).
% 0.12/0.40  fof(f24,plain,(
% 0.12/0.40    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.12/0.40    inference(rectify,[],[f23])).
% 0.12/0.40  fof(f23,plain,(
% 0.12/0.40    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.12/0.40    inference(flattening,[],[f22])).
% 0.12/0.40  fof(f22,plain,(
% 0.12/0.40    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.12/0.40    inference(nnf_transformation,[],[f16])).
% 0.12/0.40  fof(f16,plain,(
% 0.12/0.40    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.12/0.40    inference(ennf_transformation,[],[f1])).
% 0.12/0.40  fof(f1,axiom,(
% 0.12/0.40    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.12/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.12/0.40  fof(f110,plain,(
% 0.12/0.40    ( ! [X2] : (sK0 != k1_funct_1(X2,sK3(sK2,X2)) | k1_relat_1(X2) != k1_relat_1(sK1) | sK2 = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.12/0.40    inference(subsumption_resolution,[],[f109,f83])).
% 0.12/0.40  fof(f109,plain,(
% 0.12/0.40    ( ! [X2] : (k1_relat_1(X2) != k1_relat_1(sK1) | sK0 != k1_funct_1(X2,sK3(sK2,X2)) | sK2 = X2 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(sK3(sK2,X2),k1_relat_1(sK1))) )),
% 0.12/0.40    inference(forward_demodulation,[],[f108,f31])).
% 0.12/0.40  fof(f108,plain,(
% 0.12/0.40    ( ! [X2] : (sK0 != k1_funct_1(X2,sK3(sK2,X2)) | sK2 = X2 | k1_relat_1(X2) != k1_relat_1(sK2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(sK3(sK2,X2),k1_relat_1(sK1))) )),
% 0.12/0.40    inference(subsumption_resolution,[],[f107,f29])).
% 0.12/0.40  fof(f107,plain,(
% 0.12/0.40    ( ! [X2] : (sK0 != k1_funct_1(X2,sK3(sK2,X2)) | sK2 = X2 | k1_relat_1(X2) != k1_relat_1(sK2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(sK2) | ~r2_hidden(sK3(sK2,X2),k1_relat_1(sK1))) )),
% 0.12/0.40    inference(subsumption_resolution,[],[f101,f30])).
% 0.12/0.40  fof(f101,plain,(
% 0.12/0.40    ( ! [X2] : (sK0 != k1_funct_1(X2,sK3(sK2,X2)) | sK2 = X2 | k1_relat_1(X2) != k1_relat_1(sK2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~r2_hidden(sK3(sK2,X2),k1_relat_1(sK1))) )),
% 0.12/0.40    inference(superposition,[],[f37,f80])).
% 0.12/0.40  fof(f80,plain,(
% 0.12/0.40    ( ! [X2] : (sK0 = k1_funct_1(sK2,X2) | ~r2_hidden(X2,k1_relat_1(sK1))) )),
% 0.12/0.40    inference(resolution,[],[f77,f67])).
% 0.12/0.40  fof(f67,plain,(
% 0.12/0.40    ( ! [X1] : (r2_hidden(k1_funct_1(sK2,X1),k1_tarski(sK0)) | ~r2_hidden(X1,k1_relat_1(sK1))) )),
% 0.12/0.40    inference(forward_demodulation,[],[f66,f31])).
% 0.12/0.40  fof(f66,plain,(
% 0.12/0.40    ( ! [X1] : (r2_hidden(k1_funct_1(sK2,X1),k1_tarski(sK0)) | ~r2_hidden(X1,k1_relat_1(sK2))) )),
% 0.12/0.40    inference(subsumption_resolution,[],[f65,f29])).
% 0.12/0.40  fof(f65,plain,(
% 0.12/0.40    ( ! [X1] : (r2_hidden(k1_funct_1(sK2,X1),k1_tarski(sK0)) | ~r2_hidden(X1,k1_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 0.12/0.40    inference(subsumption_resolution,[],[f62,f30])).
% 0.12/0.40  fof(f62,plain,(
% 0.12/0.40    ( ! [X1] : (r2_hidden(k1_funct_1(sK2,X1),k1_tarski(sK0)) | ~r2_hidden(X1,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.12/0.40    inference(superposition,[],[f39,f33])).
% 0.12/0.40  fof(f33,plain,(
% 0.12/0.40    k1_tarski(sK0) = k2_relat_1(sK2)),
% 0.12/0.40    inference(cnf_transformation,[],[f19])).
% 0.12/0.40  fof(f37,plain,(
% 0.12/0.40    ( ! [X0,X1] : (k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) | X0 = X1 | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.12/0.40    inference(cnf_transformation,[],[f21])).
% 0.12/0.40  % SZS output end Proof for theBenchmark
% 0.12/0.40  % (6909)------------------------------
% 0.12/0.40  % (6909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.40  % (6909)Termination reason: Refutation
% 0.12/0.40  
% 0.12/0.40  % (6909)Memory used [KB]: 1791
% 0.12/0.40  % (6909)Time elapsed: 0.088 s
% 0.12/0.40  % (6909)------------------------------
% 0.12/0.40  % (6909)------------------------------
% 0.12/0.41  % (6899)Success in time 0.14 s
%------------------------------------------------------------------------------
