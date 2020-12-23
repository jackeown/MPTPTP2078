%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 447 expanded)
%              Number of leaves         :   10 ( 150 expanded)
%              Depth                    :   16
%              Number of atoms          :  276 (2959 expanded)
%              Number of equality atoms :   77 ( 666 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f280,plain,(
    $false ),
    inference(subsumption_resolution,[],[f279,f88])).

fof(f88,plain,(
    sK4(sK2) != sK5(sK2) ),
    inference(resolution,[],[f75,f43])).

fof(f43,plain,(
    ! [X0] :
      ( sP0(X0)
      | sK4(X0) != sK5(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( sK4(X0) != sK5(X0)
          & k5_relat_1(sK4(X0),X0) = k5_relat_1(sK5(X0),X0)
          & k1_relat_1(sK4(X0)) = k1_relat_1(sK5(X0))
          & r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0))
          & r1_tarski(k2_relat_1(sK4(X0)),k1_relat_1(X0))
          & v1_funct_1(sK5(X0))
          & v1_relat_1(sK5(X0))
          & v1_funct_1(sK4(X0))
          & v1_relat_1(sK4(X0)) ) )
      & ( ! [X3] :
            ( ! [X4] :
                ( X3 = X4
                | k5_relat_1(X3,X0) != k5_relat_1(X4,X0)
                | k1_relat_1(X3) != k1_relat_1(X4)
                | ~ r1_tarski(k2_relat_1(X4),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X3),k1_relat_1(X0))
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ v1_funct_1(X3)
            | ~ v1_relat_1(X3) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f21,f23,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
              & k1_relat_1(X1) = k1_relat_1(X2)
              & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
              & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( sK4(X0) != X2
            & k5_relat_1(X2,X0) = k5_relat_1(sK4(X0),X0)
            & k1_relat_1(X2) = k1_relat_1(sK4(X0))
            & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
            & r1_tarski(k2_relat_1(sK4(X0)),k1_relat_1(X0))
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(sK4(X0))
        & v1_relat_1(sK4(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK4(X0) != X2
          & k5_relat_1(X2,X0) = k5_relat_1(sK4(X0),X0)
          & k1_relat_1(X2) = k1_relat_1(sK4(X0))
          & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
          & r1_tarski(k2_relat_1(sK4(X0)),k1_relat_1(X0))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( sK4(X0) != sK5(X0)
        & k5_relat_1(sK4(X0),X0) = k5_relat_1(sK5(X0),X0)
        & k1_relat_1(sK4(X0)) = k1_relat_1(sK5(X0))
        & r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0))
        & r1_tarski(k2_relat_1(sK4(X0)),k1_relat_1(X0))
        & v1_funct_1(sK5(X0))
        & v1_relat_1(sK5(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
                & k1_relat_1(X1) = k1_relat_1(X2)
                & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) ) )
      & ( ! [X3] :
            ( ! [X4] :
                ( X3 = X4
                | k5_relat_1(X3,X0) != k5_relat_1(X4,X0)
                | k1_relat_1(X3) != k1_relat_1(X4)
                | ~ r1_tarski(k2_relat_1(X4),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X3),k1_relat_1(X0))
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ v1_funct_1(X3)
            | ~ v1_relat_1(X3) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
                & k1_relat_1(X1) = k1_relat_1(X2)
                & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) ) )
      & ( ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
              | k1_relat_1(X1) != k1_relat_1(X2)
              | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
              | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f75,plain,(
    ~ sP0(sK2) ),
    inference(subsumption_resolution,[],[f74,f30])).

fof(f30,plain,(
    ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ v2_funct_1(sK2)
    & k6_relat_1(k1_relat_1(sK2)) = k5_relat_1(sK2,sK3)
    & v1_funct_1(sK3)
    & v1_relat_1(sK3)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f7,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ~ v2_funct_1(X0)
        & ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v2_funct_1(sK2)
      & ? [X1] :
          ( k5_relat_1(sK2,X1) = k6_relat_1(k1_relat_1(sK2))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( k5_relat_1(sK2,X1) = k6_relat_1(k1_relat_1(sK2))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k6_relat_1(k1_relat_1(sK2)) = k5_relat_1(sK2,sK3)
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ? [X1] :
          ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ? [X1] :
          ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ? [X1] :
              ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & v1_funct_1(X1)
              & v1_relat_1(X1) )
         => v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

fof(f74,plain,
    ( v2_funct_1(sK2)
    | ~ sP0(sK2) ),
    inference(resolution,[],[f56,f33])).

fof(f33,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ sP0(X0)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_funct_1(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f56,plain,(
    sP1(sK2) ),
    inference(subsumption_resolution,[],[f53,f25])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,
    ( sP1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f26,f44])).

fof(f44,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f10,f14,f13])).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k5_relat_1(X1,X0) != k5_relat_1(X2,X0)
                | k1_relat_1(X1) != k1_relat_1(X2)
                | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k5_relat_1(X1,X0) = k5_relat_1(X2,X0)
                    & k1_relat_1(X1) = k1_relat_1(X2)
                    & r1_tarski(k2_relat_1(X2),k1_relat_1(X0))
                    & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) )
                 => X1 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_1)).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f279,plain,(
    sK4(sK2) = sK5(sK2) ),
    inference(forward_demodulation,[],[f272,f270])).

fof(f270,plain,(
    sK4(sK2) = k5_relat_1(k5_relat_1(sK4(sK2),sK2),sK3) ),
    inference(forward_demodulation,[],[f267,f126])).

fof(f126,plain,(
    sK4(sK2) = k5_relat_1(sK4(sK2),k5_relat_1(sK2,sK3)) ),
    inference(forward_demodulation,[],[f125,f29])).

fof(f29,plain,(
    k6_relat_1(k1_relat_1(sK2)) = k5_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f125,plain,(
    sK4(sK2) = k5_relat_1(sK4(sK2),k6_relat_1(k1_relat_1(sK2))) ),
    inference(subsumption_resolution,[],[f124,f80])).

fof(f80,plain,(
    v1_relat_1(sK4(sK2)) ),
    inference(resolution,[],[f75,f35])).

fof(f35,plain,(
    ! [X0] :
      ( sP0(X0)
      | v1_relat_1(sK4(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f124,plain,
    ( sK4(sK2) = k5_relat_1(sK4(sK2),k6_relat_1(k1_relat_1(sK2)))
    | ~ v1_relat_1(sK4(sK2)) ),
    inference(resolution,[],[f84,f45])).

% (13230)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f45,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f84,plain,(
    r1_tarski(k2_relat_1(sK4(sK2)),k1_relat_1(sK2)) ),
    inference(resolution,[],[f75,f39])).

fof(f39,plain,(
    ! [X0] :
      ( sP0(X0)
      | r1_tarski(k2_relat_1(sK4(X0)),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f267,plain,(
    k5_relat_1(sK4(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(sK4(sK2),sK2),sK3) ),
    inference(resolution,[],[f196,f80])).

fof(f196,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(X1,k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(X1,sK2),sK3) ) ),
    inference(resolution,[],[f47,f27])).

fof(f27,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(X2,sK2),X3) = k5_relat_1(X2,k5_relat_1(sK2,X3))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f25,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f272,plain,(
    sK5(sK2) = k5_relat_1(k5_relat_1(sK4(sK2),sK2),sK3) ),
    inference(forward_demodulation,[],[f271,f131])).

fof(f131,plain,(
    sK5(sK2) = k5_relat_1(sK5(sK2),k5_relat_1(sK2,sK3)) ),
    inference(forward_demodulation,[],[f130,f29])).

fof(f130,plain,(
    sK5(sK2) = k5_relat_1(sK5(sK2),k6_relat_1(k1_relat_1(sK2))) ),
    inference(subsumption_resolution,[],[f129,f82])).

fof(f82,plain,(
    v1_relat_1(sK5(sK2)) ),
    inference(resolution,[],[f75,f37])).

fof(f37,plain,(
    ! [X0] :
      ( sP0(X0)
      | v1_relat_1(sK5(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f129,plain,
    ( sK5(sK2) = k5_relat_1(sK5(sK2),k6_relat_1(k1_relat_1(sK2)))
    | ~ v1_relat_1(sK5(sK2)) ),
    inference(resolution,[],[f85,f45])).

fof(f85,plain,(
    r1_tarski(k2_relat_1(sK5(sK2)),k1_relat_1(sK2)) ),
    inference(resolution,[],[f75,f40])).

fof(f40,plain,(
    ! [X0] :
      ( sP0(X0)
      | r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f271,plain,(
    k5_relat_1(sK5(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(sK4(sK2),sK2),sK3) ),
    inference(forward_demodulation,[],[f269,f87])).

fof(f87,plain,(
    k5_relat_1(sK4(sK2),sK2) = k5_relat_1(sK5(sK2),sK2) ),
    inference(resolution,[],[f75,f42])).

fof(f42,plain,(
    ! [X0] :
      ( sP0(X0)
      | k5_relat_1(sK4(X0),X0) = k5_relat_1(sK5(X0),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f269,plain,(
    k5_relat_1(sK5(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(sK5(sK2),sK2),sK3) ),
    inference(resolution,[],[f196,f82])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:57:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (13234)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.46  % (13239)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (13234)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (13226)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f280,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f279,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    sK4(sK2) != sK5(sK2)),
% 0.21/0.48    inference(resolution,[],[f75,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0] : (sP0(X0) | sK4(X0) != sK5(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : ((sP0(X0) | ((sK4(X0) != sK5(X0) & k5_relat_1(sK4(X0),X0) = k5_relat_1(sK5(X0),X0) & k1_relat_1(sK4(X0)) = k1_relat_1(sK5(X0)) & r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0)) & r1_tarski(k2_relat_1(sK4(X0)),k1_relat_1(X0)) & v1_funct_1(sK5(X0)) & v1_relat_1(sK5(X0))) & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0)))) & (! [X3] : (! [X4] : (X3 = X4 | k5_relat_1(X3,X0) != k5_relat_1(X4,X0) | k1_relat_1(X3) != k1_relat_1(X4) | ~r1_tarski(k2_relat_1(X4),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X3),k1_relat_1(X0)) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~sP0(X0)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f21,f23,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (sK4(X0) != X2 & k5_relat_1(X2,X0) = k5_relat_1(sK4(X0),X0) & k1_relat_1(X2) = k1_relat_1(sK4(X0)) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(sK4(X0)),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (? [X2] : (sK4(X0) != X2 & k5_relat_1(X2,X0) = k5_relat_1(sK4(X0),X0) & k1_relat_1(X2) = k1_relat_1(sK4(X0)) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(sK4(X0)),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) => (sK4(X0) != sK5(X0) & k5_relat_1(sK4(X0),X0) = k5_relat_1(sK5(X0),X0) & k1_relat_1(sK4(X0)) = k1_relat_1(sK5(X0)) & r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0)) & r1_tarski(k2_relat_1(sK4(X0)),k1_relat_1(X0)) & v1_funct_1(sK5(X0)) & v1_relat_1(sK5(X0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))) & (! [X3] : (! [X4] : (X3 = X4 | k5_relat_1(X3,X0) != k5_relat_1(X4,X0) | k1_relat_1(X3) != k1_relat_1(X4) | ~r1_tarski(k2_relat_1(X4),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X3),k1_relat_1(X0)) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~sP0(X0)))),
% 0.21/0.48    inference(rectify,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (X1 != X2 & k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))) & (! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~sP0(X0)))),
% 0.21/0.48    inference(nnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    ~sP0(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f74,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ~v2_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ~v2_funct_1(sK2) & (k6_relat_1(k1_relat_1(sK2)) = k5_relat_1(sK2,sK3) & v1_funct_1(sK3) & v1_relat_1(sK3)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f7,f17,f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ? [X0] : (~v2_funct_1(X0) & ? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v2_funct_1(sK2) & ? [X1] : (k5_relat_1(sK2,X1) = k6_relat_1(k1_relat_1(sK2)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X1] : (k5_relat_1(sK2,X1) = k6_relat_1(k1_relat_1(sK2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(k1_relat_1(sK2)) = k5_relat_1(sK2,sK3) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : (~v2_funct_1(X0) & ? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f6])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0] : ((~v2_funct_1(X0) & ? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 0.21/0.49    inference(negated_conjecture,[],[f4])).
% 0.21/0.49  fof(f4,conjecture,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    v2_funct_1(sK2) | ~sP0(sK2)),
% 0.21/0.49    inference(resolution,[],[f56,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0] : (v2_funct_1(X0) | ~sP0(X0) | ~sP1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (((v2_funct_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_funct_1(X0))) | ~sP1(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : ((v2_funct_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    sP1(sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f53,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    v1_relat_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    sP1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.49    inference(resolution,[],[f26,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(definition_folding,[],[f10,f14,f13])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0] : ((v2_funct_1(X0) <=> ! [X1] : (! [X2] : (X1 = X2 | k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : ((v2_funct_1(X0) <=> ! [X1] : (! [X2] : ((X1 = X2 | (k5_relat_1(X1,X0) != k5_relat_1(X2,X0) | k1_relat_1(X1) != k1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k5_relat_1(X1,X0) = k5_relat_1(X2,X0) & k1_relat_1(X1) = k1_relat_1(X2) & r1_tarski(k2_relat_1(X2),k1_relat_1(X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(X0))) => X1 = X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_1)).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f279,plain,(
% 0.21/0.49    sK4(sK2) = sK5(sK2)),
% 0.21/0.49    inference(forward_demodulation,[],[f272,f270])).
% 0.21/0.49  fof(f270,plain,(
% 0.21/0.49    sK4(sK2) = k5_relat_1(k5_relat_1(sK4(sK2),sK2),sK3)),
% 0.21/0.49    inference(forward_demodulation,[],[f267,f126])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    sK4(sK2) = k5_relat_1(sK4(sK2),k5_relat_1(sK2,sK3))),
% 0.21/0.49    inference(forward_demodulation,[],[f125,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    k6_relat_1(k1_relat_1(sK2)) = k5_relat_1(sK2,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    sK4(sK2) = k5_relat_1(sK4(sK2),k6_relat_1(k1_relat_1(sK2)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f124,f80])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    v1_relat_1(sK4(sK2))),
% 0.21/0.49    inference(resolution,[],[f75,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0] : (sP0(X0) | v1_relat_1(sK4(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    sK4(sK2) = k5_relat_1(sK4(sK2),k6_relat_1(k1_relat_1(sK2))) | ~v1_relat_1(sK4(sK2))),
% 0.21/0.49    inference(resolution,[],[f84,f45])).
% 0.21/0.49  % (13230)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(sK4(sK2)),k1_relat_1(sK2))),
% 0.21/0.49    inference(resolution,[],[f75,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0] : (sP0(X0) | r1_tarski(k2_relat_1(sK4(X0)),k1_relat_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f267,plain,(
% 0.21/0.49    k5_relat_1(sK4(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(sK4(sK2),sK2),sK3)),
% 0.21/0.49    inference(resolution,[],[f196,f80])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    ( ! [X1] : (~v1_relat_1(X1) | k5_relat_1(X1,k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(X1,sK2),sK3)) )),
% 0.21/0.49    inference(resolution,[],[f47,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    v1_relat_1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~v1_relat_1(X3) | k5_relat_1(k5_relat_1(X2,sK2),X3) = k5_relat_1(X2,k5_relat_1(sK2,X3)) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(resolution,[],[f25,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 0.21/0.49  fof(f272,plain,(
% 0.21/0.49    sK5(sK2) = k5_relat_1(k5_relat_1(sK4(sK2),sK2),sK3)),
% 0.21/0.49    inference(forward_demodulation,[],[f271,f131])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    sK5(sK2) = k5_relat_1(sK5(sK2),k5_relat_1(sK2,sK3))),
% 0.21/0.49    inference(forward_demodulation,[],[f130,f29])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    sK5(sK2) = k5_relat_1(sK5(sK2),k6_relat_1(k1_relat_1(sK2)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f129,f82])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    v1_relat_1(sK5(sK2))),
% 0.21/0.49    inference(resolution,[],[f75,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0] : (sP0(X0) | v1_relat_1(sK5(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    sK5(sK2) = k5_relat_1(sK5(sK2),k6_relat_1(k1_relat_1(sK2))) | ~v1_relat_1(sK5(sK2))),
% 0.21/0.49    inference(resolution,[],[f85,f45])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(sK5(sK2)),k1_relat_1(sK2))),
% 0.21/0.49    inference(resolution,[],[f75,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0] : (sP0(X0) | r1_tarski(k2_relat_1(sK5(X0)),k1_relat_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f271,plain,(
% 0.21/0.49    k5_relat_1(sK5(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(sK4(sK2),sK2),sK3)),
% 0.21/0.49    inference(forward_demodulation,[],[f269,f87])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    k5_relat_1(sK4(sK2),sK2) = k5_relat_1(sK5(sK2),sK2)),
% 0.21/0.49    inference(resolution,[],[f75,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0] : (sP0(X0) | k5_relat_1(sK4(X0),X0) = k5_relat_1(sK5(X0),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f269,plain,(
% 0.21/0.49    k5_relat_1(sK5(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(sK5(sK2),sK2),sK3)),
% 0.21/0.49    inference(resolution,[],[f196,f82])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (13234)------------------------------
% 0.21/0.49  % (13234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13234)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (13234)Memory used [KB]: 1791
% 0.21/0.49  % (13234)Time elapsed: 0.064 s
% 0.21/0.49  % (13234)------------------------------
% 0.21/0.49  % (13234)------------------------------
% 0.21/0.49  % (13225)Success in time 0.126 s
%------------------------------------------------------------------------------
