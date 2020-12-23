%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 591 expanded)
%              Number of leaves         :   15 ( 242 expanded)
%              Depth                    :   20
%              Number of atoms          :  429 (4901 expanded)
%              Number of equality atoms :   87 (1139 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f359,plain,(
    $false ),
    inference(subsumption_resolution,[],[f358,f47])).

fof(f47,plain,(
    sK9 != sK10 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( k1_funct_1(sK8,sK9) = k1_funct_1(sK8,sK10)
      | ~ r2_hidden(k4_tarski(k1_funct_1(sK8,sK9),k1_funct_1(sK8,sK10)),sK7) )
    & sK9 != sK10
    & r2_hidden(k4_tarski(sK9,sK10),sK6)
    & r3_wellord1(sK6,sK7,sK8)
    & v1_funct_1(sK8)
    & v1_relat_1(sK8)
    & v1_relat_1(sK7)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f6,f22,f21,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3,X4] :
                    ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                      | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                    & X3 != X4
                    & r2_hidden(k4_tarski(X3,X4),X0) )
                & r3_wellord1(X0,X1,X2)
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X4,X3] :
                  ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                    | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                  & X3 != X4
                  & r2_hidden(k4_tarski(X3,X4),sK6) )
              & r3_wellord1(sK6,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X4,X3] :
                ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                  | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                & X3 != X4
                & r2_hidden(k4_tarski(X3,X4),sK6) )
            & r3_wellord1(sK6,X1,X2)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ? [X4,X3] :
              ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),sK7) )
              & X3 != X4
              & r2_hidden(k4_tarski(X3,X4),sK6) )
          & r3_wellord1(sK6,sK7,X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ? [X4,X3] :
            ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
              | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),sK7) )
            & X3 != X4
            & r2_hidden(k4_tarski(X3,X4),sK6) )
        & r3_wellord1(sK6,sK7,X2)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ? [X4,X3] :
          ( ( k1_funct_1(sK8,X3) = k1_funct_1(sK8,X4)
            | ~ r2_hidden(k4_tarski(k1_funct_1(sK8,X3),k1_funct_1(sK8,X4)),sK7) )
          & X3 != X4
          & r2_hidden(k4_tarski(X3,X4),sK6) )
      & r3_wellord1(sK6,sK7,sK8)
      & v1_funct_1(sK8)
      & v1_relat_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X4,X3] :
        ( ( k1_funct_1(sK8,X3) = k1_funct_1(sK8,X4)
          | ~ r2_hidden(k4_tarski(k1_funct_1(sK8,X3),k1_funct_1(sK8,X4)),sK7) )
        & X3 != X4
        & r2_hidden(k4_tarski(X3,X4),sK6) )
   => ( ( k1_funct_1(sK8,sK9) = k1_funct_1(sK8,sK10)
        | ~ r2_hidden(k4_tarski(k1_funct_1(sK8,sK9),k1_funct_1(sK8,sK10)),sK7) )
      & sK9 != sK10
      & r2_hidden(k4_tarski(sK9,sK10),sK6) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3,X4] :
                  ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                    | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                  & X3 != X4
                  & r2_hidden(k4_tarski(X3,X4),X0) )
              & r3_wellord1(X0,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3,X4] :
                  ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                    | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                  & X3 != X4
                  & r2_hidden(k4_tarski(X3,X4),X0) )
              & r3_wellord1(X0,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( r3_wellord1(X0,X1,X2)
                 => ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                     => ( ( k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
                          & r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                        | X3 = X4 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
               => ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X0)
                   => ( ( k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
                        & r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                      | X3 = X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_wellord1)).

fof(f358,plain,(
    sK9 = sK10 ),
    inference(trivial_inequality_removal,[],[f354])).

fof(f354,plain,
    ( sK9 = sK10
    | k1_funct_1(sK8,sK9) != k1_funct_1(sK8,sK9) ),
    inference(resolution,[],[f328,f239])).

fof(f239,plain,(
    r2_hidden(sK9,k1_relat_1(sK8)) ),
    inference(forward_demodulation,[],[f235,f122])).

fof(f122,plain,(
    k1_relat_1(sK8) = k3_relat_1(sK6) ),
    inference(resolution,[],[f121,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X1) = k3_relat_1(X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ~ sP1(X2,X1,X0)
        | ~ v2_funct_1(X1)
        | k3_relat_1(X0) != k2_relat_1(X1)
        | k1_relat_1(X1) != k3_relat_1(X2) )
      & ( ( sP1(X2,X1,X0)
          & v2_funct_1(X1)
          & k3_relat_1(X0) = k2_relat_1(X1)
          & k1_relat_1(X1) = k3_relat_1(X2) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X1,X2,X0] :
      ( ( sP2(X1,X2,X0)
        | ~ sP1(X0,X2,X1)
        | ~ v2_funct_1(X2)
        | k2_relat_1(X2) != k3_relat_1(X1)
        | k1_relat_1(X2) != k3_relat_1(X0) )
      & ( ( sP1(X0,X2,X1)
          & v2_funct_1(X2)
          & k2_relat_1(X2) = k3_relat_1(X1)
          & k1_relat_1(X2) = k3_relat_1(X0) )
        | ~ sP2(X1,X2,X0) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X1,X2,X0] :
      ( ( sP2(X1,X2,X0)
        | ~ sP1(X0,X2,X1)
        | ~ v2_funct_1(X2)
        | k2_relat_1(X2) != k3_relat_1(X1)
        | k1_relat_1(X2) != k3_relat_1(X0) )
      & ( ( sP1(X0,X2,X1)
          & v2_funct_1(X2)
          & k2_relat_1(X2) = k3_relat_1(X1)
          & k1_relat_1(X2) = k3_relat_1(X0) )
        | ~ sP2(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X1,X2,X0] :
      ( sP2(X1,X2,X0)
    <=> ( sP1(X0,X2,X1)
        & v2_funct_1(X2)
        & k2_relat_1(X2) = k3_relat_1(X1)
        & k1_relat_1(X2) = k3_relat_1(X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f121,plain,(
    sP2(sK7,sK8,sK6) ),
    inference(subsumption_resolution,[],[f91,f115])).

fof(f115,plain,(
    sP3(sK6,sK8,sK7) ),
    inference(resolution,[],[f98,f41])).

fof(f41,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f23])).

fof(f98,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | sP3(X1,sK8,sK7) ) ),
    inference(resolution,[],[f88,f42])).

fof(f42,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f23])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | sP3(X0,sK8,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f86,f43])).

fof(f43,plain,(
    v1_relat_1(sK8) ),
    inference(cnf_transformation,[],[f23])).

fof(f86,plain,(
    ! [X0,X1] :
      ( sP3(X0,sK8,X1)
      | ~ v1_relat_1(sK8)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f44,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X2,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP3(X0,X2,X1)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f8,f14,f13,f12,f11])).

fof(f11,plain,(
    ! [X1,X4,X2,X3,X0] :
      ( sP0(X1,X4,X2,X3,X0)
    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
        & r2_hidden(X4,k3_relat_1(X0))
        & r2_hidden(X3,k3_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f12,plain,(
    ! [X0,X2,X1] :
      ( sP1(X0,X2,X1)
    <=> ! [X3,X4] :
          ( r2_hidden(k4_tarski(X3,X4),X0)
        <=> sP0(X1,X4,X2,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f14,plain,(
    ! [X0,X2,X1] :
      ( ( r3_wellord1(X0,X1,X2)
      <=> sP2(X1,X2,X0) )
      | ~ sP3(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_wellord1)).

fof(f44,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f23])).

fof(f91,plain,
    ( sP2(sK7,sK8,sK6)
    | ~ sP3(sK6,sK8,sK7) ),
    inference(resolution,[],[f45,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X1,X0)
      | ~ r3_wellord1(X0,X2,X1)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_wellord1(X0,X2,X1)
          | ~ sP2(X2,X1,X0) )
        & ( sP2(X2,X1,X0)
          | ~ r3_wellord1(X0,X2,X1) ) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X2,X1] :
      ( ( ( r3_wellord1(X0,X1,X2)
          | ~ sP2(X1,X2,X0) )
        & ( sP2(X1,X2,X0)
          | ~ r3_wellord1(X0,X1,X2) ) )
      | ~ sP3(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f45,plain,(
    r3_wellord1(sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f23])).

fof(f235,plain,(
    r2_hidden(sK9,k3_relat_1(sK6)) ),
    inference(resolution,[],[f231,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X3,k3_relat_1(X4))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X1)),X0)
        | ~ r2_hidden(X1,k3_relat_1(X4))
        | ~ r2_hidden(X3,k3_relat_1(X4)) )
      & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X1)),X0)
          & r2_hidden(X1,k3_relat_1(X4))
          & r2_hidden(X3,k3_relat_1(X4)) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X1,X4,X2,X3,X0] :
      ( ( sP0(X1,X4,X2,X3,X0)
        | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
        | ~ r2_hidden(X4,k3_relat_1(X0))
        | ~ r2_hidden(X3,k3_relat_1(X0)) )
      & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
          & r2_hidden(X4,k3_relat_1(X0))
          & r2_hidden(X3,k3_relat_1(X0)) )
        | ~ sP0(X1,X4,X2,X3,X0) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X1,X4,X2,X3,X0] :
      ( ( sP0(X1,X4,X2,X3,X0)
        | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
        | ~ r2_hidden(X4,k3_relat_1(X0))
        | ~ r2_hidden(X3,k3_relat_1(X0)) )
      & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
          & r2_hidden(X4,k3_relat_1(X0))
          & r2_hidden(X3,k3_relat_1(X0)) )
        | ~ sP0(X1,X4,X2,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f231,plain,(
    sP0(sK7,sK10,sK8,sK9,sK6) ),
    inference(resolution,[],[f94,f125])).

fof(f125,plain,(
    sP1(sK6,sK8,sK7) ),
    inference(resolution,[],[f121,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ sP1(sK6,X1,X0)
      | sP0(X0,sK10,X1,sK9,sK6) ) ),
    inference(resolution,[],[f46,f56])).

fof(f56,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( sP0(X2,X6,X1,X5,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X2,sK12(X0,X1,X2),X1,sK11(X0,X1,X2),X0)
            | ~ r2_hidden(k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)),X0) )
          & ( sP0(X2,sK12(X0,X1,X2),X1,sK11(X0,X1,X2),X0)
            | r2_hidden(k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)),X0) ) ) )
      & ( ! [X5,X6] :
            ( ( r2_hidden(k4_tarski(X5,X6),X0)
              | ~ sP0(X2,X6,X1,X5,X0) )
            & ( sP0(X2,X6,X1,X5,X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ sP0(X2,X4,X1,X3,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          & ( sP0(X2,X4,X1,X3,X0)
            | r2_hidden(k4_tarski(X3,X4),X0) ) )
     => ( ( ~ sP0(X2,sK12(X0,X1,X2),X1,sK11(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)),X0) )
        & ( sP0(X2,sK12(X0,X1,X2),X1,sK11(X0,X1,X2),X0)
          | r2_hidden(k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3,X4] :
            ( ( ~ sP0(X2,X4,X1,X3,X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            & ( sP0(X2,X4,X1,X3,X0)
              | r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      & ( ! [X5,X6] :
            ( ( r2_hidden(k4_tarski(X5,X6),X0)
              | ~ sP0(X2,X6,X1,X5,X0) )
            & ( sP0(X2,X6,X1,X5,X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X2,X1] :
      ( ( sP1(X0,X2,X1)
        | ? [X3,X4] :
            ( ( ~ sP0(X1,X4,X2,X3,X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            & ( sP0(X1,X4,X2,X3,X0)
              | r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      & ( ! [X3,X4] :
            ( ( r2_hidden(k4_tarski(X3,X4),X0)
              | ~ sP0(X1,X4,X2,X3,X0) )
            & ( sP0(X1,X4,X2,X3,X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
        | ~ sP1(X0,X2,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f46,plain,(
    r2_hidden(k4_tarski(sK9,sK10),sK6) ),
    inference(cnf_transformation,[],[f23])).

fof(f328,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK8))
      | sK10 = X0
      | k1_funct_1(sK8,sK9) != k1_funct_1(sK8,X0) ) ),
    inference(subsumption_resolution,[],[f327,f237])).

fof(f237,plain,(
    r2_hidden(k4_tarski(k1_funct_1(sK8,sK9),k1_funct_1(sK8,sK10)),sK7) ),
    inference(resolution,[],[f231,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X1)),X0)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f327,plain,(
    ! [X0] :
      ( k1_funct_1(sK8,sK9) != k1_funct_1(sK8,X0)
      | sK10 = X0
      | ~ r2_hidden(X0,k1_relat_1(sK8))
      | ~ r2_hidden(k4_tarski(k1_funct_1(sK8,sK9),k1_funct_1(sK8,sK10)),sK7) ) ),
    inference(subsumption_resolution,[],[f326,f129])).

fof(f129,plain,(
    sP4(sK8) ),
    inference(subsumption_resolution,[],[f127,f87])).

fof(f87,plain,(
    sP5(sK8) ),
    inference(subsumption_resolution,[],[f85,f43])).

fof(f85,plain,
    ( sP5(sK8)
    | ~ v1_relat_1(sK8) ),
    inference(resolution,[],[f44,f72])).

fof(f72,plain,(
    ! [X0] :
      ( sP5(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( sP5(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f10,f17,f16])).

fof(f16,plain,(
    ! [X0] :
      ( sP4(X0)
    <=> ! [X1,X2] :
          ( X1 = X2
          | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
          | ~ r2_hidden(X2,k1_relat_1(X0))
          | ~ r2_hidden(X1,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> sP4(X0) )
      | ~ sP5(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f127,plain,
    ( sP4(sK8)
    | ~ sP5(sK8) ),
    inference(resolution,[],[f124,f65])).

fof(f65,plain,(
    ! [X0] :
      ( sP4(X0)
      | ~ v2_funct_1(X0)
      | ~ sP5(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ~ sP4(X0) )
        & ( sP4(X0)
          | ~ v2_funct_1(X0) ) )
      | ~ sP5(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f124,plain,(
    v2_funct_1(sK8) ),
    inference(resolution,[],[f121,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X1)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f326,plain,(
    ! [X0] :
      ( k1_funct_1(sK8,sK9) != k1_funct_1(sK8,X0)
      | sK10 = X0
      | ~ r2_hidden(X0,k1_relat_1(sK8))
      | ~ sP4(sK8)
      | ~ r2_hidden(k4_tarski(k1_funct_1(sK8,sK9),k1_funct_1(sK8,sK10)),sK7) ) ),
    inference(subsumption_resolution,[],[f105,f240])).

fof(f240,plain,(
    r2_hidden(sK10,k1_relat_1(sK8)) ),
    inference(forward_demodulation,[],[f236,f122])).

fof(f236,plain,(
    r2_hidden(sK10,k3_relat_1(sK6)) ),
    inference(resolution,[],[f231,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X1,k3_relat_1(X4))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f105,plain,(
    ! [X0] :
      ( k1_funct_1(sK8,sK9) != k1_funct_1(sK8,X0)
      | sK10 = X0
      | ~ r2_hidden(sK10,k1_relat_1(sK8))
      | ~ r2_hidden(X0,k1_relat_1(sK8))
      | ~ sP4(sK8)
      | ~ r2_hidden(k4_tarski(k1_funct_1(sK8,sK9),k1_funct_1(sK8,sK10)),sK7) ) ),
    inference(superposition,[],[f67,f48])).

fof(f48,plain,
    ( k1_funct_1(sK8,sK9) = k1_funct_1(sK8,sK10)
    | ~ r2_hidden(k4_tarski(k1_funct_1(sK8,sK9),k1_funct_1(sK8,sK10)),sK7) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ sP4(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( sP4(X0)
        | ( sK13(X0) != sK14(X0)
          & k1_funct_1(X0,sK13(X0)) = k1_funct_1(X0,sK14(X0))
          & r2_hidden(sK14(X0),k1_relat_1(X0))
          & r2_hidden(sK13(X0),k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP4(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14])],[f38,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK13(X0) != sK14(X0)
        & k1_funct_1(X0,sK13(X0)) = k1_funct_1(X0,sK14(X0))
        & r2_hidden(sK14(X0),k1_relat_1(X0))
        & r2_hidden(sK13(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( sP4(X0)
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
        | ~ sP4(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( sP4(X0)
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
        | ~ sP4(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:54:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (11166)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.47  % (11175)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.48  % (11159)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.48  % (11160)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.49  % (11168)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.49  % (11165)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.49  % (11157)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.49  % (11157)Refutation not found, incomplete strategy% (11157)------------------------------
% 0.21/0.49  % (11157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (11157)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (11157)Memory used [KB]: 10490
% 0.21/0.49  % (11157)Time elapsed: 0.080 s
% 0.21/0.49  % (11157)------------------------------
% 0.21/0.49  % (11157)------------------------------
% 0.21/0.50  % (11179)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (11182)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.50  % (11165)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f359,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f358,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    sK9 != sK10),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ((((k1_funct_1(sK8,sK9) = k1_funct_1(sK8,sK10) | ~r2_hidden(k4_tarski(k1_funct_1(sK8,sK9),k1_funct_1(sK8,sK10)),sK7)) & sK9 != sK10 & r2_hidden(k4_tarski(sK9,sK10),sK6)) & r3_wellord1(sK6,sK7,sK8) & v1_funct_1(sK8) & v1_relat_1(sK8)) & v1_relat_1(sK7)) & v1_relat_1(sK6)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f6,f22,f21,f20,f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),X0)) & r3_wellord1(X0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (? [X4,X3] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),sK6)) & r3_wellord1(sK6,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK6))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (? [X4,X3] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),sK6)) & r3_wellord1(sK6,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (? [X4,X3] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),sK7)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),sK6)) & r3_wellord1(sK6,sK7,X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(sK7))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ? [X2] : (? [X4,X3] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),sK7)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),sK6)) & r3_wellord1(sK6,sK7,X2) & v1_funct_1(X2) & v1_relat_1(X2)) => (? [X4,X3] : ((k1_funct_1(sK8,X3) = k1_funct_1(sK8,X4) | ~r2_hidden(k4_tarski(k1_funct_1(sK8,X3),k1_funct_1(sK8,X4)),sK7)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),sK6)) & r3_wellord1(sK6,sK7,sK8) & v1_funct_1(sK8) & v1_relat_1(sK8))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ? [X4,X3] : ((k1_funct_1(sK8,X3) = k1_funct_1(sK8,X4) | ~r2_hidden(k4_tarski(k1_funct_1(sK8,X3),k1_funct_1(sK8,X4)),sK7)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),sK6)) => ((k1_funct_1(sK8,sK9) = k1_funct_1(sK8,sK10) | ~r2_hidden(k4_tarski(k1_funct_1(sK8,sK9),k1_funct_1(sK8,sK10)),sK7)) & sK9 != sK10 & r2_hidden(k4_tarski(sK9,sK10),sK6))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f6,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),X0)) & r3_wellord1(X0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f5])).
% 0.21/0.50  fof(f5,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((? [X3,X4] : (((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) & X3 != X4) & r2_hidden(k4_tarski(X3,X4),X0)) & r3_wellord1(X0,X1,X2)) & (v1_funct_1(X2) & v1_relat_1(X2))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r3_wellord1(X0,X1,X2) => ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) => ((k1_funct_1(X2,X3) != k1_funct_1(X2,X4) & r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) | X3 = X4))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f3])).
% 0.21/0.50  fof(f3,conjecture,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r3_wellord1(X0,X1,X2) => ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) => ((k1_funct_1(X2,X3) != k1_funct_1(X2,X4) & r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) | X3 = X4))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_wellord1)).
% 0.21/0.50  fof(f358,plain,(
% 0.21/0.50    sK9 = sK10),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f354])).
% 0.21/0.50  fof(f354,plain,(
% 0.21/0.50    sK9 = sK10 | k1_funct_1(sK8,sK9) != k1_funct_1(sK8,sK9)),
% 0.21/0.50    inference(resolution,[],[f328,f239])).
% 0.21/0.50  fof(f239,plain,(
% 0.21/0.50    r2_hidden(sK9,k1_relat_1(sK8))),
% 0.21/0.50    inference(forward_demodulation,[],[f235,f122])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    k1_relat_1(sK8) = k3_relat_1(sK6)),
% 0.21/0.50    inference(resolution,[],[f121,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relat_1(X1) = k3_relat_1(X2) | ~sP2(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ~sP1(X2,X1,X0) | ~v2_funct_1(X1) | k3_relat_1(X0) != k2_relat_1(X1) | k1_relat_1(X1) != k3_relat_1(X2)) & ((sP1(X2,X1,X0) & v2_funct_1(X1) & k3_relat_1(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k3_relat_1(X2)) | ~sP2(X0,X1,X2)))),
% 0.21/0.50    inference(rectify,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X1,X2,X0] : ((sP2(X1,X2,X0) | ~sP1(X0,X2,X1) | ~v2_funct_1(X2) | k2_relat_1(X2) != k3_relat_1(X1) | k1_relat_1(X2) != k3_relat_1(X0)) & ((sP1(X0,X2,X1) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k1_relat_1(X2) = k3_relat_1(X0)) | ~sP2(X1,X2,X0)))),
% 0.21/0.50    inference(flattening,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X1,X2,X0] : ((sP2(X1,X2,X0) | (~sP1(X0,X2,X1) | ~v2_funct_1(X2) | k2_relat_1(X2) != k3_relat_1(X1) | k1_relat_1(X2) != k3_relat_1(X0))) & ((sP1(X0,X2,X1) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k1_relat_1(X2) = k3_relat_1(X0)) | ~sP2(X1,X2,X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X1,X2,X0] : (sP2(X1,X2,X0) <=> (sP1(X0,X2,X1) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k1_relat_1(X2) = k3_relat_1(X0)))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    sP2(sK7,sK8,sK6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f91,f115])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    sP3(sK6,sK8,sK7)),
% 0.21/0.50    inference(resolution,[],[f98,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    v1_relat_1(sK6)),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    ( ! [X1] : (~v1_relat_1(X1) | sP3(X1,sK8,sK7)) )),
% 0.21/0.50    inference(resolution,[],[f88,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    v1_relat_1(sK7)),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | sP3(X0,sK8,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f86,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    v1_relat_1(sK8)),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sP3(X0,sK8,X1) | ~v1_relat_1(sK8) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(resolution,[],[f44,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sP3(X0,X2,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (sP3(X0,X2,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(definition_folding,[],[f8,f14,f13,f12,f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X1,X4,X2,X3,X0] : (sP0(X1,X4,X2,X3,X0) <=> (r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0))))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X2,X1] : (sP1(X0,X2,X1) <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) <=> sP0(X1,X4,X2,X3,X0)))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X2,X1] : ((r3_wellord1(X0,X1,X2) <=> sP2(X1,X2,X0)) | ~sP3(X0,X2,X1))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r3_wellord1(X0,X1,X2) <=> (! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) <=> (r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0)))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k1_relat_1(X2) = k3_relat_1(X0))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f7])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r3_wellord1(X0,X1,X2) <=> (! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) <=> (r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0)))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k1_relat_1(X2) = k3_relat_1(X0))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r3_wellord1(X0,X1,X2) <=> (! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) <=> (r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0)))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k1_relat_1(X2) = k3_relat_1(X0))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_wellord1)).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    v1_funct_1(sK8)),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    sP2(sK7,sK8,sK6) | ~sP3(sK6,sK8,sK7)),
% 0.21/0.50    inference(resolution,[],[f45,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sP2(X2,X1,X0) | ~r3_wellord1(X0,X2,X1) | ~sP3(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r3_wellord1(X0,X2,X1) | ~sP2(X2,X1,X0)) & (sP2(X2,X1,X0) | ~r3_wellord1(X0,X2,X1))) | ~sP3(X0,X1,X2))),
% 0.21/0.50    inference(rectify,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X2,X1] : (((r3_wellord1(X0,X1,X2) | ~sP2(X1,X2,X0)) & (sP2(X1,X2,X0) | ~r3_wellord1(X0,X1,X2))) | ~sP3(X0,X2,X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f14])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    r3_wellord1(sK6,sK7,sK8)),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f235,plain,(
% 0.21/0.50    r2_hidden(sK9,k3_relat_1(sK6))),
% 0.21/0.50    inference(resolution,[],[f231,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X3,k3_relat_1(X4)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X1)),X0) | ~r2_hidden(X1,k3_relat_1(X4)) | ~r2_hidden(X3,k3_relat_1(X4))) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X1)),X0) & r2_hidden(X1,k3_relat_1(X4)) & r2_hidden(X3,k3_relat_1(X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 0.21/0.50    inference(rectify,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X1,X4,X2,X3,X0] : ((sP0(X1,X4,X2,X3,X0) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0))) | ~sP0(X1,X4,X2,X3,X0)))),
% 0.21/0.50    inference(flattening,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X1,X4,X2,X3,X0] : ((sP0(X1,X4,X2,X3,X0) | (~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)))) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0))) | ~sP0(X1,X4,X2,X3,X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f11])).
% 0.21/0.50  fof(f231,plain,(
% 0.21/0.50    sP0(sK7,sK10,sK8,sK9,sK6)),
% 0.21/0.50    inference(resolution,[],[f94,f125])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    sP1(sK6,sK8,sK7)),
% 0.21/0.50    inference(resolution,[],[f121,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sP1(X2,X1,X0) | ~sP2(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~sP1(sK6,X1,X0) | sP0(X0,sK10,X1,sK9,sK6)) )),
% 0.21/0.50    inference(resolution,[],[f46,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X6,X2,X0,X5,X1] : (sP0(X2,X6,X1,X5,X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~sP1(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X2,sK12(X0,X1,X2),X1,sK11(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)),X0)) & (sP0(X2,sK12(X0,X1,X2),X1,sK11(X0,X1,X2),X0) | r2_hidden(k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)),X0)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X0) | ~sP0(X2,X6,X1,X5,X0)) & (sP0(X2,X6,X1,X5,X0) | ~r2_hidden(k4_tarski(X5,X6),X0))) | ~sP1(X0,X1,X2)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f30,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X3,X4] : ((~sP0(X2,X4,X1,X3,X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) & (sP0(X2,X4,X1,X3,X0) | r2_hidden(k4_tarski(X3,X4),X0))) => ((~sP0(X2,sK12(X0,X1,X2),X1,sK11(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)),X0)) & (sP0(X2,sK12(X0,X1,X2),X1,sK11(X0,X1,X2),X0) | r2_hidden(k4_tarski(sK11(X0,X1,X2),sK12(X0,X1,X2)),X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3,X4] : ((~sP0(X2,X4,X1,X3,X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) & (sP0(X2,X4,X1,X3,X0) | r2_hidden(k4_tarski(X3,X4),X0)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X0) | ~sP0(X2,X6,X1,X5,X0)) & (sP0(X2,X6,X1,X5,X0) | ~r2_hidden(k4_tarski(X5,X6),X0))) | ~sP1(X0,X1,X2)))),
% 0.21/0.50    inference(rectify,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X2,X1] : ((sP1(X0,X2,X1) | ? [X3,X4] : ((~sP0(X1,X4,X2,X3,X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) & (sP0(X1,X4,X2,X3,X0) | r2_hidden(k4_tarski(X3,X4),X0)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X0) | ~sP0(X1,X4,X2,X3,X0)) & (sP0(X1,X4,X2,X3,X0) | ~r2_hidden(k4_tarski(X3,X4),X0))) | ~sP1(X0,X2,X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f12])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    r2_hidden(k4_tarski(sK9,sK10),sK6)),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f328,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK8)) | sK10 = X0 | k1_funct_1(sK8,sK9) != k1_funct_1(sK8,X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f327,f237])).
% 0.21/0.50  fof(f237,plain,(
% 0.21/0.50    r2_hidden(k4_tarski(k1_funct_1(sK8,sK9),k1_funct_1(sK8,sK10)),sK7)),
% 0.21/0.50    inference(resolution,[],[f231,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X1)),X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f327,plain,(
% 0.21/0.50    ( ! [X0] : (k1_funct_1(sK8,sK9) != k1_funct_1(sK8,X0) | sK10 = X0 | ~r2_hidden(X0,k1_relat_1(sK8)) | ~r2_hidden(k4_tarski(k1_funct_1(sK8,sK9),k1_funct_1(sK8,sK10)),sK7)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f326,f129])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    sP4(sK8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f127,f87])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    sP5(sK8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f85,f43])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    sP5(sK8) | ~v1_relat_1(sK8)),
% 0.21/0.50    inference(resolution,[],[f44,f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X0] : (sP5(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (sP5(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(definition_folding,[],[f10,f17,f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (sP4(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : ((v2_funct_1(X0) <=> sP4(X0)) | ~sP5(X0))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    sP4(sK8) | ~sP5(sK8)),
% 0.21/0.50    inference(resolution,[],[f124,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0] : (sP4(X0) | ~v2_funct_1(X0) | ~sP5(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0] : (((v2_funct_1(X0) | ~sP4(X0)) & (sP4(X0) | ~v2_funct_1(X0))) | ~sP5(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f17])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    v2_funct_1(sK8)),
% 0.21/0.50    inference(resolution,[],[f121,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v2_funct_1(X1) | ~sP2(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f326,plain,(
% 0.21/0.50    ( ! [X0] : (k1_funct_1(sK8,sK9) != k1_funct_1(sK8,X0) | sK10 = X0 | ~r2_hidden(X0,k1_relat_1(sK8)) | ~sP4(sK8) | ~r2_hidden(k4_tarski(k1_funct_1(sK8,sK9),k1_funct_1(sK8,sK10)),sK7)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f105,f240])).
% 0.21/0.50  fof(f240,plain,(
% 0.21/0.50    r2_hidden(sK10,k1_relat_1(sK8))),
% 0.21/0.50    inference(forward_demodulation,[],[f236,f122])).
% 0.21/0.50  fof(f236,plain,(
% 0.21/0.50    r2_hidden(sK10,k3_relat_1(sK6))),
% 0.21/0.50    inference(resolution,[],[f231,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X1,k3_relat_1(X4)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    ( ! [X0] : (k1_funct_1(sK8,sK9) != k1_funct_1(sK8,X0) | sK10 = X0 | ~r2_hidden(sK10,k1_relat_1(sK8)) | ~r2_hidden(X0,k1_relat_1(sK8)) | ~sP4(sK8) | ~r2_hidden(k4_tarski(k1_funct_1(sK8,sK9),k1_funct_1(sK8,sK10)),sK7)) )),
% 0.21/0.50    inference(superposition,[],[f67,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    k1_funct_1(sK8,sK9) = k1_funct_1(sK8,sK10) | ~r2_hidden(k4_tarski(k1_funct_1(sK8,sK9),k1_funct_1(sK8,sK10)),sK7)),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X4,X0,X3] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~sP4(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0] : ((sP4(X0) | (sK13(X0) != sK14(X0) & k1_funct_1(X0,sK13(X0)) = k1_funct_1(X0,sK14(X0)) & r2_hidden(sK14(X0),k1_relat_1(X0)) & r2_hidden(sK13(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP4(X0)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14])],[f38,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK13(X0) != sK14(X0) & k1_funct_1(X0,sK13(X0)) = k1_funct_1(X0,sK14(X0)) & r2_hidden(sK14(X0),k1_relat_1(X0)) & r2_hidden(sK13(X0),k1_relat_1(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0] : ((sP4(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP4(X0)))),
% 0.21/0.50    inference(rectify,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0] : ((sP4(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~sP4(X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f16])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (11165)------------------------------
% 0.21/0.50  % (11165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (11165)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (11165)Memory used [KB]: 1791
% 0.21/0.50  % (11165)Time elapsed: 0.091 s
% 0.21/0.50  % (11165)------------------------------
% 0.21/0.50  % (11165)------------------------------
% 0.21/0.50  % (11176)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.50  % (11156)Success in time 0.147 s
%------------------------------------------------------------------------------
