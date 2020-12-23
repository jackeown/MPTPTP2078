%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0794+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:40 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 587 expanded)
%              Number of leaves         :   18 ( 241 expanded)
%              Depth                    :   29
%              Number of atoms          :  523 (5033 expanded)
%              Number of equality atoms :   90 (1144 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f192,plain,(
    $false ),
    inference(global_subsumption,[],[f39,f191])).

fof(f191,plain,(
    ~ v1_relat_1(sK6) ),
    inference(resolution,[],[f187,f42])).

fof(f42,plain,(
    r3_wellord1(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( k1_funct_1(sK7,sK8) = k1_funct_1(sK7,sK9)
      | ~ r2_hidden(k4_tarski(k1_funct_1(sK7,sK8),k1_funct_1(sK7,sK9)),sK6) )
    & sK8 != sK9
    & r2_hidden(k4_tarski(sK8,sK9),sK5)
    & r3_wellord1(sK5,sK6,sK7)
    & v1_funct_1(sK7)
    & v1_relat_1(sK7)
    & v1_relat_1(sK6)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f6,f21,f20,f19,f18])).

fof(f18,plain,
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
                  & r2_hidden(k4_tarski(X3,X4),sK5) )
              & r3_wellord1(sK5,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X4,X3] :
                ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                  | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                & X3 != X4
                & r2_hidden(k4_tarski(X3,X4),sK5) )
            & r3_wellord1(sK5,X1,X2)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ? [X4,X3] :
              ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),sK6) )
              & X3 != X4
              & r2_hidden(k4_tarski(X3,X4),sK5) )
          & r3_wellord1(sK5,sK6,X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( ? [X4,X3] :
            ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
              | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),sK6) )
            & X3 != X4
            & r2_hidden(k4_tarski(X3,X4),sK5) )
        & r3_wellord1(sK5,sK6,X2)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ? [X4,X3] :
          ( ( k1_funct_1(sK7,X3) = k1_funct_1(sK7,X4)
            | ~ r2_hidden(k4_tarski(k1_funct_1(sK7,X3),k1_funct_1(sK7,X4)),sK6) )
          & X3 != X4
          & r2_hidden(k4_tarski(X3,X4),sK5) )
      & r3_wellord1(sK5,sK6,sK7)
      & v1_funct_1(sK7)
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X4,X3] :
        ( ( k1_funct_1(sK7,X3) = k1_funct_1(sK7,X4)
          | ~ r2_hidden(k4_tarski(k1_funct_1(sK7,X3),k1_funct_1(sK7,X4)),sK6) )
        & X3 != X4
        & r2_hidden(k4_tarski(X3,X4),sK5) )
   => ( ( k1_funct_1(sK7,sK8) = k1_funct_1(sK7,sK9)
        | ~ r2_hidden(k4_tarski(k1_funct_1(sK7,sK8),k1_funct_1(sK7,sK9)),sK6) )
      & sK8 != sK9
      & r2_hidden(k4_tarski(sK8,sK9),sK5) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_wellord1)).

fof(f187,plain,(
    ! [X3] :
      ( ~ r3_wellord1(sK5,X3,sK7)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f101,f186])).

fof(f186,plain,(
    ! [X0,X1] : ~ sP0(X0,X1,sK5) ),
    inference(resolution,[],[f185,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ sP15(X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(general_splitting,[],[f71,f72_D])).

fof(f72,plain,(
    ! [X2,X5] :
      ( ~ sP14(X5,X2)
      | sP15(X2) ) ),
    inference(cnf_transformation,[],[f72_D])).

fof(f72_D,plain,(
    ! [X2] :
      ( ! [X5] : ~ sP14(X5,X2)
    <=> ~ sP15(X2) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP15])])).

fof(f71,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ sP14(X5,X2) ) ),
    inference(general_splitting,[],[f54,f70_D])).

fof(f70,plain,(
    ! [X6,X2,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X2)
      | r2_hidden(X6,k3_relat_1(X2))
      | sP14(X5,X2) ) ),
    inference(cnf_transformation,[],[f70_D])).

fof(f70_D,plain,(
    ! [X2,X5] :
      ( ! [X6] :
          ( ~ r2_hidden(k4_tarski(X5,X6),X2)
          | r2_hidden(X6,k3_relat_1(X2)) )
    <=> ~ sP14(X5,X2) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP14])])).

fof(f54,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X6,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X1,sK10(X0,X1,X2)),k1_funct_1(X1,sK11(X0,X1,X2))),X0)
            | ~ r2_hidden(sK11(X0,X1,X2),k3_relat_1(X2))
            | ~ r2_hidden(sK10(X0,X1,X2),k3_relat_1(X2))
            | ~ r2_hidden(k4_tarski(sK10(X0,X1,X2),sK11(X0,X1,X2)),X2) )
          & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,sK10(X0,X1,X2)),k1_funct_1(X1,sK11(X0,X1,X2))),X0)
              & r2_hidden(sK11(X0,X1,X2),k3_relat_1(X2))
              & r2_hidden(sK10(X0,X1,X2),k3_relat_1(X2)) )
            | r2_hidden(k4_tarski(sK10(X0,X1,X2),sK11(X0,X1,X2)),X2) ) ) )
      & ( ! [X5,X6] :
            ( ( r2_hidden(k4_tarski(X5,X6),X2)
              | ~ r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
              | ~ r2_hidden(X6,k3_relat_1(X2))
              | ~ r2_hidden(X5,k3_relat_1(X2)) )
            & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
                & r2_hidden(X6,k3_relat_1(X2))
                & r2_hidden(X5,k3_relat_1(X2)) )
              | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0)
            | ~ r2_hidden(X4,k3_relat_1(X2))
            | ~ r2_hidden(X3,k3_relat_1(X2))
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0)
              & r2_hidden(X4,k3_relat_1(X2))
              & r2_hidden(X3,k3_relat_1(X2)) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X1,sK10(X0,X1,X2)),k1_funct_1(X1,sK11(X0,X1,X2))),X0)
          | ~ r2_hidden(sK11(X0,X1,X2),k3_relat_1(X2))
          | ~ r2_hidden(sK10(X0,X1,X2),k3_relat_1(X2))
          | ~ r2_hidden(k4_tarski(sK10(X0,X1,X2),sK11(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,sK10(X0,X1,X2)),k1_funct_1(X1,sK11(X0,X1,X2))),X0)
            & r2_hidden(sK11(X0,X1,X2),k3_relat_1(X2))
            & r2_hidden(sK10(X0,X1,X2),k3_relat_1(X2)) )
          | r2_hidden(k4_tarski(sK10(X0,X1,X2),sK11(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0)
              | ~ r2_hidden(X4,k3_relat_1(X2))
              | ~ r2_hidden(X3,k3_relat_1(X2))
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,X3),k1_funct_1(X1,X4)),X0)
                & r2_hidden(X4,k3_relat_1(X2))
                & r2_hidden(X3,k3_relat_1(X2)) )
              | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
      & ( ! [X5,X6] :
            ( ( r2_hidden(k4_tarski(X5,X6),X2)
              | ~ r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
              | ~ r2_hidden(X6,k3_relat_1(X2))
              | ~ r2_hidden(X5,k3_relat_1(X2)) )
            & ( ( r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
                & r2_hidden(X6,k3_relat_1(X2))
                & r2_hidden(X5,k3_relat_1(X2)) )
              | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0))
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                & r2_hidden(X4,k3_relat_1(X0))
                & r2_hidden(X3,k3_relat_1(X0)) )
              | r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      & ( ! [X3,X4] :
            ( ( r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
            & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                & r2_hidden(X4,k3_relat_1(X0))
                & r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0))
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                & r2_hidden(X4,k3_relat_1(X0))
                & r2_hidden(X3,k3_relat_1(X0)) )
              | r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      & ( ! [X3,X4] :
            ( ( r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
            & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                & r2_hidden(X4,k3_relat_1(X0))
                & r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ! [X3,X4] :
          ( r2_hidden(k4_tarski(X3,X4),X0)
        <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
            & r2_hidden(X4,k3_relat_1(X0))
            & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f185,plain,(
    sP15(sK5) ),
    inference(global_subsumption,[],[f39,f184])).

fof(f184,plain,
    ( ~ v1_relat_1(sK6)
    | sP15(sK5) ),
    inference(resolution,[],[f183,f42])).

fof(f183,plain,(
    ! [X0] :
      ( ~ r3_wellord1(sK5,X0,sK7)
      | ~ v1_relat_1(X0)
      | sP15(sK5) ) ),
    inference(resolution,[],[f182,f101])).

fof(f182,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1,sK5)
      | sP15(sK5) ) ),
    inference(resolution,[],[f181,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ sP17(X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(general_splitting,[],[f75,f76_D])).

fof(f76,plain,(
    ! [X2,X5] :
      ( r2_hidden(X5,k3_relat_1(X2))
      | ~ sP16(X5,X2)
      | sP17(X2) ) ),
    inference(cnf_transformation,[],[f76_D])).

fof(f76_D,plain,(
    ! [X2] :
      ( ! [X5] :
          ( r2_hidden(X5,k3_relat_1(X2))
          | ~ sP16(X5,X2) )
    <=> ~ sP17(X2) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP17])])).

fof(f75,plain,(
    ! [X2,X0,X5,X1] :
      ( r2_hidden(X5,k3_relat_1(X2))
      | ~ sP0(X0,X1,X2)
      | ~ sP16(X5,X2) ) ),
    inference(general_splitting,[],[f53,f74_D])).

fof(f74,plain,(
    ! [X6,X2,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X2)
      | sP16(X5,X2) ) ),
    inference(cnf_transformation,[],[f74_D])).

fof(f74_D,plain,(
    ! [X2,X5] :
      ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
    <=> ~ sP16(X5,X2) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP16])])).

fof(f53,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f181,plain,
    ( sP17(sK5)
    | sP15(sK5) ),
    inference(resolution,[],[f180,f72])).

fof(f180,plain,
    ( sP14(sK8,sK5)
    | sP17(sK5) ),
    inference(global_subsumption,[],[f80,f179])).

fof(f179,plain,
    ( sP14(sK8,sK5)
    | ~ sP16(sK8,sK5)
    | sP17(sK5) ),
    inference(resolution,[],[f178,f126])).

fof(f126,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(sK7))
      | ~ sP16(X0,sK5)
      | sP17(sK5) ) ),
    inference(superposition,[],[f76,f124])).

fof(f124,plain,(
    k3_relat_1(sK5) = k1_relat_1(sK7) ),
    inference(global_subsumption,[],[f39,f123])).

fof(f123,plain,
    ( ~ v1_relat_1(sK6)
    | k3_relat_1(sK5) = k1_relat_1(sK7) ),
    inference(resolution,[],[f100,f42])).

fof(f100,plain,(
    ! [X2] :
      ( ~ r3_wellord1(sK5,X2,sK7)
      | ~ v1_relat_1(X2)
      | k3_relat_1(sK5) = k1_relat_1(sK7) ) ),
    inference(resolution,[],[f91,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | k3_relat_1(X0) = k1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ~ sP0(X2,X1,X0)
        | ~ v2_funct_1(X1)
        | k2_relat_1(X1) != k3_relat_1(X2)
        | k3_relat_1(X0) != k1_relat_1(X1) )
      & ( ( sP0(X2,X1,X0)
          & v2_funct_1(X1)
          & k2_relat_1(X1) = k3_relat_1(X2)
          & k3_relat_1(X0) = k1_relat_1(X1) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X2,X1] :
      ( ( sP1(X0,X2,X1)
        | ~ sP0(X1,X2,X0)
        | ~ v2_funct_1(X2)
        | k2_relat_1(X2) != k3_relat_1(X1)
        | k1_relat_1(X2) != k3_relat_1(X0) )
      & ( ( sP0(X1,X2,X0)
          & v2_funct_1(X2)
          & k2_relat_1(X2) = k3_relat_1(X1)
          & k1_relat_1(X2) = k3_relat_1(X0) )
        | ~ sP1(X0,X2,X1) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X2,X1] :
      ( ( sP1(X0,X2,X1)
        | ~ sP0(X1,X2,X0)
        | ~ v2_funct_1(X2)
        | k2_relat_1(X2) != k3_relat_1(X1)
        | k1_relat_1(X2) != k3_relat_1(X0) )
      & ( ( sP0(X1,X2,X0)
          & v2_funct_1(X2)
          & k2_relat_1(X2) = k3_relat_1(X1)
          & k1_relat_1(X2) = k3_relat_1(X0) )
        | ~ sP1(X0,X2,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X2,X1] :
      ( sP1(X0,X2,X1)
    <=> ( sP0(X1,X2,X0)
        & v2_funct_1(X2)
        & k2_relat_1(X2) = k3_relat_1(X1)
        & k1_relat_1(X2) = k3_relat_1(X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f91,plain,(
    ! [X1] :
      ( sP1(sK5,sK7,X1)
      | ~ r3_wellord1(sK5,X1,sK7)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f87,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r3_wellord1(X2,X0,X1)
      | sP1(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_wellord1(X2,X0,X1)
          | ~ sP1(X2,X1,X0) )
        & ( sP1(X2,X1,X0)
          | ~ r3_wellord1(X2,X0,X1) ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X1,X2,X0] :
      ( ( ( r3_wellord1(X0,X1,X2)
          | ~ sP1(X0,X2,X1) )
        & ( sP1(X0,X2,X1)
          | ~ r3_wellord1(X0,X1,X2) ) )
      | ~ sP2(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X1,X2,X0] :
      ( ( r3_wellord1(X0,X1,X2)
      <=> sP1(X0,X2,X1) )
      | ~ sP2(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f87,plain,(
    ! [X0] :
      ( sP2(X0,sK7,sK5)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f86,f38])).

fof(f38,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f22])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | sP2(X0,sK7,X1) ) ),
    inference(global_subsumption,[],[f40,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( sP2(X0,sK7,X1)
      | ~ v1_relat_1(sK7)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f61,f41])).

fof(f41,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | sP2(X1,X2,X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP2(X1,X2,X0)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f8,f13,f12,f11])).

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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_wellord1)).

fof(f40,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f22])).

fof(f178,plain,
    ( ~ r2_hidden(sK8,k1_relat_1(sK7))
    | sP14(sK8,sK5) ),
    inference(global_subsumption,[],[f44,f177])).

fof(f177,plain,
    ( ~ r2_hidden(sK8,k1_relat_1(sK7))
    | sK8 = sK9
    | sP14(sK8,sK5) ),
    inference(equality_resolution,[],[f175])).

fof(f175,plain,(
    ! [X1] :
      ( k1_funct_1(sK7,sK8) != k1_funct_1(sK7,X1)
      | ~ r2_hidden(X1,k1_relat_1(sK7))
      | sK9 = X1
      | sP14(sK8,sK5) ) ),
    inference(global_subsumption,[],[f41,f40,f105,f174])).

fof(f174,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK7))
      | k1_funct_1(sK7,sK8) != k1_funct_1(sK7,X1)
      | sK9 = X1
      | sP14(sK8,sK5)
      | ~ v1_relat_1(sK7)
      | ~ v2_funct_1(sK7)
      | ~ v1_funct_1(sK7) ) ),
    inference(resolution,[],[f171,f79])).

fof(f79,plain,(
    ! [X1] :
      ( sP3(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f69,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ sP4(X0)
      | ~ v2_funct_1(X0)
      | sP3(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ~ sP3(X0) )
        & ( sP3(X0)
          | ~ v2_funct_1(X0) ) )
      | ~ sP4(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> sP3(X0) )
      | ~ sP4(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f69,plain,(
    ! [X0] :
      ( sP4(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( sP4(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f10,f16,f15])).

fof(f15,plain,(
    ! [X0] :
      ( sP3(X0)
    <=> ! [X1,X2] :
          ( X1 = X2
          | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
          | ~ r2_hidden(X2,k1_relat_1(X0))
          | ~ r2_hidden(X1,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

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

fof(f171,plain,(
    ! [X0] :
      ( ~ sP3(sK7)
      | ~ r2_hidden(X0,k1_relat_1(sK7))
      | k1_funct_1(sK7,sK8) != k1_funct_1(sK7,X0)
      | sK9 = X0
      | sP14(sK8,sK5) ) ),
    inference(resolution,[],[f167,f125])).

fof(f125,plain,
    ( r2_hidden(sK9,k1_relat_1(sK7))
    | sP14(sK8,sK5) ),
    inference(backward_demodulation,[],[f96,f124])).

fof(f96,plain,
    ( r2_hidden(sK9,k3_relat_1(sK5))
    | sP14(sK8,sK5) ),
    inference(resolution,[],[f70,f43])).

fof(f43,plain,(
    r2_hidden(k4_tarski(sK8,sK9),sK5) ),
    inference(cnf_transformation,[],[f22])).

fof(f167,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK9,k1_relat_1(sK7))
      | sK9 = X0
      | ~ r2_hidden(X0,k1_relat_1(sK7))
      | k1_funct_1(sK7,sK8) != k1_funct_1(sK7,X0)
      | ~ sP3(sK7) ) ),
    inference(superposition,[],[f64,f138])).

fof(f138,plain,(
    k1_funct_1(sK7,sK8) = k1_funct_1(sK7,sK9) ),
    inference(global_subsumption,[],[f42,f39,f137])).

fof(f137,plain,
    ( k1_funct_1(sK7,sK8) = k1_funct_1(sK7,sK9)
    | ~ v1_relat_1(sK6)
    | ~ r3_wellord1(sK5,sK6,sK7) ),
    inference(resolution,[],[f136,f101])).

fof(f136,plain,
    ( ~ sP0(sK6,sK7,sK5)
    | k1_funct_1(sK7,sK8) = k1_funct_1(sK7,sK9) ),
    inference(resolution,[],[f130,f45])).

fof(f45,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(sK7,sK8),k1_funct_1(sK7,sK9)),sK6)
    | k1_funct_1(sK7,sK8) = k1_funct_1(sK7,sK9) ),
    inference(cnf_transformation,[],[f22])).

fof(f130,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(k1_funct_1(X0,sK8),k1_funct_1(X0,sK9)),X1)
      | ~ sP0(X1,X0,sK5) ) ),
    inference(resolution,[],[f55,f43])).

fof(f55,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X2)
      | r2_hidden(k4_tarski(k1_funct_1(X1,X5),k1_funct_1(X1,X6)),X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ sP3(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( sP3(X0)
        | ( sK12(X0) != sK13(X0)
          & k1_funct_1(X0,sK12(X0)) = k1_funct_1(X0,sK13(X0))
          & r2_hidden(sK13(X0),k1_relat_1(X0))
          & r2_hidden(sK12(X0),k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP3(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f35,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK12(X0) != sK13(X0)
        & k1_funct_1(X0,sK12(X0)) = k1_funct_1(X0,sK13(X0))
        & r2_hidden(sK13(X0),k1_relat_1(X0))
        & r2_hidden(sK12(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( sP3(X0)
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
        | ~ sP3(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( sP3(X0)
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
        | ~ sP3(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f105,plain,(
    v2_funct_1(sK7) ),
    inference(global_subsumption,[],[f39,f104])).

fof(f104,plain,
    ( ~ v1_relat_1(sK6)
    | v2_funct_1(sK7) ),
    inference(resolution,[],[f102,f42])).

fof(f102,plain,(
    ! [X4] :
      ( ~ r3_wellord1(sK5,X4,sK7)
      | ~ v1_relat_1(X4)
      | v2_funct_1(sK7) ) ),
    inference(resolution,[],[f91,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | v2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    sK8 != sK9 ),
    inference(cnf_transformation,[],[f22])).

fof(f80,plain,(
    sP16(sK8,sK5) ),
    inference(resolution,[],[f74,f43])).

fof(f101,plain,(
    ! [X3] :
      ( sP0(X3,sK7,sK5)
      | ~ v1_relat_1(X3)
      | ~ r3_wellord1(sK5,X3,sK7) ) ),
    inference(resolution,[],[f91,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f22])).

%------------------------------------------------------------------------------
