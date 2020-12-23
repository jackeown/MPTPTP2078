%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 780 expanded)
%              Number of leaves         :   17 ( 316 expanded)
%              Depth                    :   25
%              Number of atoms          :  547 (7395 expanded)
%              Number of equality atoms :  129 (1762 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f421,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f190,f419])).

fof(f419,plain,(
    ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f418])).

fof(f418,plain,
    ( $false
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f415,f45])).

fof(f45,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)
      | ~ r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1) )
    & sK3 != sK4
    & r2_hidden(k4_tarski(sK3,sK4),sK0)
    & r3_wellord1(sK0,sK1,sK2)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f13,f27,f26,f25,f24])).

fof(f24,plain,
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
                  & r2_hidden(k4_tarski(X3,X4),sK0) )
              & r3_wellord1(sK0,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X4,X3] :
                ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                  | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                & X3 != X4
                & r2_hidden(k4_tarski(X3,X4),sK0) )
            & r3_wellord1(sK0,X1,X2)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ? [X4,X3] :
              ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),sK1) )
              & X3 != X4
              & r2_hidden(k4_tarski(X3,X4),sK0) )
          & r3_wellord1(sK0,sK1,X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ? [X4,X3] :
            ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
              | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),sK1) )
            & X3 != X4
            & r2_hidden(k4_tarski(X3,X4),sK0) )
        & r3_wellord1(sK0,sK1,X2)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ? [X4,X3] :
          ( ( k1_funct_1(sK2,X3) = k1_funct_1(sK2,X4)
            | ~ r2_hidden(k4_tarski(k1_funct_1(sK2,X3),k1_funct_1(sK2,X4)),sK1) )
          & X3 != X4
          & r2_hidden(k4_tarski(X3,X4),sK0) )
      & r3_wellord1(sK0,sK1,sK2)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X4,X3] :
        ( ( k1_funct_1(sK2,X3) = k1_funct_1(sK2,X4)
          | ~ r2_hidden(k4_tarski(k1_funct_1(sK2,X3),k1_funct_1(sK2,X4)),sK1) )
        & X3 != X4
        & r2_hidden(k4_tarski(X3,X4),sK0) )
   => ( ( k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)
        | ~ r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1) )
      & sK3 != sK4
      & r2_hidden(k4_tarski(sK3,sK4),sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f415,plain,
    ( sK3 = sK4
    | ~ spl8_2 ),
    inference(resolution,[],[f403,f72])).

fof(f72,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK7(X0,X1) != X0
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( sK7(X0,X1) = X0
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK7(X0,X1) != X0
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( sK7(X0,X1) = X0
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f403,plain,
    ( r2_hidden(sK4,k1_tarski(sK3))
    | ~ spl8_2 ),
    inference(superposition,[],[f71,f339])).

fof(f339,plain,
    ( k1_tarski(sK3) = k1_tarski(sK4)
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f338,f297])).

fof(f297,plain,(
    k1_tarski(sK3) = k10_relat_1(sK2,k1_tarski(k1_funct_1(sK2,sK3))) ),
    inference(forward_demodulation,[],[f296,f292])).

fof(f292,plain,(
    k1_tarski(k1_funct_1(sK2,sK3)) = k9_relat_1(sK2,k1_tarski(sK3)) ),
    inference(resolution,[],[f173,f91])).

fof(f91,plain,(
    r2_hidden(sK3,k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f89,f39])).

fof(f39,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f89,plain,
    ( r2_hidden(sK3,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f68,f44])).

fof(f44,plain,(
    r2_hidden(k4_tarski(sK3,sK4),sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(f173,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_relat_1(sK0))
      | k1_tarski(k1_funct_1(sK2,X0)) = k9_relat_1(sK2,k1_tarski(X0)) ) ),
    inference(forward_demodulation,[],[f172,f88])).

fof(f88,plain,(
    ! [X2] : k2_relat_1(k7_relat_1(sK2,X2)) = k9_relat_1(sK2,X2) ),
    inference(resolution,[],[f58,f41])).

fof(f41,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f172,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_relat_1(sK0))
      | k2_relat_1(k7_relat_1(sK2,k1_tarski(X0))) = k1_tarski(k1_funct_1(sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f171,f41])).

fof(f171,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_relat_1(sK0))
      | k2_relat_1(k7_relat_1(sK2,k1_tarski(X0))) = k1_tarski(k1_funct_1(sK2,X0))
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f169,f42])).

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f169,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_relat_1(sK0))
      | k2_relat_1(k7_relat_1(sK2,k1_tarski(X0))) = k1_tarski(k1_funct_1(sK2,X0))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f59,f118])).

fof(f118,plain,(
    k3_relat_1(sK0) = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f117,f39])).

fof(f117,plain,
    ( k3_relat_1(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f116,f40])).

fof(f40,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f116,plain,
    ( k3_relat_1(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f115,f41])).

fof(f115,plain,
    ( k3_relat_1(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f114,f42])).

fof(f114,plain,
    ( k3_relat_1(sK0) = k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f47,f43])).

fof(f43,plain,(
    r3_wellord1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,X1,X2)
      | k1_relat_1(X2) = k3_relat_1(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_wellord1(X0,X1,X2)
                  | ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,sK5(X0,X1,X2)),k1_funct_1(X2,sK6(X0,X1,X2))),X1)
                      | ~ r2_hidden(sK6(X0,X1,X2),k3_relat_1(X0))
                      | ~ r2_hidden(sK5(X0,X1,X2),k3_relat_1(X0))
                      | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0) )
                    & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,sK5(X0,X1,X2)),k1_funct_1(X2,sK6(X0,X1,X2))),X1)
                        & r2_hidden(sK6(X0,X1,X2),k3_relat_1(X0))
                        & r2_hidden(sK5(X0,X1,X2),k3_relat_1(X0)) )
                      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0) ) )
                  | ~ v2_funct_1(X2)
                  | k2_relat_1(X2) != k3_relat_1(X1)
                  | k1_relat_1(X2) != k3_relat_1(X0) )
                & ( ( ! [X5,X6] :
                        ( ( r2_hidden(k4_tarski(X5,X6),X0)
                          | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1)
                          | ~ r2_hidden(X6,k3_relat_1(X0))
                          | ~ r2_hidden(X5,k3_relat_1(X0)) )
                        & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1)
                            & r2_hidden(X6,k3_relat_1(X0))
                            & r2_hidden(X5,k3_relat_1(X0)) )
                          | ~ r2_hidden(k4_tarski(X5,X6),X0) ) )
                    & v2_funct_1(X2)
                    & k2_relat_1(X2) = k3_relat_1(X1)
                    & k1_relat_1(X2) = k3_relat_1(X0) )
                  | ~ r3_wellord1(X0,X1,X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
            | ~ r2_hidden(X4,k3_relat_1(X0))
            | ~ r2_hidden(X3,k3_relat_1(X0))
            | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
              & r2_hidden(X4,k3_relat_1(X0))
              & r2_hidden(X3,k3_relat_1(X0)) )
            | r2_hidden(k4_tarski(X3,X4),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,sK5(X0,X1,X2)),k1_funct_1(X2,sK6(X0,X1,X2))),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),k3_relat_1(X0))
          | ~ r2_hidden(sK5(X0,X1,X2),k3_relat_1(X0))
          | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0) )
        & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,sK5(X0,X1,X2)),k1_funct_1(X2,sK6(X0,X1,X2))),X1)
            & r2_hidden(sK6(X0,X1,X2),k3_relat_1(X0))
            & r2_hidden(sK5(X0,X1,X2),k3_relat_1(X0)) )
          | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_wellord1(X0,X1,X2)
                  | ? [X3,X4] :
                      ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        | ~ r2_hidden(X4,k3_relat_1(X0))
                        | ~ r2_hidden(X3,k3_relat_1(X0))
                        | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                      & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                          & r2_hidden(X4,k3_relat_1(X0))
                          & r2_hidden(X3,k3_relat_1(X0)) )
                        | r2_hidden(k4_tarski(X3,X4),X0) ) )
                  | ~ v2_funct_1(X2)
                  | k2_relat_1(X2) != k3_relat_1(X1)
                  | k1_relat_1(X2) != k3_relat_1(X0) )
                & ( ( ! [X5,X6] :
                        ( ( r2_hidden(k4_tarski(X5,X6),X0)
                          | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1)
                          | ~ r2_hidden(X6,k3_relat_1(X0))
                          | ~ r2_hidden(X5,k3_relat_1(X0)) )
                        & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1)
                            & r2_hidden(X6,k3_relat_1(X0))
                            & r2_hidden(X5,k3_relat_1(X0)) )
                          | ~ r2_hidden(k4_tarski(X5,X6),X0) ) )
                    & v2_funct_1(X2)
                    & k2_relat_1(X2) = k3_relat_1(X1)
                    & k1_relat_1(X2) = k3_relat_1(X0) )
                  | ~ r3_wellord1(X0,X1,X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_wellord1(X0,X1,X2)
                  | ? [X3,X4] :
                      ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        | ~ r2_hidden(X4,k3_relat_1(X0))
                        | ~ r2_hidden(X3,k3_relat_1(X0))
                        | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                      & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                          & r2_hidden(X4,k3_relat_1(X0))
                          & r2_hidden(X3,k3_relat_1(X0)) )
                        | r2_hidden(k4_tarski(X3,X4),X0) ) )
                  | ~ v2_funct_1(X2)
                  | k2_relat_1(X2) != k3_relat_1(X1)
                  | k1_relat_1(X2) != k3_relat_1(X0) )
                & ( ( ! [X3,X4] :
                        ( ( r2_hidden(k4_tarski(X3,X4),X0)
                          | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                          | ~ r2_hidden(X4,k3_relat_1(X0))
                          | ~ r2_hidden(X3,k3_relat_1(X0)) )
                        & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                            & r2_hidden(X4,k3_relat_1(X0))
                            & r2_hidden(X3,k3_relat_1(X0)) )
                          | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                    & v2_funct_1(X2)
                    & k2_relat_1(X2) = k3_relat_1(X1)
                    & k1_relat_1(X2) = k3_relat_1(X0) )
                  | ~ r3_wellord1(X0,X1,X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_wellord1(X0,X1,X2)
                  | ? [X3,X4] :
                      ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        | ~ r2_hidden(X4,k3_relat_1(X0))
                        | ~ r2_hidden(X3,k3_relat_1(X0))
                        | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                      & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                          & r2_hidden(X4,k3_relat_1(X0))
                          & r2_hidden(X3,k3_relat_1(X0)) )
                        | r2_hidden(k4_tarski(X3,X4),X0) ) )
                  | ~ v2_funct_1(X2)
                  | k2_relat_1(X2) != k3_relat_1(X1)
                  | k1_relat_1(X2) != k3_relat_1(X0) )
                & ( ( ! [X3,X4] :
                        ( ( r2_hidden(k4_tarski(X3,X4),X0)
                          | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                          | ~ r2_hidden(X4,k3_relat_1(X0))
                          | ~ r2_hidden(X3,k3_relat_1(X0)) )
                        & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                            & r2_hidden(X4,k3_relat_1(X0))
                            & r2_hidden(X3,k3_relat_1(X0)) )
                          | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                    & v2_funct_1(X2)
                    & k2_relat_1(X2) = k3_relat_1(X1)
                    & k1_relat_1(X2) = k3_relat_1(X0) )
                  | ~ r3_wellord1(X0,X1,X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_funct_1)).

fof(f296,plain,(
    k1_tarski(sK3) = k10_relat_1(sK2,k9_relat_1(sK2,k1_tarski(sK3))) ),
    inference(resolution,[],[f236,f176])).

fof(f176,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k3_relat_1(sK0))
      | k10_relat_1(sK2,k9_relat_1(sK2,X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f175,f41])).

fof(f175,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k3_relat_1(sK0))
      | k10_relat_1(sK2,k9_relat_1(sK2,X1)) = X1
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f174,f42])).

fof(f174,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k3_relat_1(sK0))
      | k10_relat_1(sK2,k9_relat_1(sK2,X1)) = X1
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f170,f110])).

fof(f110,plain,(
    v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f109,f39])).

fof(f109,plain,
    ( v2_funct_1(sK2)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f108,f40])).

fof(f108,plain,
    ( v2_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f107,f41])).

fof(f107,plain,
    ( v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f106,f42])).

fof(f106,plain,
    ( v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f49,f43])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,X1,X2)
      | v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f170,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k3_relat_1(sK0))
      | ~ v2_funct_1(sK2)
      | k10_relat_1(sK2,k9_relat_1(sK2,X1)) = X1
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f60,f118])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(f236,plain,(
    r1_tarski(k1_tarski(sK3),k3_relat_1(sK0)) ),
    inference(trivial_inequality_removal,[],[f235])).

fof(f235,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_tarski(sK3),k3_relat_1(sK0)) ),
    inference(superposition,[],[f65,f126])).

fof(f126,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK3),k3_relat_1(sK0)) ),
    inference(resolution,[],[f91,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f338,plain,
    ( k1_tarski(sK4) = k10_relat_1(sK2,k1_tarski(k1_funct_1(sK2,sK3)))
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f337,f295])).

fof(f295,plain,
    ( k1_tarski(k1_funct_1(sK2,sK3)) = k9_relat_1(sK2,k1_tarski(sK4))
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f293,f80])).

fof(f80,plain,
    ( k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl8_2
  <=> k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f293,plain,(
    k1_tarski(k1_funct_1(sK2,sK4)) = k9_relat_1(sK2,k1_tarski(sK4)) ),
    inference(resolution,[],[f173,f94])).

fof(f94,plain,(
    r2_hidden(sK4,k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f92,f39])).

fof(f92,plain,
    ( r2_hidden(sK4,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f69,f44])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f337,plain,(
    k1_tarski(sK4) = k10_relat_1(sK2,k9_relat_1(sK2,k1_tarski(sK4))) ),
    inference(resolution,[],[f240,f176])).

fof(f240,plain,(
    r1_tarski(k1_tarski(sK4),k3_relat_1(sK0)) ),
    inference(trivial_inequality_removal,[],[f239])).

fof(f239,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_tarski(sK4),k3_relat_1(sK0)) ),
    inference(superposition,[],[f65,f150])).

fof(f150,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK4),k3_relat_1(sK0)) ),
    inference(resolution,[],[f94,f67])).

fof(f71,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f190,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f188,f40])).

fof(f188,plain,
    ( ~ v1_relat_1(sK1)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f187,f41])).

fof(f187,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f186,f42])).

fof(f186,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f185,f76])).

fof(f76,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl8_1
  <=> r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f185,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f142,f43])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ r3_wellord1(sK0,X1,X0)
      | r2_hidden(k4_tarski(k1_funct_1(X0,sK3),k1_funct_1(X0,sK4)),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f140,f39])).

fof(f140,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(k1_funct_1(X0,sK3),k1_funct_1(X0,sK4)),X1)
      | ~ r3_wellord1(sK0,X1,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f52,f44])).

fof(f52,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f46,f78,f74])).

fof(f46,plain,
    ( k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)
    | ~ r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:03:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (3797)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.46  % (3797)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (3804)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.47  % (3805)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.48  % (3796)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f421,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f81,f190,f419])).
% 0.21/0.48  fof(f419,plain,(
% 0.21/0.48    ~spl8_2),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f418])).
% 0.21/0.48  fof(f418,plain,(
% 0.21/0.48    $false | ~spl8_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f415,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    sK3 != sK4),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ((((k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4) | ~r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1)) & sK3 != sK4 & r2_hidden(k4_tarski(sK3,sK4),sK0)) & r3_wellord1(sK0,sK1,sK2) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f13,f27,f26,f25,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),X0)) & r3_wellord1(X0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (? [X4,X3] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),sK0)) & r3_wellord1(sK0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ? [X1] : (? [X2] : (? [X4,X3] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),sK0)) & r3_wellord1(sK0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (? [X4,X3] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),sK1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),sK0)) & r3_wellord1(sK0,sK1,X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ? [X2] : (? [X4,X3] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),sK1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),sK0)) & r3_wellord1(sK0,sK1,X2) & v1_funct_1(X2) & v1_relat_1(X2)) => (? [X4,X3] : ((k1_funct_1(sK2,X3) = k1_funct_1(sK2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(sK2,X3),k1_funct_1(sK2,X4)),sK1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),sK0)) & r3_wellord1(sK0,sK1,sK2) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ? [X4,X3] : ((k1_funct_1(sK2,X3) = k1_funct_1(sK2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(sK2,X3),k1_funct_1(sK2,X4)),sK1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),sK0)) => ((k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4) | ~r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1)) & sK3 != sK4 & r2_hidden(k4_tarski(sK3,sK4),sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) & X3 != X4 & r2_hidden(k4_tarski(X3,X4),X0)) & r3_wellord1(X0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : ((? [X3,X4] : (((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) & X3 != X4) & r2_hidden(k4_tarski(X3,X4),X0)) & r3_wellord1(X0,X1,X2)) & (v1_funct_1(X2) & v1_relat_1(X2))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r3_wellord1(X0,X1,X2) => ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) => ((k1_funct_1(X2,X3) != k1_funct_1(X2,X4) & r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) | X3 = X4))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f9])).
% 0.21/0.48  fof(f9,conjecture,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r3_wellord1(X0,X1,X2) => ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) => ((k1_funct_1(X2,X3) != k1_funct_1(X2,X4) & r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)) | X3 = X4))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_wellord1)).
% 0.21/0.48  fof(f415,plain,(
% 0.21/0.48    sK3 = sK4 | ~spl8_2),
% 0.21/0.48    inference(resolution,[],[f403,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.21/0.48    inference(equality_resolution,[],[f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK7(X0,X1) != X0 | ~r2_hidden(sK7(X0,X1),X1)) & (sK7(X0,X1) = X0 | r2_hidden(sK7(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f35,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK7(X0,X1) != X0 | ~r2_hidden(sK7(X0,X1),X1)) & (sK7(X0,X1) = X0 | r2_hidden(sK7(X0,X1),X1))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.48    inference(rectify,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.48  fof(f403,plain,(
% 0.21/0.48    r2_hidden(sK4,k1_tarski(sK3)) | ~spl8_2),
% 0.21/0.48    inference(superposition,[],[f71,f339])).
% 0.21/0.48  fof(f339,plain,(
% 0.21/0.48    k1_tarski(sK3) = k1_tarski(sK4) | ~spl8_2),
% 0.21/0.48    inference(forward_demodulation,[],[f338,f297])).
% 0.21/0.48  fof(f297,plain,(
% 0.21/0.48    k1_tarski(sK3) = k10_relat_1(sK2,k1_tarski(k1_funct_1(sK2,sK3)))),
% 0.21/0.48    inference(forward_demodulation,[],[f296,f292])).
% 0.21/0.48  fof(f292,plain,(
% 0.21/0.48    k1_tarski(k1_funct_1(sK2,sK3)) = k9_relat_1(sK2,k1_tarski(sK3))),
% 0.21/0.48    inference(resolution,[],[f173,f91])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    r2_hidden(sK3,k3_relat_1(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f89,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    v1_relat_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    r2_hidden(sK3,k3_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(resolution,[],[f68,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK3,sK4),sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).
% 0.21/0.48  fof(f173,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k3_relat_1(sK0)) | k1_tarski(k1_funct_1(sK2,X0)) = k9_relat_1(sK2,k1_tarski(X0))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f172,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ( ! [X2] : (k2_relat_1(k7_relat_1(sK2,X2)) = k9_relat_1(sK2,X2)) )),
% 0.21/0.48    inference(resolution,[],[f58,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    v1_relat_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k3_relat_1(sK0)) | k2_relat_1(k7_relat_1(sK2,k1_tarski(X0))) = k1_tarski(k1_funct_1(sK2,X0))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f171,f41])).
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k3_relat_1(sK0)) | k2_relat_1(k7_relat_1(sK2,k1_tarski(X0))) = k1_tarski(k1_funct_1(sK2,X0)) | ~v1_relat_1(sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f169,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    v1_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k3_relat_1(sK0)) | k2_relat_1(k7_relat_1(sK2,k1_tarski(X0))) = k1_tarski(k1_funct_1(sK2,X0)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.48    inference(superposition,[],[f59,f118])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    k3_relat_1(sK0) = k1_relat_1(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f117,f39])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    k3_relat_1(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f116,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    v1_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    k3_relat_1(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f115,f41])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    k3_relat_1(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f114,f42])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    k3_relat_1(sK0) = k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(resolution,[],[f47,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    r3_wellord1(sK0,sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r3_wellord1(X0,X1,X2) | k1_relat_1(X2) = k3_relat_1(X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r3_wellord1(X0,X1,X2) | ((~r2_hidden(k4_tarski(k1_funct_1(X2,sK5(X0,X1,X2)),k1_funct_1(X2,sK6(X0,X1,X2))),X1) | ~r2_hidden(sK6(X0,X1,X2),k3_relat_1(X0)) | ~r2_hidden(sK5(X0,X1,X2),k3_relat_1(X0)) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0)) & ((r2_hidden(k4_tarski(k1_funct_1(X2,sK5(X0,X1,X2)),k1_funct_1(X2,sK6(X0,X1,X2))),X1) & r2_hidden(sK6(X0,X1,X2),k3_relat_1(X0)) & r2_hidden(sK5(X0,X1,X2),k3_relat_1(X0))) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0))) | ~v2_funct_1(X2) | k2_relat_1(X2) != k3_relat_1(X1) | k1_relat_1(X2) != k3_relat_1(X0)) & ((! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1) | ~r2_hidden(X6,k3_relat_1(X0)) | ~r2_hidden(X5,k3_relat_1(X0))) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1) & r2_hidden(X6,k3_relat_1(X0)) & r2_hidden(X5,k3_relat_1(X0))) | ~r2_hidden(k4_tarski(X5,X6),X0))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k1_relat_1(X2) = k3_relat_1(X0)) | ~r3_wellord1(X0,X1,X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f31,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~r2_hidden(k4_tarski(X3,X4),X0)) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0))) | r2_hidden(k4_tarski(X3,X4),X0))) => ((~r2_hidden(k4_tarski(k1_funct_1(X2,sK5(X0,X1,X2)),k1_funct_1(X2,sK6(X0,X1,X2))),X1) | ~r2_hidden(sK6(X0,X1,X2),k3_relat_1(X0)) | ~r2_hidden(sK5(X0,X1,X2),k3_relat_1(X0)) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0)) & ((r2_hidden(k4_tarski(k1_funct_1(X2,sK5(X0,X1,X2)),k1_funct_1(X2,sK6(X0,X1,X2))),X1) & r2_hidden(sK6(X0,X1,X2),k3_relat_1(X0)) & r2_hidden(sK5(X0,X1,X2),k3_relat_1(X0))) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r3_wellord1(X0,X1,X2) | ? [X3,X4] : ((~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~r2_hidden(k4_tarski(X3,X4),X0)) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0))) | r2_hidden(k4_tarski(X3,X4),X0))) | ~v2_funct_1(X2) | k2_relat_1(X2) != k3_relat_1(X1) | k1_relat_1(X2) != k3_relat_1(X0)) & ((! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1) | ~r2_hidden(X6,k3_relat_1(X0)) | ~r2_hidden(X5,k3_relat_1(X0))) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1) & r2_hidden(X6,k3_relat_1(X0)) & r2_hidden(X5,k3_relat_1(X0))) | ~r2_hidden(k4_tarski(X5,X6),X0))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k1_relat_1(X2) = k3_relat_1(X0)) | ~r3_wellord1(X0,X1,X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(rectify,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r3_wellord1(X0,X1,X2) | ? [X3,X4] : ((~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~r2_hidden(k4_tarski(X3,X4),X0)) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0))) | r2_hidden(k4_tarski(X3,X4),X0))) | ~v2_funct_1(X2) | k2_relat_1(X2) != k3_relat_1(X1) | k1_relat_1(X2) != k3_relat_1(X0)) & ((! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(k4_tarski(X3,X4),X0))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k1_relat_1(X2) = k3_relat_1(X0)) | ~r3_wellord1(X0,X1,X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r3_wellord1(X0,X1,X2) | (? [X3,X4] : (((~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(k4_tarski(X3,X4),X0)) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0))) | r2_hidden(k4_tarski(X3,X4),X0))) | ~v2_funct_1(X2) | k2_relat_1(X2) != k3_relat_1(X1) | k1_relat_1(X2) != k3_relat_1(X0))) & ((! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X0) | (~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)))) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(k4_tarski(X3,X4),X0))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k1_relat_1(X2) = k3_relat_1(X0)) | ~r3_wellord1(X0,X1,X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r3_wellord1(X0,X1,X2) <=> (! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) <=> (r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0)))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k1_relat_1(X2) = k3_relat_1(X0))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r3_wellord1(X0,X1,X2) <=> (! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) <=> (r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0)))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k1_relat_1(X2) = k3_relat_1(X0))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r3_wellord1(X0,X1,X2) <=> (! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) <=> (r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0)))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k1_relat_1(X2) = k3_relat_1(X0))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_wellord1)).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : ((k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_funct_1)).
% 0.21/0.48  fof(f296,plain,(
% 0.21/0.48    k1_tarski(sK3) = k10_relat_1(sK2,k9_relat_1(sK2,k1_tarski(sK3)))),
% 0.21/0.48    inference(resolution,[],[f236,f176])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    ( ! [X1] : (~r1_tarski(X1,k3_relat_1(sK0)) | k10_relat_1(sK2,k9_relat_1(sK2,X1)) = X1) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f175,f41])).
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    ( ! [X1] : (~r1_tarski(X1,k3_relat_1(sK0)) | k10_relat_1(sK2,k9_relat_1(sK2,X1)) = X1 | ~v1_relat_1(sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f174,f42])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    ( ! [X1] : (~r1_tarski(X1,k3_relat_1(sK0)) | k10_relat_1(sK2,k9_relat_1(sK2,X1)) = X1 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f170,f110])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    v2_funct_1(sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f109,f39])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    v2_funct_1(sK2) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f108,f40])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    v2_funct_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f107,f41])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f106,f42])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(resolution,[],[f49,f43])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r3_wellord1(X0,X1,X2) | v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    ( ! [X1] : (~r1_tarski(X1,k3_relat_1(sK0)) | ~v2_funct_1(sK2) | k10_relat_1(sK2,k9_relat_1(sK2,X1)) = X1 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.48    inference(superposition,[],[f60,f118])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).
% 0.21/0.48  fof(f236,plain,(
% 0.21/0.48    r1_tarski(k1_tarski(sK3),k3_relat_1(sK0))),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f235])).
% 0.21/0.48  fof(f235,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_tarski(sK3),k3_relat_1(sK0))),
% 0.21/0.48    inference(superposition,[],[f65,f126])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(k1_tarski(sK3),k3_relat_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f91,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 => r1_tarski(X0,X1))),
% 0.21/0.48    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.21/0.48  fof(f338,plain,(
% 0.21/0.48    k1_tarski(sK4) = k10_relat_1(sK2,k1_tarski(k1_funct_1(sK2,sK3))) | ~spl8_2),
% 0.21/0.48    inference(forward_demodulation,[],[f337,f295])).
% 0.21/0.48  fof(f295,plain,(
% 0.21/0.48    k1_tarski(k1_funct_1(sK2,sK3)) = k9_relat_1(sK2,k1_tarski(sK4)) | ~spl8_2),
% 0.21/0.48    inference(forward_demodulation,[],[f293,f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4) | ~spl8_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f78])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    spl8_2 <=> k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.48  fof(f293,plain,(
% 0.21/0.48    k1_tarski(k1_funct_1(sK2,sK4)) = k9_relat_1(sK2,k1_tarski(sK4))),
% 0.21/0.48    inference(resolution,[],[f173,f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    r2_hidden(sK4,k3_relat_1(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f92,f39])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    r2_hidden(sK4,k3_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(resolution,[],[f69,f44])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f337,plain,(
% 0.21/0.48    k1_tarski(sK4) = k10_relat_1(sK2,k9_relat_1(sK2,k1_tarski(sK4)))),
% 0.21/0.48    inference(resolution,[],[f240,f176])).
% 0.21/0.48  fof(f240,plain,(
% 0.21/0.48    r1_tarski(k1_tarski(sK4),k3_relat_1(sK0))),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f239])).
% 0.21/0.48  fof(f239,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_tarski(sK4),k3_relat_1(sK0))),
% 0.21/0.48    inference(superposition,[],[f65,f150])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(k1_tarski(sK4),k3_relat_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f94,f67])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.21/0.48    inference(equality_resolution,[],[f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.21/0.48    inference(equality_resolution,[],[f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f37])).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    spl8_1),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f189])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    $false | spl8_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f188,f40])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    ~v1_relat_1(sK1) | spl8_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f187,f41])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | spl8_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f186,f42])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | spl8_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f185,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ~r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1) | spl8_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f74])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl8_1 <=> r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.48  fof(f185,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1)),
% 0.21/0.48    inference(resolution,[],[f142,f43])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r3_wellord1(sK0,X1,X0) | r2_hidden(k4_tarski(k1_funct_1(X0,sK3),k1_funct_1(X0,sK4)),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f140,f39])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(k4_tarski(k1_funct_1(X0,sK3),k1_funct_1(X0,sK4)),X1) | ~r3_wellord1(sK0,X1,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(sK0)) )),
% 0.21/0.48    inference(resolution,[],[f52,f44])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X6,X2,X0,X5,X1] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ~spl8_1 | spl8_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f46,f78,f74])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4) | ~r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (3797)------------------------------
% 0.21/0.49  % (3797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (3797)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (3797)Memory used [KB]: 10874
% 0.21/0.49  % (3797)Time elapsed: 0.067 s
% 0.21/0.49  % (3797)------------------------------
% 0.21/0.49  % (3797)------------------------------
% 0.21/0.49  % (3786)Success in time 0.133 s
%------------------------------------------------------------------------------
