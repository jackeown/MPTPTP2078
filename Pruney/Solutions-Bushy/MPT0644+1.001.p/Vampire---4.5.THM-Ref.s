%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0644+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:22 EST 2020

% Result     : Theorem 45.26s
% Output     : Refutation 45.26s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 748 expanded)
%              Number of leaves         :   15 ( 234 expanded)
%              Depth                    :   29
%              Number of atoms          :  656 (5241 expanded)
%              Number of equality atoms :  117 (1017 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f72198,plain,(
    $false ),
    inference(subsumption_resolution,[],[f72197,f549])).

fof(f549,plain,(
    r2_hidden(k1_funct_1(sK0,sK7(k1_relat_1(sK0),k2_relat_1(sK1))),k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f548,f44])).

fof(f44,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k2_relat_1(sK1))
    & v2_funct_1(sK0)
    & k2_relat_1(sK0) = k2_relat_1(k5_relat_1(sK1,sK0))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
            & v2_funct_1(X0)
            & k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(sK0),k2_relat_1(X1))
          & v2_funct_1(sK0)
          & k2_relat_1(sK0) = k2_relat_1(k5_relat_1(X1,sK0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k1_relat_1(sK0),k2_relat_1(X1))
        & v2_funct_1(sK0)
        & k2_relat_1(sK0) = k2_relat_1(k5_relat_1(X1,sK0))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k1_relat_1(sK0),k2_relat_1(sK1))
      & v2_funct_1(sK0)
      & k2_relat_1(sK0) = k2_relat_1(k5_relat_1(sK1,sK0))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          & v2_funct_1(X0)
          & k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          & v2_funct_1(X0)
          & k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( v2_funct_1(X0)
                & k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) )
             => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X0)
              & k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) )
           => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_1)).

fof(f548,plain,
    ( r2_hidden(k1_funct_1(sK0,sK7(k1_relat_1(sK0),k2_relat_1(sK1))),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f538,f45])).

fof(f45,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f538,plain,
    ( r2_hidden(k1_funct_1(sK0,sK7(k1_relat_1(sK0),k2_relat_1(sK1))),k2_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f217,f73])).

fof(f73,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f33,f36,f35,f34])).

fof(f34,plain,(
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

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK4(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f217,plain,(
    r2_hidden(sK7(k1_relat_1(sK0),k2_relat_1(sK1)),k1_relat_1(sK0)) ),
    inference(resolution,[],[f50,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f41,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f50,plain,(
    ~ r1_tarski(k1_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f72197,plain,(
    ~ r2_hidden(k1_funct_1(sK0,sK7(k1_relat_1(sK0),k2_relat_1(sK1))),k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f72188,f218])).

fof(f218,plain,(
    ~ r2_hidden(sK7(k1_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    inference(resolution,[],[f50,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f72188,plain,
    ( r2_hidden(sK7(k1_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(sK1))
    | ~ r2_hidden(k1_funct_1(sK0,sK7(k1_relat_1(sK0),k2_relat_1(sK1))),k2_relat_1(sK0)) ),
    inference(superposition,[],[f72165,f60389])).

fof(f60389,plain,(
    sK7(k1_relat_1(sK0),k2_relat_1(sK1)) = sK6(sK0,k1_funct_1(sK0,sK7(k1_relat_1(sK0),k2_relat_1(sK1)))) ),
    inference(subsumption_resolution,[],[f60379,f1228])).

fof(f1228,plain,(
    r2_hidden(sK6(sK0,k1_funct_1(sK0,sK7(k1_relat_1(sK0),k2_relat_1(sK1)))),k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f1227,f44])).

fof(f1227,plain,
    ( r2_hidden(sK6(sK0,k1_funct_1(sK0,sK7(k1_relat_1(sK0),k2_relat_1(sK1)))),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f1218,f45])).

fof(f1218,plain,
    ( r2_hidden(sK6(sK0,k1_funct_1(sK0,sK7(k1_relat_1(sK0),k2_relat_1(sK1)))),k1_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f549,f75])).

fof(f75,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f60379,plain,
    ( sK7(k1_relat_1(sK0),k2_relat_1(sK1)) = sK6(sK0,k1_funct_1(sK0,sK7(k1_relat_1(sK0),k2_relat_1(sK1))))
    | ~ r2_hidden(sK6(sK0,k1_funct_1(sK0,sK7(k1_relat_1(sK0),k2_relat_1(sK1)))),k1_relat_1(sK0)) ),
    inference(trivial_inequality_removal,[],[f60319])).

fof(f60319,plain,
    ( k1_funct_1(sK0,sK7(k1_relat_1(sK0),k2_relat_1(sK1))) != k1_funct_1(sK0,sK7(k1_relat_1(sK0),k2_relat_1(sK1)))
    | sK7(k1_relat_1(sK0),k2_relat_1(sK1)) = sK6(sK0,k1_funct_1(sK0,sK7(k1_relat_1(sK0),k2_relat_1(sK1))))
    | ~ r2_hidden(sK6(sK0,k1_funct_1(sK0,sK7(k1_relat_1(sK0),k2_relat_1(sK1)))),k1_relat_1(sK0)) ),
    inference(superposition,[],[f554,f1230])).

fof(f1230,plain,(
    k1_funct_1(sK0,sK7(k1_relat_1(sK0),k2_relat_1(sK1))) = k1_funct_1(sK0,sK6(sK0,k1_funct_1(sK0,sK7(k1_relat_1(sK0),k2_relat_1(sK1))))) ),
    inference(subsumption_resolution,[],[f1229,f44])).

fof(f1229,plain,
    ( k1_funct_1(sK0,sK7(k1_relat_1(sK0),k2_relat_1(sK1))) = k1_funct_1(sK0,sK6(sK0,k1_funct_1(sK0,sK7(k1_relat_1(sK0),k2_relat_1(sK1)))))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f1219,f45])).

fof(f1219,plain,
    ( k1_funct_1(sK0,sK7(k1_relat_1(sK0),k2_relat_1(sK1))) = k1_funct_1(sK0,sK6(sK0,k1_funct_1(sK0,sK7(k1_relat_1(sK0),k2_relat_1(sK1)))))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f549,f74])).

fof(f74,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f554,plain,(
    ! [X2] :
      ( k1_funct_1(sK0,sK7(k1_relat_1(sK0),k2_relat_1(sK1))) != k1_funct_1(sK0,X2)
      | sK7(k1_relat_1(sK0),k2_relat_1(sK1)) = X2
      | ~ r2_hidden(X2,k1_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f553,f44])).

fof(f553,plain,(
    ! [X2] :
      ( sK7(k1_relat_1(sK0),k2_relat_1(sK1)) = X2
      | k1_funct_1(sK0,sK7(k1_relat_1(sK0),k2_relat_1(sK1))) != k1_funct_1(sK0,X2)
      | ~ r2_hidden(X2,k1_relat_1(sK0))
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f552,f45])).

fof(f552,plain,(
    ! [X2] :
      ( sK7(k1_relat_1(sK0),k2_relat_1(sK1)) = X2
      | k1_funct_1(sK0,sK7(k1_relat_1(sK0),k2_relat_1(sK1))) != k1_funct_1(sK0,X2)
      | ~ r2_hidden(X2,k1_relat_1(sK0))
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f540,f49])).

fof(f49,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f540,plain,(
    ! [X2] :
      ( sK7(k1_relat_1(sK0),k2_relat_1(sK1)) = X2
      | k1_funct_1(sK0,sK7(k1_relat_1(sK0),k2_relat_1(sK1))) != k1_funct_1(sK0,X2)
      | ~ r2_hidden(X2,k1_relat_1(sK0))
      | ~ v2_funct_1(sK0)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f217,f51])).

fof(f51,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK2(X0) != sK3(X0)
            & k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0))
            & r2_hidden(sK3(X0),k1_relat_1(X0))
            & r2_hidden(sK2(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK2(X0) != sK3(X0)
        & k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0))
        & r2_hidden(sK3(X0),k1_relat_1(X0))
        & r2_hidden(sK2(X0),k1_relat_1(X0)) ) ) ),
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f72165,plain,(
    ! [X59] :
      ( r2_hidden(sK6(sK0,X59),k2_relat_1(sK1))
      | ~ r2_hidden(X59,k2_relat_1(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f72164])).

fof(f72164,plain,(
    ! [X59] :
      ( ~ r2_hidden(X59,k2_relat_1(sK0))
      | r2_hidden(sK6(sK0,X59),k2_relat_1(sK1))
      | ~ r2_hidden(X59,k2_relat_1(sK0)) ) ),
    inference(forward_demodulation,[],[f72163,f48])).

fof(f48,plain,(
    k2_relat_1(sK0) = k2_relat_1(k5_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f72163,plain,(
    ! [X59] :
      ( r2_hidden(sK6(sK0,X59),k2_relat_1(sK1))
      | ~ r2_hidden(X59,k2_relat_1(k5_relat_1(sK1,sK0)))
      | ~ r2_hidden(X59,k2_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f72162,f47])).

fof(f47,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f72162,plain,(
    ! [X59] :
      ( r2_hidden(sK6(sK0,X59),k2_relat_1(sK1))
      | ~ r2_hidden(X59,k2_relat_1(k5_relat_1(sK1,sK0)))
      | ~ v1_funct_1(sK1)
      | ~ r2_hidden(X59,k2_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f72097,f46])).

fof(f46,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f72097,plain,(
    ! [X59] :
      ( r2_hidden(sK6(sK0,X59),k2_relat_1(sK1))
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X59,k2_relat_1(k5_relat_1(sK1,sK0)))
      | ~ v1_funct_1(sK1)
      | ~ r2_hidden(X59,k2_relat_1(sK0)) ) ),
    inference(superposition,[],[f4957,f9443])).

fof(f9443,plain,(
    ! [X71] :
      ( k1_funct_1(sK1,sK6(k5_relat_1(sK1,sK0),X71)) = sK6(sK0,X71)
      | ~ r2_hidden(X71,k2_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f9442,f6204])).

fof(f6204,plain,(
    ! [X12] :
      ( r2_hidden(k1_funct_1(sK1,sK6(k5_relat_1(sK1,sK0),X12)),k1_relat_1(sK0))
      | ~ r2_hidden(X12,k2_relat_1(sK0)) ) ),
    inference(forward_demodulation,[],[f6203,f48])).

fof(f6203,plain,(
    ! [X12] :
      ( ~ r2_hidden(X12,k2_relat_1(k5_relat_1(sK1,sK0)))
      | r2_hidden(k1_funct_1(sK1,sK6(k5_relat_1(sK1,sK0),X12)),k1_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f6202,f44])).

fof(f6202,plain,(
    ! [X12] :
      ( ~ r2_hidden(X12,k2_relat_1(k5_relat_1(sK1,sK0)))
      | r2_hidden(k1_funct_1(sK1,sK6(k5_relat_1(sK1,sK0),X12)),k1_relat_1(sK0))
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f6201,f45])).

fof(f6201,plain,(
    ! [X12] :
      ( ~ r2_hidden(X12,k2_relat_1(k5_relat_1(sK1,sK0)))
      | r2_hidden(k1_funct_1(sK1,sK6(k5_relat_1(sK1,sK0),X12)),k1_relat_1(sK0))
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f6200,f47])).

fof(f6200,plain,(
    ! [X12] :
      ( ~ v1_funct_1(sK1)
      | ~ r2_hidden(X12,k2_relat_1(k5_relat_1(sK1,sK0)))
      | r2_hidden(k1_funct_1(sK1,sK6(k5_relat_1(sK1,sK0),X12)),k1_relat_1(sK0))
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f6179,f46])).

fof(f6179,plain,(
    ! [X12] :
      ( ~ v1_relat_1(sK1)
      | ~ v1_funct_1(sK1)
      | ~ r2_hidden(X12,k2_relat_1(k5_relat_1(sK1,sK0)))
      | r2_hidden(k1_funct_1(sK1,sK6(k5_relat_1(sK1,sK0),X12)),k1_relat_1(sK0))
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f448,f208])).

fof(f208,plain,(
    ! [X21,X20] :
      ( ~ r2_hidden(X20,k1_relat_1(k5_relat_1(sK1,X21)))
      | r2_hidden(k1_funct_1(sK1,X20),k1_relat_1(X21))
      | ~ v1_funct_1(X21)
      | ~ v1_relat_1(X21) ) ),
    inference(subsumption_resolution,[],[f187,f46])).

fof(f187,plain,(
    ! [X21,X20] :
      ( r2_hidden(k1_funct_1(sK1,X20),k1_relat_1(X21))
      | ~ r2_hidden(X20,k1_relat_1(k5_relat_1(sK1,X21)))
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(X21)
      | ~ v1_relat_1(X21) ) ),
    inference(resolution,[],[f47,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
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
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

fof(f448,plain,(
    ! [X50,X51] :
      ( r2_hidden(sK6(k5_relat_1(X50,sK0),X51),k1_relat_1(k5_relat_1(X50,sK0)))
      | ~ v1_relat_1(X50)
      | ~ v1_funct_1(X50)
      | ~ r2_hidden(X51,k2_relat_1(k5_relat_1(X50,sK0))) ) ),
    inference(subsumption_resolution,[],[f427,f97])).

fof(f97,plain,(
    ! [X27] :
      ( v1_relat_1(k5_relat_1(X27,sK0))
      | ~ v1_relat_1(X27) ) ),
    inference(resolution,[],[f44,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f427,plain,(
    ! [X50,X51] :
      ( ~ v1_funct_1(X50)
      | ~ v1_relat_1(X50)
      | r2_hidden(sK6(k5_relat_1(X50,sK0),X51),k1_relat_1(k5_relat_1(X50,sK0)))
      | ~ r2_hidden(X51,k2_relat_1(k5_relat_1(X50,sK0)))
      | ~ v1_relat_1(k5_relat_1(X50,sK0)) ) ),
    inference(resolution,[],[f133,f75])).

fof(f133,plain,(
    ! [X9] :
      ( v1_funct_1(k5_relat_1(X9,sK0))
      | ~ v1_funct_1(X9)
      | ~ v1_relat_1(X9) ) ),
    inference(subsumption_resolution,[],[f112,f44])).

fof(f112,plain,(
    ! [X9] :
      ( v1_funct_1(k5_relat_1(X9,sK0))
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(X9)
      | ~ v1_relat_1(X9) ) ),
    inference(resolution,[],[f45,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f9442,plain,(
    ! [X71] :
      ( ~ r2_hidden(X71,k2_relat_1(sK0))
      | k1_funct_1(sK1,sK6(k5_relat_1(sK1,sK0),X71)) = sK6(sK0,X71)
      | ~ r2_hidden(k1_funct_1(sK1,sK6(k5_relat_1(sK1,sK0),X71)),k1_relat_1(sK0)) ) ),
    inference(forward_demodulation,[],[f9441,f48])).

fof(f9441,plain,(
    ! [X71] :
      ( k1_funct_1(sK1,sK6(k5_relat_1(sK1,sK0),X71)) = sK6(sK0,X71)
      | ~ r2_hidden(k1_funct_1(sK1,sK6(k5_relat_1(sK1,sK0),X71)),k1_relat_1(sK0))
      | ~ r2_hidden(X71,k2_relat_1(k5_relat_1(sK1,sK0))) ) ),
    inference(subsumption_resolution,[],[f9440,f44])).

fof(f9440,plain,(
    ! [X71] :
      ( k1_funct_1(sK1,sK6(k5_relat_1(sK1,sK0),X71)) = sK6(sK0,X71)
      | ~ r2_hidden(k1_funct_1(sK1,sK6(k5_relat_1(sK1,sK0),X71)),k1_relat_1(sK0))
      | ~ v1_relat_1(sK0)
      | ~ r2_hidden(X71,k2_relat_1(k5_relat_1(sK1,sK0))) ) ),
    inference(subsumption_resolution,[],[f9323,f45])).

fof(f9323,plain,(
    ! [X71] :
      ( k1_funct_1(sK1,sK6(k5_relat_1(sK1,sK0),X71)) = sK6(sK0,X71)
      | ~ r2_hidden(k1_funct_1(sK1,sK6(k5_relat_1(sK1,sK0),X71)),k1_relat_1(sK0))
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0)
      | ~ r2_hidden(X71,k2_relat_1(k5_relat_1(sK1,sK0))) ) ),
    inference(superposition,[],[f4917,f1808])).

fof(f1808,plain,(
    ! [X10,X9] :
      ( k1_funct_1(X9,k1_funct_1(sK1,sK6(k5_relat_1(sK1,X9),X10))) = X10
      | ~ v1_funct_1(X9)
      | ~ v1_relat_1(X9)
      | ~ r2_hidden(X10,k2_relat_1(k5_relat_1(sK1,X9))) ) ),
    inference(subsumption_resolution,[],[f1807,f165])).

fof(f165,plain,(
    ! [X26] :
      ( v1_relat_1(k5_relat_1(sK1,X26))
      | ~ v1_relat_1(X26) ) ),
    inference(resolution,[],[f46,f68])).

fof(f1807,plain,(
    ! [X10,X9] :
      ( k1_funct_1(X9,k1_funct_1(sK1,sK6(k5_relat_1(sK1,X9),X10))) = X10
      | ~ v1_funct_1(X9)
      | ~ v1_relat_1(X9)
      | ~ r2_hidden(X10,k2_relat_1(k5_relat_1(sK1,X9)))
      | ~ v1_relat_1(k5_relat_1(sK1,X9)) ) ),
    inference(subsumption_resolution,[],[f1806,f201])).

fof(f201,plain,(
    ! [X8] :
      ( v1_funct_1(k5_relat_1(sK1,X8))
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(X8) ) ),
    inference(subsumption_resolution,[],[f180,f46])).

fof(f180,plain,(
    ! [X8] :
      ( v1_funct_1(k5_relat_1(sK1,X8))
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f47,f63])).

fof(f1806,plain,(
    ! [X10,X9] :
      ( k1_funct_1(X9,k1_funct_1(sK1,sK6(k5_relat_1(sK1,X9),X10))) = X10
      | ~ v1_funct_1(X9)
      | ~ v1_relat_1(X9)
      | ~ r2_hidden(X10,k2_relat_1(k5_relat_1(sK1,X9)))
      | ~ v1_funct_1(k5_relat_1(sK1,X9))
      | ~ v1_relat_1(k5_relat_1(sK1,X9)) ) ),
    inference(subsumption_resolution,[],[f1781,f75])).

fof(f1781,plain,(
    ! [X10,X9] :
      ( k1_funct_1(X9,k1_funct_1(sK1,sK6(k5_relat_1(sK1,X9),X10))) = X10
      | ~ r2_hidden(sK6(k5_relat_1(sK1,X9),X10),k1_relat_1(k5_relat_1(sK1,X9)))
      | ~ v1_funct_1(X9)
      | ~ v1_relat_1(X9)
      | ~ r2_hidden(X10,k2_relat_1(k5_relat_1(sK1,X9)))
      | ~ v1_funct_1(k5_relat_1(sK1,X9))
      | ~ v1_relat_1(k5_relat_1(sK1,X9)) ) ),
    inference(superposition,[],[f204,f74])).

fof(f204,plain,(
    ! [X12,X13] :
      ( k1_funct_1(k5_relat_1(sK1,X12),X13) = k1_funct_1(X12,k1_funct_1(sK1,X13))
      | ~ r2_hidden(X13,k1_relat_1(k5_relat_1(sK1,X12)))
      | ~ v1_funct_1(X12)
      | ~ v1_relat_1(X12) ) ),
    inference(subsumption_resolution,[],[f183,f46])).

fof(f183,plain,(
    ! [X12,X13] :
      ( k1_funct_1(k5_relat_1(sK1,X12),X13) = k1_funct_1(X12,k1_funct_1(sK1,X13))
      | ~ r2_hidden(X13,k1_relat_1(k5_relat_1(sK1,X12)))
      | ~ v1_relat_1(sK1)
      | ~ v1_funct_1(X12)
      | ~ v1_relat_1(X12) ) ),
    inference(resolution,[],[f47,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
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
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(f4917,plain,(
    ! [X0] :
      ( sK6(sK0,k1_funct_1(sK0,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f4905,f142])).

fof(f142,plain,(
    ! [X26] :
      ( r2_hidden(k1_funct_1(sK0,X26),k2_relat_1(sK0))
      | ~ r2_hidden(X26,k1_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f121,f44])).

fof(f121,plain,(
    ! [X26] :
      ( r2_hidden(k1_funct_1(sK0,X26),k2_relat_1(sK0))
      | ~ r2_hidden(X26,k1_relat_1(sK0))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f45,f73])).

fof(f4905,plain,(
    ! [X0] :
      ( sK6(sK0,k1_funct_1(sK0,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(sK0))
      | ~ r2_hidden(k1_funct_1(sK0,X0),k2_relat_1(sK0)) ) ),
    inference(equality_resolution,[],[f702])).

fof(f702,plain,(
    ! [X10,X9] :
      ( k1_funct_1(sK0,X10) != X9
      | sK6(sK0,X9) = X10
      | ~ r2_hidden(X10,k1_relat_1(sK0))
      | ~ r2_hidden(X9,k2_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f701,f144])).

fof(f144,plain,(
    ! [X28] :
      ( r2_hidden(sK6(sK0,X28),k1_relat_1(sK0))
      | ~ r2_hidden(X28,k2_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f123,f44])).

fof(f123,plain,(
    ! [X28] :
      ( r2_hidden(sK6(sK0,X28),k1_relat_1(sK0))
      | ~ r2_hidden(X28,k2_relat_1(sK0))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f45,f75])).

fof(f701,plain,(
    ! [X10,X9] :
      ( k1_funct_1(sK0,X10) != X9
      | sK6(sK0,X9) = X10
      | ~ r2_hidden(sK6(sK0,X9),k1_relat_1(sK0))
      | ~ r2_hidden(X10,k1_relat_1(sK0))
      | ~ r2_hidden(X9,k2_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f700,f44])).

fof(f700,plain,(
    ! [X10,X9] :
      ( k1_funct_1(sK0,X10) != X9
      | sK6(sK0,X9) = X10
      | ~ r2_hidden(sK6(sK0,X9),k1_relat_1(sK0))
      | ~ r2_hidden(X10,k1_relat_1(sK0))
      | ~ v1_relat_1(sK0)
      | ~ r2_hidden(X9,k2_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f699,f45])).

fof(f699,plain,(
    ! [X10,X9] :
      ( k1_funct_1(sK0,X10) != X9
      | sK6(sK0,X9) = X10
      | ~ r2_hidden(sK6(sK0,X9),k1_relat_1(sK0))
      | ~ r2_hidden(X10,k1_relat_1(sK0))
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0)
      | ~ r2_hidden(X9,k2_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f689,f49])).

fof(f689,plain,(
    ! [X10,X9] :
      ( k1_funct_1(sK0,X10) != X9
      | sK6(sK0,X9) = X10
      | ~ r2_hidden(sK6(sK0,X9),k1_relat_1(sK0))
      | ~ r2_hidden(X10,k1_relat_1(sK0))
      | ~ v2_funct_1(sK0)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0)
      | ~ r2_hidden(X9,k2_relat_1(sK0)) ) ),
    inference(superposition,[],[f51,f143])).

fof(f143,plain,(
    ! [X27] :
      ( k1_funct_1(sK0,sK6(sK0,X27)) = X27
      | ~ r2_hidden(X27,k2_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f122,f44])).

fof(f122,plain,(
    ! [X27] :
      ( k1_funct_1(sK0,sK6(sK0,X27)) = X27
      | ~ r2_hidden(X27,k2_relat_1(sK0))
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f45,f74])).

fof(f4957,plain,(
    ! [X4,X3] :
      ( r2_hidden(k1_funct_1(X3,sK6(k5_relat_1(X3,sK0),X4)),k2_relat_1(X3))
      | ~ v1_relat_1(X3)
      | ~ r2_hidden(X4,k2_relat_1(k5_relat_1(X3,sK0)))
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f4938])).

fof(f4938,plain,(
    ! [X4,X3] :
      ( ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ r2_hidden(X4,k2_relat_1(k5_relat_1(X3,sK0)))
      | r2_hidden(k1_funct_1(X3,sK6(k5_relat_1(X3,sK0),X4)),k2_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f864,f73])).

fof(f864,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK6(k5_relat_1(X6,sK0),X7),k1_relat_1(X6))
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6)
      | ~ r2_hidden(X7,k2_relat_1(k5_relat_1(X6,sK0))) ) ),
    inference(subsumption_resolution,[],[f863,f97])).

fof(f863,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK6(k5_relat_1(X6,sK0),X7),k1_relat_1(X6))
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6)
      | ~ r2_hidden(X7,k2_relat_1(k5_relat_1(X6,sK0)))
      | ~ v1_relat_1(k5_relat_1(X6,sK0)) ) ),
    inference(subsumption_resolution,[],[f849,f133])).

fof(f849,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK6(k5_relat_1(X6,sK0),X7),k1_relat_1(X6))
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6)
      | ~ r2_hidden(X7,k2_relat_1(k5_relat_1(X6,sK0)))
      | ~ v1_funct_1(k5_relat_1(X6,sK0))
      | ~ v1_relat_1(k5_relat_1(X6,sK0)) ) ),
    inference(resolution,[],[f136,f75])).

fof(f136,plain,(
    ! [X14,X15] :
      ( ~ r2_hidden(X14,k1_relat_1(k5_relat_1(X15,sK0)))
      | r2_hidden(X14,k1_relat_1(X15))
      | ~ v1_funct_1(X15)
      | ~ v1_relat_1(X15) ) ),
    inference(subsumption_resolution,[],[f115,f44])).

fof(f115,plain,(
    ! [X14,X15] :
      ( r2_hidden(X14,k1_relat_1(X15))
      | ~ r2_hidden(X14,k1_relat_1(k5_relat_1(X15,sK0)))
      | ~ v1_funct_1(X15)
      | ~ v1_relat_1(X15)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f45,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

%------------------------------------------------------------------------------
