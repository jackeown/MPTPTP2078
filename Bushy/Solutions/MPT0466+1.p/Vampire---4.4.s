%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t54_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:03 EDT 2019

% Result     : Theorem 77.74s
% Output     : Refutation 77.74s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 407 expanded)
%              Number of leaves         :   25 ( 141 expanded)
%              Depth                    :   16
%              Number of atoms          :  535 (1842 expanded)
%              Number of equality atoms :   34 ( 269 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2704,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f263,f271,f278,f292,f383,f390,f453,f470,f2701])).

fof(f2701,plain,
    ( ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_20 ),
    inference(avatar_contradiction_clause,[],[f2700])).

fof(f2700,plain,
    ( $false
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_20 ),
    inference(subsumption_resolution,[],[f2691,f1031])).

fof(f1031,plain,
    ( r2_hidden(k4_tarski(sK9(sK0,sK1,sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k4_relat_1(sK0))
    | ~ spl12_20 ),
    inference(subsumption_resolution,[],[f1026,f54])).

fof(f54,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( k5_relat_1(k4_relat_1(sK1),k4_relat_1(sK0)) != k4_relat_1(k5_relat_1(sK0,sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) != k4_relat_1(k5_relat_1(X0,X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k5_relat_1(k4_relat_1(X1),k4_relat_1(sK0)) != k4_relat_1(k5_relat_1(sK0,X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) != k4_relat_1(k5_relat_1(X0,X1))
          & v1_relat_1(X1) )
     => ( k5_relat_1(k4_relat_1(sK1),k4_relat_1(X0)) != k4_relat_1(k5_relat_1(X0,sK1))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) != k4_relat_1(k5_relat_1(X0,X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t54_relat_1.p',t54_relat_1)).

fof(f1026,plain,
    ( r2_hidden(k4_tarski(sK9(sK0,sK1,sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k4_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl12_20 ),
    inference(resolution,[],[f465,f198])).

fof(f198,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X4),X0)
      | r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f84,f59])).

fof(f59,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t54_relat_1.p',dt_k4_relat_1)).

fof(f84,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t54_relat_1.p',d7_relat_1)).

fof(f465,plain,
    ( r2_hidden(k4_tarski(sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK9(sK0,sK1,sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))))),sK0)
    | ~ spl12_20 ),
    inference(subsumption_resolution,[],[f464,f54])).

fof(f464,plain,
    ( r2_hidden(k4_tarski(sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK9(sK0,sK1,sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))))),sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl12_20 ),
    inference(subsumption_resolution,[],[f457,f55])).

fof(f55,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f457,plain,
    ( r2_hidden(k4_tarski(sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK9(sK0,sK1,sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))))),sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl12_20 ),
    inference(resolution,[],[f382,f130])).

fof(f130,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f88,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t54_relat_1.p',dt_k5_relat_1)).

fof(f88,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK7(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK8(X0,X1,X2),sK7(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK8(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK9(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f47,f50,f49,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK7(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK7(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK6(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK8(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK8(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK9(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t54_relat_1.p',d8_relat_1)).

fof(f382,plain,
    ( r2_hidden(k4_tarski(sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k5_relat_1(sK0,sK1))
    | ~ spl12_20 ),
    inference(avatar_component_clause,[],[f381])).

fof(f381,plain,
    ( spl12_20
  <=> r2_hidden(k4_tarski(sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f2691,plain,
    ( ~ r2_hidden(k4_tarski(sK9(sK0,sK1,sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k4_relat_1(sK0))
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14
    | ~ spl12_20 ),
    inference(resolution,[],[f1042,f484])).

fof(f484,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),X0),k4_relat_1(sK1))
        | ~ r2_hidden(k4_tarski(X0,sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k4_relat_1(sK0)) )
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f483,f235])).

fof(f235,plain,
    ( v1_relat_1(k4_relat_1(sK1))
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl12_8
  <=> v1_relat_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f483,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k4_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),X0),k4_relat_1(sK1))
        | ~ v1_relat_1(k4_relat_1(sK1)) )
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f482,f241])).

fof(f241,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl12_10
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f482,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k4_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),X0),k4_relat_1(sK1))
        | ~ v1_relat_1(k4_relat_1(sK0))
        | ~ v1_relat_1(k4_relat_1(sK1)) )
    | ~ spl12_12
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f481,f247])).

fof(f247,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl12_12
  <=> v1_relat_1(k4_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f481,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k4_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),X0),k4_relat_1(sK1))
        | ~ v1_relat_1(k4_relat_1(k5_relat_1(sK0,sK1)))
        | ~ v1_relat_1(k4_relat_1(sK0))
        | ~ v1_relat_1(k4_relat_1(sK1)) )
    | ~ spl12_14 ),
    inference(subsumption_resolution,[],[f475,f90])).

fof(f90,plain,(
    ~ sQ11_eqProxy(k5_relat_1(k4_relat_1(sK1),k4_relat_1(sK0)),k4_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(equality_proxy_replacement,[],[f56,f89])).

fof(f89,plain,(
    ! [X1,X0] :
      ( sQ11_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ11_eqProxy])])).

fof(f56,plain,(
    k5_relat_1(k4_relat_1(sK1),k4_relat_1(sK0)) != k4_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f475,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k4_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),X0),k4_relat_1(sK1))
        | sQ11_eqProxy(k5_relat_1(k4_relat_1(sK1),k4_relat_1(sK0)),k4_relat_1(k5_relat_1(sK0,sK1)))
        | ~ v1_relat_1(k4_relat_1(k5_relat_1(sK0,sK1)))
        | ~ v1_relat_1(k4_relat_1(sK0))
        | ~ v1_relat_1(k4_relat_1(sK1)) )
    | ~ spl12_14 ),
    inference(resolution,[],[f256,f97])).

fof(f97,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)
      | ~ r2_hidden(k4_tarski(X5,sK7(X0,X1,X2)),X1)
      | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0)
      | sQ11_eqProxy(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f74,f89])).

fof(f74,plain,(
    ! [X2,X0,X5,X1] :
      ( k5_relat_1(X0,X1) = X2
      | ~ r2_hidden(k4_tarski(X5,sK7(X0,X1,X2)),X1)
      | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0)
      | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f256,plain,
    ( r2_hidden(k4_tarski(sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k4_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl12_14 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl12_14
  <=> r2_hidden(k4_tarski(sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k4_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f1042,plain,
    ( r2_hidden(k4_tarski(sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK9(sK0,sK1,sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))))),k4_relat_1(sK1))
    | ~ spl12_20 ),
    inference(subsumption_resolution,[],[f1036,f55])).

fof(f1036,plain,
    ( r2_hidden(k4_tarski(sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK9(sK0,sK1,sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))))),k4_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl12_20 ),
    inference(resolution,[],[f467,f198])).

fof(f467,plain,
    ( r2_hidden(k4_tarski(sK9(sK0,sK1,sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),sK1)
    | ~ spl12_20 ),
    inference(subsumption_resolution,[],[f466,f54])).

fof(f466,plain,
    ( r2_hidden(k4_tarski(sK9(sK0,sK1,sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl12_20 ),
    inference(subsumption_resolution,[],[f458,f55])).

fof(f458,plain,
    ( r2_hidden(k4_tarski(sK9(sK0,sK1,sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl12_20 ),
    inference(resolution,[],[f382,f125])).

fof(f125,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK9(X0,X1,X7,X8),X8),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f87,f79])).

fof(f87,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK9(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK9(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f470,plain,
    ( spl12_15
    | ~ spl12_18
    | ~ spl12_20 ),
    inference(avatar_contradiction_clause,[],[f469])).

fof(f469,plain,
    ( $false
    | ~ spl12_15
    | ~ spl12_18
    | ~ spl12_20 ),
    inference(subsumption_resolution,[],[f468,f373])).

fof(f373,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl12_18 ),
    inference(avatar_component_clause,[],[f372])).

fof(f372,plain,
    ( spl12_18
  <=> v1_relat_1(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).

fof(f468,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl12_15
    | ~ spl12_20 ),
    inference(subsumption_resolution,[],[f459,f253])).

fof(f253,plain,
    ( ~ r2_hidden(k4_tarski(sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k4_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl12_15 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl12_15
  <=> ~ r2_hidden(k4_tarski(sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k4_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).

fof(f459,plain,
    ( r2_hidden(k4_tarski(sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k4_relat_1(k5_relat_1(sK0,sK1)))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl12_20 ),
    inference(resolution,[],[f382,f198])).

fof(f453,plain,
    ( ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | spl12_15
    | ~ spl12_16
    | spl12_21 ),
    inference(avatar_contradiction_clause,[],[f452])).

fof(f452,plain,
    ( $false
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_15
    | ~ spl12_16
    | ~ spl12_21 ),
    inference(unit_resulting_resolution,[],[f54,f55,f399,f417,f379,f157])).

fof(f157,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( ~ r2_hidden(k4_tarski(X9,X8),X1)
      | r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f86,f79])).

fof(f86,plain,(
    ! [X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X8,X7,X1,X9] :
      ( r2_hidden(k4_tarski(X7,X8),X2)
      | ~ r2_hidden(k4_tarski(X9,X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X9),X0)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f379,plain,
    ( ~ r2_hidden(k4_tarski(sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k5_relat_1(sK0,sK1))
    | ~ spl12_21 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl12_21
  <=> ~ r2_hidden(k4_tarski(sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_21])])).

fof(f417,plain,
    ( r2_hidden(k4_tarski(sK8(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),sK1)
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f412,f55])).

fof(f412,plain,
    ( r2_hidden(k4_tarski(sK8(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_15 ),
    inference(resolution,[],[f409,f219])).

fof(f219,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f85,f59])).

fof(f85,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f409,plain,
    ( r2_hidden(k4_tarski(sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK8(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k4_relat_1(sK1))
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f393,f253])).

fof(f393,plain,
    ( r2_hidden(k4_tarski(sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK8(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k4_relat_1(sK1))
    | r2_hidden(k4_tarski(sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k4_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_12 ),
    inference(subsumption_resolution,[],[f392,f235])).

fof(f392,plain,
    ( r2_hidden(k4_tarski(sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK8(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k4_relat_1(sK1))
    | r2_hidden(k4_tarski(sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k4_relat_1(k5_relat_1(sK0,sK1)))
    | ~ v1_relat_1(k4_relat_1(sK1))
    | ~ spl12_10
    | ~ spl12_12 ),
    inference(subsumption_resolution,[],[f391,f241])).

fof(f391,plain,
    ( r2_hidden(k4_tarski(sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK8(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k4_relat_1(sK1))
    | r2_hidden(k4_tarski(sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k4_relat_1(k5_relat_1(sK0,sK1)))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK1))
    | ~ spl12_12 ),
    inference(subsumption_resolution,[],[f181,f247])).

fof(f181,plain,
    ( r2_hidden(k4_tarski(sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK8(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k4_relat_1(sK1))
    | r2_hidden(k4_tarski(sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k4_relat_1(k5_relat_1(sK0,sK1)))
    | ~ v1_relat_1(k4_relat_1(k5_relat_1(sK0,sK1)))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK1)) ),
    inference(resolution,[],[f99,f90])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( sQ11_eqProxy(k5_relat_1(X0,X1),X2)
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK8(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f72,f89])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK8(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f399,plain,
    ( r2_hidden(k4_tarski(sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK8(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),sK0)
    | ~ spl12_16 ),
    inference(subsumption_resolution,[],[f394,f54])).

fof(f394,plain,
    ( r2_hidden(k4_tarski(sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK8(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl12_16 ),
    inference(resolution,[],[f262,f219])).

fof(f262,plain,
    ( r2_hidden(k4_tarski(sK8(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k4_relat_1(sK0))
    | ~ spl12_16 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl12_16
  <=> r2_hidden(k4_tarski(sK8(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).

fof(f390,plain,(
    spl12_19 ),
    inference(avatar_contradiction_clause,[],[f389])).

fof(f389,plain,
    ( $false
    | ~ spl12_19 ),
    inference(subsumption_resolution,[],[f388,f54])).

fof(f388,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl12_19 ),
    inference(subsumption_resolution,[],[f385,f55])).

fof(f385,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl12_19 ),
    inference(resolution,[],[f376,f79])).

fof(f376,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl12_19 ),
    inference(avatar_component_clause,[],[f375])).

fof(f375,plain,
    ( spl12_19
  <=> ~ v1_relat_1(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).

fof(f383,plain,
    ( ~ spl12_19
    | spl12_20
    | ~ spl12_14 ),
    inference(avatar_split_clause,[],[f298,f255,f381,f375])).

fof(f298,plain,
    ( r2_hidden(k4_tarski(sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl12_14 ),
    inference(resolution,[],[f256,f219])).

fof(f292,plain,(
    spl12_13 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | ~ spl12_13 ),
    inference(subsumption_resolution,[],[f290,f54])).

fof(f290,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl12_13 ),
    inference(subsumption_resolution,[],[f287,f55])).

fof(f287,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl12_13 ),
    inference(resolution,[],[f282,f79])).

fof(f282,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl12_13 ),
    inference(resolution,[],[f250,f59])).

fof(f250,plain,
    ( ~ v1_relat_1(k4_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl12_13 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl12_13
  <=> ~ v1_relat_1(k4_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).

fof(f278,plain,(
    spl12_11 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | ~ spl12_11 ),
    inference(subsumption_resolution,[],[f274,f54])).

fof(f274,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl12_11 ),
    inference(resolution,[],[f244,f59])).

fof(f244,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | ~ spl12_11 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl12_11
  <=> ~ v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f271,plain,(
    spl12_9 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | ~ spl12_9 ),
    inference(subsumption_resolution,[],[f267,f55])).

fof(f267,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl12_9 ),
    inference(resolution,[],[f238,f59])).

fof(f238,plain,
    ( ~ v1_relat_1(k4_relat_1(sK1))
    | ~ spl12_9 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl12_9
  <=> ~ v1_relat_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f263,plain,
    ( ~ spl12_9
    | ~ spl12_11
    | ~ spl12_13
    | spl12_14
    | spl12_16 ),
    inference(avatar_split_clause,[],[f169,f261,f255,f249,f243,f237])).

fof(f169,plain,
    ( r2_hidden(k4_tarski(sK8(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k4_relat_1(sK0))
    | r2_hidden(k4_tarski(sK6(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1))),sK7(k4_relat_1(sK1),k4_relat_1(sK0),k4_relat_1(k5_relat_1(sK0,sK1)))),k4_relat_1(k5_relat_1(sK0,sK1)))
    | ~ v1_relat_1(k4_relat_1(k5_relat_1(sK0,sK1)))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK1)) ),
    inference(resolution,[],[f98,f90])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( sQ11_eqProxy(k5_relat_1(X0,X1),X2)
      | r2_hidden(k4_tarski(sK8(X0,X1,X2),sK7(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f73,f89])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK8(X0,X1,X2),sK7(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
