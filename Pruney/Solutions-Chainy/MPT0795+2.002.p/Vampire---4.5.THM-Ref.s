%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 409 expanded)
%              Number of leaves         :    9 ( 110 expanded)
%              Depth                    :   28
%              Number of atoms          :  470 (2312 expanded)
%              Number of equality atoms :   71 ( 316 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f162,plain,(
    $false ),
    inference(subsumption_resolution,[],[f160,f161])).

fof(f161,plain,(
    r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,
    ( r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(backward_demodulation,[],[f150,f154])).

fof(f154,plain,(
    sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))) = k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))) ),
    inference(resolution,[],[f107,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_1)).

fof(f107,plain,(
    r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f106,f77])).

fof(f77,plain,(
    ! [X92,X93] :
      ( ~ r2_hidden(k4_tarski(X93,X92),sK0)
      | r2_hidden(X92,k3_relat_1(sK0)) ) ),
    inference(resolution,[],[f22,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r3_wellord1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ~ r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0)))
        & v1_relat_1(X0) )
   => ( ~ r3_wellord1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ~ r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0)))
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_wellord1)).

fof(f106,plain,
    ( r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f105,f22])).

fof(f105,plain,
    ( r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f104,f25])).

fof(f25,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f104,plain,
    ( r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f103,f26])).

fof(f26,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f103,plain,
    ( r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f102,f27])).

fof(f27,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f102,plain,
    ( r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f101,f28])).

fof(f28,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f101,plain,
    ( r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f92,f24])).

fof(f24,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(f92,plain,
    ( r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,
    ( r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f23,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r3_wellord1(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),k3_relat_1(X0))
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)
      | ~ v2_funct_1(X2)
      | k2_relat_1(X2) != k3_relat_1(X1)
      | k1_relat_1(X2) != k3_relat_1(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_wellord1(X0,X1,X2)
                  | ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,sK1(X0,X1,X2)),k1_funct_1(X2,sK2(X0,X1,X2))),X1)
                      | ~ r2_hidden(sK2(X0,X1,X2),k3_relat_1(X0))
                      | ~ r2_hidden(sK1(X0,X1,X2),k3_relat_1(X0))
                      | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) )
                    & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,sK1(X0,X1,X2)),k1_funct_1(X2,sK2(X0,X1,X2))),X1)
                        & r2_hidden(sK2(X0,X1,X2),k3_relat_1(X0))
                        & r2_hidden(sK1(X0,X1,X2),k3_relat_1(X0)) )
                      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f19,f20])).

fof(f20,plain,(
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
     => ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,sK1(X0,X1,X2)),k1_funct_1(X2,sK2(X0,X1,X2))),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),k3_relat_1(X0))
          | ~ r2_hidden(sK1(X0,X1,X2),k3_relat_1(X0))
          | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) )
        & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,sK1(X0,X1,X2)),k1_funct_1(X2,sK2(X0,X1,X2))),X1)
            & r2_hidden(sK2(X0,X1,X2),k3_relat_1(X0))
            & r2_hidden(sK1(X0,X1,X2),k3_relat_1(X0)) )
          | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f23,plain,(
    ~ r3_wellord1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f150,plain,
    ( r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(backward_demodulation,[],[f113,f145])).

fof(f145,plain,(
    sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))) = k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))) ),
    inference(resolution,[],[f100,f40])).

fof(f100,plain,(
    r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f99,f76])).

fof(f76,plain,(
    ! [X90,X91] :
      ( ~ r2_hidden(k4_tarski(X90,X91),sK0)
      | r2_hidden(X90,k3_relat_1(sK0)) ) ),
    inference(resolution,[],[f22,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f99,plain,
    ( r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f98,f22])).

fof(f98,plain,
    ( r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f97,f25])).

fof(f97,plain,
    ( r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f96,f26])).

fof(f96,plain,
    ( r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f95,f27])).

fof(f95,plain,
    ( r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f94,f28])).

fof(f94,plain,
    ( r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f93,f24])).

fof(f93,plain,
    ( r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,
    ( r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f23,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r3_wellord1(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),k3_relat_1(X0))
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)
      | ~ v2_funct_1(X2)
      | k2_relat_1(X2) != k3_relat_1(X1)
      | k1_relat_1(X2) != k3_relat_1(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f113,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f112,f22])).

fof(f112,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f111,f25])).

fof(f111,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f110,f26])).

fof(f110,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f109,f27])).

fof(f109,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f108,f28])).

fof(f108,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f91,f24])).

fof(f91,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f23,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r3_wellord1(X0,X1,X2)
      | r2_hidden(k4_tarski(k1_funct_1(X2,sK1(X0,X1,X2)),k1_funct_1(X2,sK2(X0,X1,X2))),X1)
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)
      | ~ v2_funct_1(X2)
      | k2_relat_1(X2) != k3_relat_1(X1)
      | k1_relat_1(X2) != k3_relat_1(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f160,plain,(
    ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(backward_demodulation,[],[f149,f154])).

fof(f149,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(backward_demodulation,[],[f121,f145])).

fof(f121,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f120,f22])).

fof(f120,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f119,f25])).

fof(f119,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f118,f26])).

fof(f118,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f117,f27])).

fof(f117,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f116,f28])).

fof(f116,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f115,f24])).

fof(f115,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f114,f100])).

fof(f114,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | ~ r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f90,f107])).

fof(f90,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | ~ r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0)
    | ~ r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))
    | ~ r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)
    | ~ v2_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_funct_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(k6_relat_1(k3_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f23,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r3_wellord1(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(k1_funct_1(X2,sK1(X0,X1,X2)),k1_funct_1(X2,sK2(X0,X1,X2))),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),k3_relat_1(X0))
      | ~ r2_hidden(sK1(X0,X1,X2),k3_relat_1(X0))
      | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)
      | ~ v2_funct_1(X2)
      | k2_relat_1(X2) != k3_relat_1(X1)
      | k1_relat_1(X2) != k3_relat_1(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (9802)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.46  % (9810)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.47  % (9802)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f160,f161])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f158])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)),
% 0.21/0.48    inference(backward_demodulation,[],[f150,f154])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))) = k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),
% 0.21/0.48    inference(resolution,[],[f107,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => k1_funct_1(k6_relat_1(X1),X0) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_1)).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f106,f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ( ! [X92,X93] : (~r2_hidden(k4_tarski(X93,X92),sK0) | r2_hidden(X92,k3_relat_1(sK0))) )),
% 0.21/0.48    inference(resolution,[],[f22,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    v1_relat_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ~r3_wellord1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))) & v1_relat_1(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0] : (~r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))) & v1_relat_1(X0)) => (~r3_wellord1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))) & v1_relat_1(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0] : (~r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))) & v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (v1_relat_1(X0) => r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))))),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => r3_wellord1(X0,X0,k6_relat_1(k3_relat_1(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_wellord1)).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f105,f22])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f104,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f103,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v1_funct_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f102,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_funct_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f101,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0))) | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_funct_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f92,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v2_funct_1(k6_relat_1(k3_relat_1(sK0))) | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0))) | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_funct_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v2_funct_1(k6_relat_1(k3_relat_1(sK0))) | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0))) | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_funct_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(resolution,[],[f23,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r3_wellord1(X0,X1,X2) | r2_hidden(sK2(X0,X1,X2),k3_relat_1(X0)) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) | ~v2_funct_1(X2) | k2_relat_1(X2) != k3_relat_1(X1) | k1_relat_1(X2) != k3_relat_1(X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r3_wellord1(X0,X1,X2) | ((~r2_hidden(k4_tarski(k1_funct_1(X2,sK1(X0,X1,X2)),k1_funct_1(X2,sK2(X0,X1,X2))),X1) | ~r2_hidden(sK2(X0,X1,X2),k3_relat_1(X0)) | ~r2_hidden(sK1(X0,X1,X2),k3_relat_1(X0)) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)) & ((r2_hidden(k4_tarski(k1_funct_1(X2,sK1(X0,X1,X2)),k1_funct_1(X2,sK2(X0,X1,X2))),X1) & r2_hidden(sK2(X0,X1,X2),k3_relat_1(X0)) & r2_hidden(sK1(X0,X1,X2),k3_relat_1(X0))) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0))) | ~v2_funct_1(X2) | k2_relat_1(X2) != k3_relat_1(X1) | k1_relat_1(X2) != k3_relat_1(X0)) & ((! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1) | ~r2_hidden(X6,k3_relat_1(X0)) | ~r2_hidden(X5,k3_relat_1(X0))) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1) & r2_hidden(X6,k3_relat_1(X0)) & r2_hidden(X5,k3_relat_1(X0))) | ~r2_hidden(k4_tarski(X5,X6),X0))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k1_relat_1(X2) = k3_relat_1(X0)) | ~r3_wellord1(X0,X1,X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f19,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~r2_hidden(k4_tarski(X3,X4),X0)) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0))) | r2_hidden(k4_tarski(X3,X4),X0))) => ((~r2_hidden(k4_tarski(k1_funct_1(X2,sK1(X0,X1,X2)),k1_funct_1(X2,sK2(X0,X1,X2))),X1) | ~r2_hidden(sK2(X0,X1,X2),k3_relat_1(X0)) | ~r2_hidden(sK1(X0,X1,X2),k3_relat_1(X0)) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)) & ((r2_hidden(k4_tarski(k1_funct_1(X2,sK1(X0,X1,X2)),k1_funct_1(X2,sK2(X0,X1,X2))),X1) & r2_hidden(sK2(X0,X1,X2),k3_relat_1(X0)) & r2_hidden(sK1(X0,X1,X2),k3_relat_1(X0))) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r3_wellord1(X0,X1,X2) | ? [X3,X4] : ((~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~r2_hidden(k4_tarski(X3,X4),X0)) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0))) | r2_hidden(k4_tarski(X3,X4),X0))) | ~v2_funct_1(X2) | k2_relat_1(X2) != k3_relat_1(X1) | k1_relat_1(X2) != k3_relat_1(X0)) & ((! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1) | ~r2_hidden(X6,k3_relat_1(X0)) | ~r2_hidden(X5,k3_relat_1(X0))) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1) & r2_hidden(X6,k3_relat_1(X0)) & r2_hidden(X5,k3_relat_1(X0))) | ~r2_hidden(k4_tarski(X5,X6),X0))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k1_relat_1(X2) = k3_relat_1(X0)) | ~r3_wellord1(X0,X1,X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(rectify,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r3_wellord1(X0,X1,X2) | ? [X3,X4] : ((~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~r2_hidden(k4_tarski(X3,X4),X0)) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0))) | r2_hidden(k4_tarski(X3,X4),X0))) | ~v2_funct_1(X2) | k2_relat_1(X2) != k3_relat_1(X1) | k1_relat_1(X2) != k3_relat_1(X0)) & ((! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(k4_tarski(X3,X4),X0))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k1_relat_1(X2) = k3_relat_1(X0)) | ~r3_wellord1(X0,X1,X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r3_wellord1(X0,X1,X2) | (? [X3,X4] : (((~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(k4_tarski(X3,X4),X0)) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0))) | r2_hidden(k4_tarski(X3,X4),X0))) | ~v2_funct_1(X2) | k2_relat_1(X2) != k3_relat_1(X1) | k1_relat_1(X2) != k3_relat_1(X0))) & ((! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X0) | (~r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)))) & ((r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(k4_tarski(X3,X4),X0))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k1_relat_1(X2) = k3_relat_1(X0)) | ~r3_wellord1(X0,X1,X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r3_wellord1(X0,X1,X2) <=> (! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) <=> (r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0)))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k1_relat_1(X2) = k3_relat_1(X0))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r3_wellord1(X0,X1,X2) <=> (! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) <=> (r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0)))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k1_relat_1(X2) = k3_relat_1(X0))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r3_wellord1(X0,X1,X2) <=> (! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X0) <=> (r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) & r2_hidden(X4,k3_relat_1(X0)) & r2_hidden(X3,k3_relat_1(X0)))) & v2_funct_1(X2) & k2_relat_1(X2) = k3_relat_1(X1) & k1_relat_1(X2) = k3_relat_1(X0))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_wellord1)).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ~r3_wellord1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)),
% 0.21/0.48    inference(backward_demodulation,[],[f113,f145])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))) = k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),
% 0.21/0.48    inference(resolution,[],[f100,f40])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f99,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ( ! [X90,X91] : (~r2_hidden(k4_tarski(X90,X91),sK0) | r2_hidden(X90,k3_relat_1(sK0))) )),
% 0.21/0.48    inference(resolution,[],[f22,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f98,f22])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f97,f25])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f96,f26])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v1_funct_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f95,f27])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_funct_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f94,f28])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0))) | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_funct_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f93,f24])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v2_funct_1(k6_relat_1(k3_relat_1(sK0))) | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0))) | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_funct_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f86])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v2_funct_1(k6_relat_1(k3_relat_1(sK0))) | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0))) | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_funct_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(resolution,[],[f23,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r3_wellord1(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),k3_relat_1(X0)) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) | ~v2_funct_1(X2) | k2_relat_1(X2) != k3_relat_1(X1) | k1_relat_1(X2) != k3_relat_1(X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f112,f22])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f111,f25])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f110,f26])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v1_funct_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f109,f27])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_funct_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f108,f28])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0))) | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_funct_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f91,f24])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v2_funct_1(k6_relat_1(k3_relat_1(sK0))) | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0))) | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_funct_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0) | r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v2_funct_1(k6_relat_1(k3_relat_1(sK0))) | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0))) | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_funct_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(resolution,[],[f23,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r3_wellord1(X0,X1,X2) | r2_hidden(k4_tarski(k1_funct_1(X2,sK1(X0,X1,X2)),k1_funct_1(X2,sK2(X0,X1,X2))),X1) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) | ~v2_funct_1(X2) | k2_relat_1(X2) != k3_relat_1(X1) | k1_relat_1(X2) != k3_relat_1(X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    ~r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f159])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    ~r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)),
% 0.21/0.48    inference(backward_demodulation,[],[f149,f154])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    ~r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0) | ~r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)),
% 0.21/0.48    inference(backward_demodulation,[],[f121,f145])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    ~r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0) | ~r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f120,f22])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    ~r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0) | ~r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f119,f25])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    ~r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0) | ~r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f118,f26])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ~r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0) | ~r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v1_funct_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f117,f27])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    ~r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0) | ~r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_funct_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f116,f28])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ~r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0) | ~r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0))) | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_funct_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f115,f24])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    ~r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0) | ~r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v2_funct_1(k6_relat_1(k3_relat_1(sK0))) | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0))) | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_funct_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f114,f100])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ~r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0) | ~r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) | ~r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v2_funct_1(k6_relat_1(k3_relat_1(sK0))) | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0))) | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_funct_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f90,f107])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ~r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0) | ~r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) | ~r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) | ~r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v2_funct_1(k6_relat_1(k3_relat_1(sK0))) | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0))) | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_funct_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f89])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ~r2_hidden(k4_tarski(k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),k1_funct_1(k6_relat_1(k3_relat_1(sK0)),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))))),sK0) | ~r2_hidden(sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) | ~r2_hidden(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),k3_relat_1(sK0)) | ~r2_hidden(k4_tarski(sK1(sK0,sK0,k6_relat_1(k3_relat_1(sK0))),sK2(sK0,sK0,k6_relat_1(k3_relat_1(sK0)))),sK0) | ~v2_funct_1(k6_relat_1(k3_relat_1(sK0))) | k3_relat_1(sK0) != k2_relat_1(k6_relat_1(k3_relat_1(sK0))) | k3_relat_1(sK0) != k1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_funct_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(k6_relat_1(k3_relat_1(sK0))) | ~v1_relat_1(sK0) | ~v1_relat_1(sK0)),
% 0.21/0.48    inference(resolution,[],[f23,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r3_wellord1(X0,X1,X2) | ~r2_hidden(k4_tarski(k1_funct_1(X2,sK1(X0,X1,X2)),k1_funct_1(X2,sK2(X0,X1,X2))),X1) | ~r2_hidden(sK2(X0,X1,X2),k3_relat_1(X0)) | ~r2_hidden(sK1(X0,X1,X2),k3_relat_1(X0)) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) | ~v2_funct_1(X2) | k2_relat_1(X2) != k3_relat_1(X1) | k1_relat_1(X2) != k3_relat_1(X0) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (9802)------------------------------
% 0.21/0.48  % (9802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9802)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (9802)Memory used [KB]: 1791
% 0.21/0.48  % (9802)Time elapsed: 0.065 s
% 0.21/0.48  % (9802)------------------------------
% 0.21/0.48  % (9802)------------------------------
% 0.21/0.48  % (9790)Success in time 0.125 s
%------------------------------------------------------------------------------
