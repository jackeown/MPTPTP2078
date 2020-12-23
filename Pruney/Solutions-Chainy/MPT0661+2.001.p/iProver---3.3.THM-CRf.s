%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:57 EST 2020

% Result     : Theorem 27.77s
% Output     : CNFRefutation 27.77s
% Verified   : 
% Statistics : Number of formulae       :  205 (2484 expanded)
%              Number of clauses        :  121 ( 609 expanded)
%              Number of leaves         :   24 ( 685 expanded)
%              Depth                    :   26
%              Number of atoms          :  557 (8269 expanded)
%              Number of equality atoms :  341 (4173 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f90,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f92,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f58,f90,f90])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
              & k3_xboole_0(k1_relat_1(X2),X0) = k1_relat_1(X1) )
           => k7_relat_1(X2,X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( ! [X3] :
                    ( r2_hidden(X3,k1_relat_1(X1))
                   => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
                & k3_xboole_0(k1_relat_1(X2),X0) = k1_relat_1(X1) )
             => k7_relat_1(X2,X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f46,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_relat_1(X2,X0) != X1
          & ! [X3] :
              ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & k3_xboole_0(k1_relat_1(X2),X0) = k1_relat_1(X1)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f47,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_relat_1(X2,X0) != X1
          & ! [X3] :
              ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & k3_xboole_0(k1_relat_1(X2),X0) = k1_relat_1(X1)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k7_relat_1(X2,X0) != X1
          & ! [X3] :
              ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & k3_xboole_0(k1_relat_1(X2),X0) = k1_relat_1(X1)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k7_relat_1(sK3,X0) != X1
        & ! [X3] :
            ( k1_funct_1(sK3,X3) = k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,k1_relat_1(X1)) )
        & k3_xboole_0(k1_relat_1(sK3),X0) = k1_relat_1(X1)
        & v1_funct_1(sK3)
        & v1_relat_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k7_relat_1(X2,X0) != X1
            & ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relat_1(X1)) )
            & k3_xboole_0(k1_relat_1(X2),X0) = k1_relat_1(X1)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k7_relat_1(X2,sK1) != sK2
          & ! [X3] :
              ( k1_funct_1(sK2,X3) = k1_funct_1(X2,X3)
              | ~ r2_hidden(X3,k1_relat_1(sK2)) )
          & k3_xboole_0(k1_relat_1(X2),sK1) = k1_relat_1(sK2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( k7_relat_1(sK3,sK1) != sK2
    & ! [X3] :
        ( k1_funct_1(sK2,X3) = k1_funct_1(sK3,X3)
        | ~ r2_hidden(X3,k1_relat_1(sK2)) )
    & k3_xboole_0(k1_relat_1(sK3),sK1) = k1_relat_1(sK2)
    & v1_funct_1(sK3)
    & v1_relat_1(sK3)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f47,f53,f52])).

fof(f85,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f91,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f61,f90])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f72,f91])).

fof(f87,plain,(
    k3_xboole_0(k1_relat_1(sK3),sK1) = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f96,plain,(
    k1_setfam_1(k2_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),sK1)) = k1_relat_1(sK2) ),
    inference(definition_unfolding,[],[f87,f91])).

fof(f83,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
        & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
            & r2_hidden(sK0(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f50])).

fof(f81,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f75,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f63,f91])).

fof(f84,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,(
    k7_relat_1(sK3,sK1) != sK2 ),
    inference(cnf_transformation,[],[f54])).

fof(f86,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      | ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      | ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      | ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      | ~ r2_hidden(X0,k1_setfam_1(k2_enumset1(k1_relat_1(X2),k1_relat_1(X2),k1_relat_1(X2),X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f80,f91])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
           => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0))
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0))
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0))
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f69,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f82,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f88,plain,(
    ! [X3] :
      ( k1_funct_1(sK2,X3) = k1_funct_1(sK3,X3)
      | ~ r2_hidden(X3,k1_relat_1(sK2)) ) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_29,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1079,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1091,plain,
    ( k1_setfam_1(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3642,plain,
    ( k1_setfam_1(k2_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_1079,c_1091])).

cnf(c_4415,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_relat_1(sK3))) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_3,c_3642])).

cnf(c_27,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),sK1)) = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1564,plain,
    ( k1_setfam_1(k2_enumset1(sK1,sK1,sK1,k1_relat_1(sK3))) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3,c_27])).

cnf(c_4658,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK1)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_4415,c_1564])).

cnf(c_31,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1077,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1099,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k7_relat_1(X0,X1),X1) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1097,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),X1) = k7_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2207,plain,
    ( k7_relat_1(k7_relat_1(sK3,X0),X0) = k7_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1079,c_1097])).

cnf(c_12,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1093,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2439,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2207,c_1093])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1090,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3194,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_relat_1(k7_relat_1(sK3,k1_relat_1(X0))))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(X0)))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_relat_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2439,c_1090])).

cnf(c_3311,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_relat_1(k7_relat_1(sK3,k1_relat_1(X0))))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(X0)))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1099,c_3194])).

cnf(c_34,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3427,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_relat_1(k7_relat_1(X0,k1_relat_1(k7_relat_1(sK3,k1_relat_1(X0))))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3311,c_34])).

cnf(c_3428,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_relat_1(k7_relat_1(sK3,k1_relat_1(X0))))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(X0)))
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3427])).

cnf(c_3434,plain,
    ( k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2))))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2))) ),
    inference(superposition,[status(thm)],[c_1077,c_3428])).

cnf(c_24,plain,
    ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X1 = X0
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1082,plain,
    ( X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0)
    | r2_hidden(sK0(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3512,plain,
    ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2)))) = X0
    | k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2))) != k1_relat_1(X0)
    | r2_hidden(sK0(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2)))),X0),k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2)))))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2))))) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3434,c_1082])).

cnf(c_3524,plain,
    ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2)))) = X0
    | k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2))) != k1_relat_1(X0)
    | r2_hidden(sK0(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2)))),X0),k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2))))) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2))))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3512,c_3434])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1088,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1712,plain,
    ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_1077,c_1088])).

cnf(c_19,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1086,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3641,plain,
    ( k1_setfam_1(k2_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_1086,c_1091])).

cnf(c_10,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3644,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_3641,c_10])).

cnf(c_3734,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(sK1),k1_relat_1(sK3))) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3644,c_1564])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1098,plain,
    ( k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3732,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_3,c_3644])).

cnf(c_3930,plain,
    ( k7_relat_1(X0,k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k7_relat_1(X0,X2),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1098,c_3732])).

cnf(c_3936,plain,
    ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k7_relat_1(sK3,X1),X0) ),
    inference(superposition,[status(thm)],[c_1079,c_3930])).

cnf(c_4213,plain,
    ( k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),sK1) = k7_relat_1(sK3,k1_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3734,c_3936])).

cnf(c_1711,plain,
    ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_1079,c_1088])).

cnf(c_4227,plain,
    ( k7_relat_1(sK3,k1_relat_1(sK2)) = k7_relat_1(sK3,sK1) ),
    inference(light_normalisation,[status(thm)],[c_4213,c_1711])).

cnf(c_35508,plain,
    ( k1_relat_1(X0) != k1_relat_1(sK2)
    | sK2 = X0
    | r2_hidden(sK0(sK2,X0),k1_relat_1(sK2)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3524,c_1712,c_4227,c_4658])).

cnf(c_32,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_33,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_35512,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_relat_1(X0) != k1_relat_1(sK2)
    | sK2 = X0
    | r2_hidden(sK0(sK2,X0),k1_relat_1(sK2)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_35508,c_32,c_33])).

cnf(c_35513,plain,
    ( k1_relat_1(X0) != k1_relat_1(sK2)
    | sK2 = X0
    | r2_hidden(sK0(sK2,X0),k1_relat_1(sK2)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_35512])).

cnf(c_35519,plain,
    ( k7_relat_1(sK3,sK1) = sK2
    | r2_hidden(sK0(sK2,k7_relat_1(sK3,sK1)),k1_relat_1(sK2)) = iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK1)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4658,c_35513])).

cnf(c_25,negated_conjecture,
    ( k7_relat_1(sK3,sK1) != sK2 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_4902,plain,
    ( k7_relat_1(sK3,sK1) = X0
    | k1_relat_1(X0) != k1_relat_1(sK2)
    | r2_hidden(sK0(X0,k7_relat_1(sK3,sK1)),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4658,c_1082])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_35,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_20,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1153,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK1))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1154,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK1)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1153])).

cnf(c_1208,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1209,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK1)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1208])).

cnf(c_34936,plain,
    ( v1_relat_1(X0) != iProver_top
    | k7_relat_1(sK3,sK1) = X0
    | k1_relat_1(X0) != k1_relat_1(sK2)
    | r2_hidden(sK0(X0,k7_relat_1(sK3,sK1)),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4902,c_34,c_35,c_1154,c_1209])).

cnf(c_34937,plain,
    ( k7_relat_1(sK3,sK1) = X0
    | k1_relat_1(X0) != k1_relat_1(sK2)
    | r2_hidden(sK0(X0,k7_relat_1(sK3,sK1)),k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_34936])).

cnf(c_34960,plain,
    ( k7_relat_1(sK3,sK1) = sK2
    | r2_hidden(sK0(sK2,k7_relat_1(sK3,sK1)),k1_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_34937])).

cnf(c_35707,plain,
    ( r2_hidden(sK0(sK2,k7_relat_1(sK3,sK1)),k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_35519,c_32,c_33,c_25,c_34960])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1096,plain,
    ( k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5670,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(X1,k1_relat_1(k6_relat_1(X0))))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1086,c_1096])).

cnf(c_5673,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(X1,X0))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5670,c_10])).

cnf(c_5994,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) ),
    inference(superposition,[status(thm)],[c_1086,c_5673])).

cnf(c_3935,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
    inference(superposition,[status(thm)],[c_1086,c_3930])).

cnf(c_5997,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_5994,c_10,c_3935])).

cnf(c_6006,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(sK3)),k1_relat_1(sK2)) = k7_relat_1(k6_relat_1(k1_relat_1(sK3)),sK1) ),
    inference(superposition,[status(thm)],[c_3734,c_5997])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k5_relat_1(k6_relat_1(X2),X1),X0) = k1_funct_1(X1,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1084,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,X2)
    | r2_hidden(X2,k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3720,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,X2)
    | r2_hidden(X2,k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(X1)),X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3644,c_1084])).

cnf(c_41902,plain,
    ( k1_funct_1(k5_relat_1(k6_relat_1(k1_relat_1(sK2)),sK3),X0) = k1_funct_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(sK3)),sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6006,c_3720])).

cnf(c_3740,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(sK3)),sK1)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3732,c_1564])).

cnf(c_3432,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK3,k1_relat_1(k6_relat_1(X0)))))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(k6_relat_1(X0)))) ),
    inference(superposition,[status(thm)],[c_1086,c_3428])).

cnf(c_3436,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK3,X0)))) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(light_normalisation,[status(thm)],[c_3432,c_10])).

cnf(c_13,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1092,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2199,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_1092])).

cnf(c_54,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2639,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2199,c_54])).

cnf(c_3902,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3436,c_2639])).

cnf(c_9,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_8,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k7_relat_1(X1,X2)) = k5_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1095,plain,
    ( k5_relat_1(X0,k7_relat_1(X1,X2)) = k5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(k7_relat_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4607,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(X1,X2)) = k5_relat_1(k6_relat_1(X0),X1)
    | r1_tarski(X0,k1_relat_1(k7_relat_1(X1,X2))) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_1095])).

cnf(c_6924,plain,
    ( v1_relat_1(X1) != iProver_top
    | r1_tarski(X0,k1_relat_1(k7_relat_1(X1,X2))) != iProver_top
    | k5_relat_1(k6_relat_1(X0),k7_relat_1(X1,X2)) = k5_relat_1(k6_relat_1(X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4607,c_54])).

cnf(c_6925,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(X1,X2)) = k5_relat_1(k6_relat_1(X0),X1)
    | r1_tarski(X0,k1_relat_1(k7_relat_1(X1,X2))) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6924])).

cnf(c_6942,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(sK3,k1_relat_1(sK2))) = k5_relat_1(k6_relat_1(X0),sK3)
    | r1_tarski(X0,k1_relat_1(k7_relat_1(sK3,sK1))) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4227,c_6925])).

cnf(c_6973,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(sK3,sK1)) = k5_relat_1(k6_relat_1(X0),sK3)
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6942,c_4227,c_4658])).

cnf(c_18754,plain,
    ( r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | k5_relat_1(k6_relat_1(X0),k7_relat_1(sK3,sK1)) = k5_relat_1(k6_relat_1(X0),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6973,c_34])).

cnf(c_18755,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(sK3,sK1)) = k5_relat_1(k6_relat_1(X0),sK3)
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_18754])).

cnf(c_18764,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2)))),k7_relat_1(sK3,sK1)) = k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2)))),sK3) ),
    inference(superposition,[status(thm)],[c_3902,c_18755])).

cnf(c_4219,plain,
    ( v1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),X1)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3936,c_1099])).

cnf(c_7674,plain,
    ( v1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4219,c_34])).

cnf(c_7680,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2207,c_7674])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1094,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7725,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK3,X0))),k7_relat_1(sK3,X0)) = k7_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_7680,c_1094])).

cnf(c_11371,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(sK2)),k7_relat_1(sK3,sK1)) = k7_relat_1(sK3,sK1) ),
    inference(superposition,[status(thm)],[c_4658,c_7725])).

cnf(c_18769,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(sK2)),sK3) = k7_relat_1(sK3,sK1) ),
    inference(light_normalisation,[status(thm)],[c_18764,c_4227,c_4658,c_11371])).

cnf(c_41984,plain,
    ( k1_funct_1(k7_relat_1(sK3,sK1),X0) = k1_funct_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_41902,c_3740,c_18769])).

cnf(c_43153,plain,
    ( k1_funct_1(k7_relat_1(sK3,sK1),X0) = k1_funct_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_41984,c_34,c_35])).

cnf(c_43159,plain,
    ( k1_funct_1(k7_relat_1(sK3,sK1),sK0(sK2,k7_relat_1(sK3,sK1))) = k1_funct_1(sK3,sK0(sK2,k7_relat_1(sK3,sK1))) ),
    inference(superposition,[status(thm)],[c_35707,c_43153])).

cnf(c_23,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X1 = X0
    | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1))
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1083,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
    | k1_relat_1(X1) != k1_relat_1(X0)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_105969,plain,
    ( k1_funct_1(sK3,sK0(sK2,k7_relat_1(sK3,sK1))) != k1_funct_1(sK2,sK0(sK2,k7_relat_1(sK3,sK1)))
    | k7_relat_1(sK3,sK1) = sK2
    | k1_relat_1(k7_relat_1(sK3,sK1)) != k1_relat_1(sK2)
    | v1_funct_1(k7_relat_1(sK3,sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK1)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_43159,c_1083])).

cnf(c_26,negated_conjecture,
    ( ~ r2_hidden(X0,k1_relat_1(sK2))
    | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1081,plain,
    ( k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_35716,plain,
    ( k1_funct_1(sK3,sK0(sK2,k7_relat_1(sK3,sK1))) = k1_funct_1(sK2,sK0(sK2,k7_relat_1(sK3,sK1))) ),
    inference(superposition,[status(thm)],[c_35707,c_1081])).

cnf(c_105970,plain,
    ( k1_funct_1(sK3,sK0(sK2,k7_relat_1(sK3,sK1))) != k1_funct_1(sK3,sK0(sK2,k7_relat_1(sK3,sK1)))
    | k7_relat_1(sK3,sK1) = sK2
    | k1_relat_1(sK2) != k1_relat_1(sK2)
    | v1_funct_1(k7_relat_1(sK3,sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK1)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_105969,c_4658,c_35716])).

cnf(c_105971,plain,
    ( k7_relat_1(sK3,sK1) = sK2
    | v1_funct_1(k7_relat_1(sK3,sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK1)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_105970])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_105971,c_1209,c_1154,c_25,c_35,c_34,c_33,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:24:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 27.77/4.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.77/4.02  
% 27.77/4.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.77/4.02  
% 27.77/4.02  ------  iProver source info
% 27.77/4.02  
% 27.77/4.02  git: date: 2020-06-30 10:37:57 +0100
% 27.77/4.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.77/4.02  git: non_committed_changes: false
% 27.77/4.02  git: last_make_outside_of_git: false
% 27.77/4.02  
% 27.77/4.02  ------ 
% 27.77/4.02  
% 27.77/4.02  ------ Input Options
% 27.77/4.02  
% 27.77/4.02  --out_options                           all
% 27.77/4.02  --tptp_safe_out                         true
% 27.77/4.02  --problem_path                          ""
% 27.77/4.02  --include_path                          ""
% 27.77/4.02  --clausifier                            res/vclausify_rel
% 27.77/4.02  --clausifier_options                    ""
% 27.77/4.02  --stdin                                 false
% 27.77/4.02  --stats_out                             all
% 27.77/4.02  
% 27.77/4.02  ------ General Options
% 27.77/4.02  
% 27.77/4.02  --fof                                   false
% 27.77/4.02  --time_out_real                         305.
% 27.77/4.02  --time_out_virtual                      -1.
% 27.77/4.02  --symbol_type_check                     false
% 27.77/4.02  --clausify_out                          false
% 27.77/4.02  --sig_cnt_out                           false
% 27.77/4.02  --trig_cnt_out                          false
% 27.77/4.02  --trig_cnt_out_tolerance                1.
% 27.77/4.02  --trig_cnt_out_sk_spl                   false
% 27.77/4.02  --abstr_cl_out                          false
% 27.77/4.02  
% 27.77/4.02  ------ Global Options
% 27.77/4.02  
% 27.77/4.02  --schedule                              default
% 27.77/4.02  --add_important_lit                     false
% 27.77/4.02  --prop_solver_per_cl                    1000
% 27.77/4.02  --min_unsat_core                        false
% 27.77/4.02  --soft_assumptions                      false
% 27.77/4.02  --soft_lemma_size                       3
% 27.77/4.02  --prop_impl_unit_size                   0
% 27.77/4.02  --prop_impl_unit                        []
% 27.77/4.02  --share_sel_clauses                     true
% 27.77/4.02  --reset_solvers                         false
% 27.77/4.02  --bc_imp_inh                            [conj_cone]
% 27.77/4.02  --conj_cone_tolerance                   3.
% 27.77/4.02  --extra_neg_conj                        none
% 27.77/4.02  --large_theory_mode                     true
% 27.77/4.02  --prolific_symb_bound                   200
% 27.77/4.02  --lt_threshold                          2000
% 27.77/4.02  --clause_weak_htbl                      true
% 27.77/4.02  --gc_record_bc_elim                     false
% 27.77/4.02  
% 27.77/4.02  ------ Preprocessing Options
% 27.77/4.02  
% 27.77/4.02  --preprocessing_flag                    true
% 27.77/4.02  --time_out_prep_mult                    0.1
% 27.77/4.02  --splitting_mode                        input
% 27.77/4.02  --splitting_grd                         true
% 27.77/4.02  --splitting_cvd                         false
% 27.77/4.02  --splitting_cvd_svl                     false
% 27.77/4.02  --splitting_nvd                         32
% 27.77/4.02  --sub_typing                            true
% 27.77/4.02  --prep_gs_sim                           true
% 27.77/4.02  --prep_unflatten                        true
% 27.77/4.02  --prep_res_sim                          true
% 27.77/4.02  --prep_upred                            true
% 27.77/4.02  --prep_sem_filter                       exhaustive
% 27.77/4.02  --prep_sem_filter_out                   false
% 27.77/4.02  --pred_elim                             true
% 27.77/4.02  --res_sim_input                         true
% 27.77/4.02  --eq_ax_congr_red                       true
% 27.77/4.02  --pure_diseq_elim                       true
% 27.77/4.02  --brand_transform                       false
% 27.77/4.02  --non_eq_to_eq                          false
% 27.77/4.02  --prep_def_merge                        true
% 27.77/4.02  --prep_def_merge_prop_impl              false
% 27.77/4.02  --prep_def_merge_mbd                    true
% 27.77/4.02  --prep_def_merge_tr_red                 false
% 27.77/4.02  --prep_def_merge_tr_cl                  false
% 27.77/4.02  --smt_preprocessing                     true
% 27.77/4.02  --smt_ac_axioms                         fast
% 27.77/4.02  --preprocessed_out                      false
% 27.77/4.02  --preprocessed_stats                    false
% 27.77/4.02  
% 27.77/4.02  ------ Abstraction refinement Options
% 27.77/4.02  
% 27.77/4.02  --abstr_ref                             []
% 27.77/4.02  --abstr_ref_prep                        false
% 27.77/4.02  --abstr_ref_until_sat                   false
% 27.77/4.02  --abstr_ref_sig_restrict                funpre
% 27.77/4.02  --abstr_ref_af_restrict_to_split_sk     false
% 27.77/4.02  --abstr_ref_under                       []
% 27.77/4.02  
% 27.77/4.02  ------ SAT Options
% 27.77/4.02  
% 27.77/4.02  --sat_mode                              false
% 27.77/4.02  --sat_fm_restart_options                ""
% 27.77/4.02  --sat_gr_def                            false
% 27.77/4.02  --sat_epr_types                         true
% 27.77/4.02  --sat_non_cyclic_types                  false
% 27.77/4.02  --sat_finite_models                     false
% 27.77/4.02  --sat_fm_lemmas                         false
% 27.77/4.02  --sat_fm_prep                           false
% 27.77/4.02  --sat_fm_uc_incr                        true
% 27.77/4.02  --sat_out_model                         small
% 27.77/4.02  --sat_out_clauses                       false
% 27.77/4.02  
% 27.77/4.02  ------ QBF Options
% 27.77/4.02  
% 27.77/4.02  --qbf_mode                              false
% 27.77/4.02  --qbf_elim_univ                         false
% 27.77/4.02  --qbf_dom_inst                          none
% 27.77/4.02  --qbf_dom_pre_inst                      false
% 27.77/4.02  --qbf_sk_in                             false
% 27.77/4.02  --qbf_pred_elim                         true
% 27.77/4.02  --qbf_split                             512
% 27.77/4.02  
% 27.77/4.02  ------ BMC1 Options
% 27.77/4.02  
% 27.77/4.02  --bmc1_incremental                      false
% 27.77/4.02  --bmc1_axioms                           reachable_all
% 27.77/4.02  --bmc1_min_bound                        0
% 27.77/4.02  --bmc1_max_bound                        -1
% 27.77/4.02  --bmc1_max_bound_default                -1
% 27.77/4.02  --bmc1_symbol_reachability              true
% 27.77/4.02  --bmc1_property_lemmas                  false
% 27.77/4.02  --bmc1_k_induction                      false
% 27.77/4.02  --bmc1_non_equiv_states                 false
% 27.77/4.02  --bmc1_deadlock                         false
% 27.77/4.02  --bmc1_ucm                              false
% 27.77/4.02  --bmc1_add_unsat_core                   none
% 27.77/4.02  --bmc1_unsat_core_children              false
% 27.77/4.02  --bmc1_unsat_core_extrapolate_axioms    false
% 27.77/4.02  --bmc1_out_stat                         full
% 27.77/4.02  --bmc1_ground_init                      false
% 27.77/4.02  --bmc1_pre_inst_next_state              false
% 27.77/4.02  --bmc1_pre_inst_state                   false
% 27.77/4.02  --bmc1_pre_inst_reach_state             false
% 27.77/4.02  --bmc1_out_unsat_core                   false
% 27.77/4.02  --bmc1_aig_witness_out                  false
% 27.77/4.02  --bmc1_verbose                          false
% 27.77/4.02  --bmc1_dump_clauses_tptp                false
% 27.77/4.02  --bmc1_dump_unsat_core_tptp             false
% 27.77/4.02  --bmc1_dump_file                        -
% 27.77/4.02  --bmc1_ucm_expand_uc_limit              128
% 27.77/4.02  --bmc1_ucm_n_expand_iterations          6
% 27.77/4.02  --bmc1_ucm_extend_mode                  1
% 27.77/4.02  --bmc1_ucm_init_mode                    2
% 27.77/4.02  --bmc1_ucm_cone_mode                    none
% 27.77/4.02  --bmc1_ucm_reduced_relation_type        0
% 27.77/4.02  --bmc1_ucm_relax_model                  4
% 27.77/4.02  --bmc1_ucm_full_tr_after_sat            true
% 27.77/4.02  --bmc1_ucm_expand_neg_assumptions       false
% 27.77/4.02  --bmc1_ucm_layered_model                none
% 27.77/4.02  --bmc1_ucm_max_lemma_size               10
% 27.77/4.02  
% 27.77/4.02  ------ AIG Options
% 27.77/4.02  
% 27.77/4.02  --aig_mode                              false
% 27.77/4.02  
% 27.77/4.02  ------ Instantiation Options
% 27.77/4.02  
% 27.77/4.02  --instantiation_flag                    true
% 27.77/4.02  --inst_sos_flag                         true
% 27.77/4.02  --inst_sos_phase                        true
% 27.77/4.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.77/4.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.77/4.02  --inst_lit_sel_side                     num_symb
% 27.77/4.02  --inst_solver_per_active                1400
% 27.77/4.02  --inst_solver_calls_frac                1.
% 27.77/4.02  --inst_passive_queue_type               priority_queues
% 27.77/4.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.77/4.02  --inst_passive_queues_freq              [25;2]
% 27.77/4.02  --inst_dismatching                      true
% 27.77/4.02  --inst_eager_unprocessed_to_passive     true
% 27.77/4.02  --inst_prop_sim_given                   true
% 27.77/4.02  --inst_prop_sim_new                     false
% 27.77/4.02  --inst_subs_new                         false
% 27.77/4.02  --inst_eq_res_simp                      false
% 27.77/4.02  --inst_subs_given                       false
% 27.77/4.02  --inst_orphan_elimination               true
% 27.77/4.02  --inst_learning_loop_flag               true
% 27.77/4.02  --inst_learning_start                   3000
% 27.77/4.02  --inst_learning_factor                  2
% 27.77/4.02  --inst_start_prop_sim_after_learn       3
% 27.77/4.02  --inst_sel_renew                        solver
% 27.77/4.02  --inst_lit_activity_flag                true
% 27.77/4.02  --inst_restr_to_given                   false
% 27.77/4.02  --inst_activity_threshold               500
% 27.77/4.02  --inst_out_proof                        true
% 27.77/4.02  
% 27.77/4.02  ------ Resolution Options
% 27.77/4.02  
% 27.77/4.02  --resolution_flag                       true
% 27.77/4.02  --res_lit_sel                           adaptive
% 27.77/4.02  --res_lit_sel_side                      none
% 27.77/4.02  --res_ordering                          kbo
% 27.77/4.02  --res_to_prop_solver                    active
% 27.77/4.02  --res_prop_simpl_new                    false
% 27.77/4.02  --res_prop_simpl_given                  true
% 27.77/4.02  --res_passive_queue_type                priority_queues
% 27.77/4.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.77/4.02  --res_passive_queues_freq               [15;5]
% 27.77/4.02  --res_forward_subs                      full
% 27.77/4.02  --res_backward_subs                     full
% 27.77/4.02  --res_forward_subs_resolution           true
% 27.77/4.02  --res_backward_subs_resolution          true
% 27.77/4.02  --res_orphan_elimination                true
% 27.77/4.02  --res_time_limit                        2.
% 27.77/4.02  --res_out_proof                         true
% 27.77/4.02  
% 27.77/4.02  ------ Superposition Options
% 27.77/4.02  
% 27.77/4.02  --superposition_flag                    true
% 27.77/4.02  --sup_passive_queue_type                priority_queues
% 27.77/4.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.77/4.02  --sup_passive_queues_freq               [8;1;4]
% 27.77/4.02  --demod_completeness_check              fast
% 27.77/4.02  --demod_use_ground                      true
% 27.77/4.02  --sup_to_prop_solver                    passive
% 27.77/4.02  --sup_prop_simpl_new                    true
% 27.77/4.02  --sup_prop_simpl_given                  true
% 27.77/4.02  --sup_fun_splitting                     true
% 27.77/4.02  --sup_smt_interval                      50000
% 27.77/4.02  
% 27.77/4.02  ------ Superposition Simplification Setup
% 27.77/4.02  
% 27.77/4.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.77/4.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.77/4.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.77/4.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.77/4.02  --sup_full_triv                         [TrivRules;PropSubs]
% 27.77/4.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.77/4.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.77/4.02  --sup_immed_triv                        [TrivRules]
% 27.77/4.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.77/4.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.77/4.02  --sup_immed_bw_main                     []
% 27.77/4.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.77/4.02  --sup_input_triv                        [Unflattening;TrivRules]
% 27.77/4.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.77/4.02  --sup_input_bw                          []
% 27.77/4.02  
% 27.77/4.02  ------ Combination Options
% 27.77/4.02  
% 27.77/4.02  --comb_res_mult                         3
% 27.77/4.02  --comb_sup_mult                         2
% 27.77/4.02  --comb_inst_mult                        10
% 27.77/4.02  
% 27.77/4.02  ------ Debug Options
% 27.77/4.02  
% 27.77/4.02  --dbg_backtrace                         false
% 27.77/4.02  --dbg_dump_prop_clauses                 false
% 27.77/4.02  --dbg_dump_prop_clauses_file            -
% 27.77/4.02  --dbg_out_stat                          false
% 27.77/4.02  ------ Parsing...
% 27.77/4.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.77/4.02  
% 27.77/4.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 27.77/4.02  
% 27.77/4.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.77/4.02  
% 27.77/4.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.77/4.02  ------ Proving...
% 27.77/4.02  ------ Problem Properties 
% 27.77/4.02  
% 27.77/4.02  
% 27.77/4.02  clauses                                 30
% 27.77/4.02  conjectures                             7
% 27.77/4.02  EPR                                     6
% 27.77/4.02  Horn                                    29
% 27.77/4.02  unary                                   12
% 27.77/4.02  binary                                  9
% 27.77/4.02  lits                                    67
% 27.77/4.02  lits eq                                 22
% 27.77/4.02  fd_pure                                 0
% 27.77/4.02  fd_pseudo                               0
% 27.77/4.02  fd_cond                                 0
% 27.77/4.02  fd_pseudo_cond                          3
% 27.77/4.02  AC symbols                              0
% 27.77/4.02  
% 27.77/4.02  ------ Schedule dynamic 5 is on 
% 27.77/4.02  
% 27.77/4.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.77/4.02  
% 27.77/4.02  
% 27.77/4.02  ------ 
% 27.77/4.02  Current options:
% 27.77/4.02  ------ 
% 27.77/4.02  
% 27.77/4.02  ------ Input Options
% 27.77/4.02  
% 27.77/4.02  --out_options                           all
% 27.77/4.02  --tptp_safe_out                         true
% 27.77/4.02  --problem_path                          ""
% 27.77/4.02  --include_path                          ""
% 27.77/4.02  --clausifier                            res/vclausify_rel
% 27.77/4.02  --clausifier_options                    ""
% 27.77/4.02  --stdin                                 false
% 27.77/4.02  --stats_out                             all
% 27.77/4.02  
% 27.77/4.02  ------ General Options
% 27.77/4.02  
% 27.77/4.02  --fof                                   false
% 27.77/4.02  --time_out_real                         305.
% 27.77/4.02  --time_out_virtual                      -1.
% 27.77/4.02  --symbol_type_check                     false
% 27.77/4.02  --clausify_out                          false
% 27.77/4.02  --sig_cnt_out                           false
% 27.77/4.02  --trig_cnt_out                          false
% 27.77/4.02  --trig_cnt_out_tolerance                1.
% 27.77/4.02  --trig_cnt_out_sk_spl                   false
% 27.77/4.02  --abstr_cl_out                          false
% 27.77/4.02  
% 27.77/4.02  ------ Global Options
% 27.77/4.02  
% 27.77/4.02  --schedule                              default
% 27.77/4.02  --add_important_lit                     false
% 27.77/4.02  --prop_solver_per_cl                    1000
% 27.77/4.02  --min_unsat_core                        false
% 27.77/4.02  --soft_assumptions                      false
% 27.77/4.02  --soft_lemma_size                       3
% 27.77/4.02  --prop_impl_unit_size                   0
% 27.77/4.02  --prop_impl_unit                        []
% 27.77/4.02  --share_sel_clauses                     true
% 27.77/4.02  --reset_solvers                         false
% 27.77/4.02  --bc_imp_inh                            [conj_cone]
% 27.77/4.02  --conj_cone_tolerance                   3.
% 27.77/4.02  --extra_neg_conj                        none
% 27.77/4.02  --large_theory_mode                     true
% 27.77/4.02  --prolific_symb_bound                   200
% 27.77/4.02  --lt_threshold                          2000
% 27.77/4.02  --clause_weak_htbl                      true
% 27.77/4.02  --gc_record_bc_elim                     false
% 27.77/4.02  
% 27.77/4.02  ------ Preprocessing Options
% 27.77/4.02  
% 27.77/4.02  --preprocessing_flag                    true
% 27.77/4.02  --time_out_prep_mult                    0.1
% 27.77/4.02  --splitting_mode                        input
% 27.77/4.02  --splitting_grd                         true
% 27.77/4.02  --splitting_cvd                         false
% 27.77/4.02  --splitting_cvd_svl                     false
% 27.77/4.02  --splitting_nvd                         32
% 27.77/4.02  --sub_typing                            true
% 27.77/4.02  --prep_gs_sim                           true
% 27.77/4.02  --prep_unflatten                        true
% 27.77/4.02  --prep_res_sim                          true
% 27.77/4.02  --prep_upred                            true
% 27.77/4.02  --prep_sem_filter                       exhaustive
% 27.77/4.02  --prep_sem_filter_out                   false
% 27.77/4.02  --pred_elim                             true
% 27.77/4.02  --res_sim_input                         true
% 27.77/4.02  --eq_ax_congr_red                       true
% 27.77/4.02  --pure_diseq_elim                       true
% 27.77/4.02  --brand_transform                       false
% 27.77/4.02  --non_eq_to_eq                          false
% 27.77/4.02  --prep_def_merge                        true
% 27.77/4.02  --prep_def_merge_prop_impl              false
% 27.77/4.02  --prep_def_merge_mbd                    true
% 27.77/4.02  --prep_def_merge_tr_red                 false
% 27.77/4.02  --prep_def_merge_tr_cl                  false
% 27.77/4.02  --smt_preprocessing                     true
% 27.77/4.02  --smt_ac_axioms                         fast
% 27.77/4.02  --preprocessed_out                      false
% 27.77/4.02  --preprocessed_stats                    false
% 27.77/4.02  
% 27.77/4.02  ------ Abstraction refinement Options
% 27.77/4.02  
% 27.77/4.02  --abstr_ref                             []
% 27.77/4.02  --abstr_ref_prep                        false
% 27.77/4.02  --abstr_ref_until_sat                   false
% 27.77/4.02  --abstr_ref_sig_restrict                funpre
% 27.77/4.02  --abstr_ref_af_restrict_to_split_sk     false
% 27.77/4.02  --abstr_ref_under                       []
% 27.77/4.02  
% 27.77/4.02  ------ SAT Options
% 27.77/4.02  
% 27.77/4.02  --sat_mode                              false
% 27.77/4.02  --sat_fm_restart_options                ""
% 27.77/4.02  --sat_gr_def                            false
% 27.77/4.02  --sat_epr_types                         true
% 27.77/4.02  --sat_non_cyclic_types                  false
% 27.77/4.02  --sat_finite_models                     false
% 27.77/4.02  --sat_fm_lemmas                         false
% 27.77/4.02  --sat_fm_prep                           false
% 27.77/4.02  --sat_fm_uc_incr                        true
% 27.77/4.02  --sat_out_model                         small
% 27.77/4.02  --sat_out_clauses                       false
% 27.77/4.02  
% 27.77/4.02  ------ QBF Options
% 27.77/4.02  
% 27.77/4.02  --qbf_mode                              false
% 27.77/4.02  --qbf_elim_univ                         false
% 27.77/4.02  --qbf_dom_inst                          none
% 27.77/4.02  --qbf_dom_pre_inst                      false
% 27.77/4.02  --qbf_sk_in                             false
% 27.77/4.02  --qbf_pred_elim                         true
% 27.77/4.02  --qbf_split                             512
% 27.77/4.02  
% 27.77/4.02  ------ BMC1 Options
% 27.77/4.02  
% 27.77/4.02  --bmc1_incremental                      false
% 27.77/4.02  --bmc1_axioms                           reachable_all
% 27.77/4.02  --bmc1_min_bound                        0
% 27.77/4.02  --bmc1_max_bound                        -1
% 27.77/4.02  --bmc1_max_bound_default                -1
% 27.77/4.02  --bmc1_symbol_reachability              true
% 27.77/4.02  --bmc1_property_lemmas                  false
% 27.77/4.02  --bmc1_k_induction                      false
% 27.77/4.02  --bmc1_non_equiv_states                 false
% 27.77/4.02  --bmc1_deadlock                         false
% 27.77/4.02  --bmc1_ucm                              false
% 27.77/4.02  --bmc1_add_unsat_core                   none
% 27.77/4.02  --bmc1_unsat_core_children              false
% 27.77/4.02  --bmc1_unsat_core_extrapolate_axioms    false
% 27.77/4.02  --bmc1_out_stat                         full
% 27.77/4.02  --bmc1_ground_init                      false
% 27.77/4.02  --bmc1_pre_inst_next_state              false
% 27.77/4.02  --bmc1_pre_inst_state                   false
% 27.77/4.02  --bmc1_pre_inst_reach_state             false
% 27.77/4.02  --bmc1_out_unsat_core                   false
% 27.77/4.02  --bmc1_aig_witness_out                  false
% 27.77/4.02  --bmc1_verbose                          false
% 27.77/4.02  --bmc1_dump_clauses_tptp                false
% 27.77/4.02  --bmc1_dump_unsat_core_tptp             false
% 27.77/4.02  --bmc1_dump_file                        -
% 27.77/4.02  --bmc1_ucm_expand_uc_limit              128
% 27.77/4.02  --bmc1_ucm_n_expand_iterations          6
% 27.77/4.02  --bmc1_ucm_extend_mode                  1
% 27.77/4.02  --bmc1_ucm_init_mode                    2
% 27.77/4.02  --bmc1_ucm_cone_mode                    none
% 27.77/4.02  --bmc1_ucm_reduced_relation_type        0
% 27.77/4.02  --bmc1_ucm_relax_model                  4
% 27.77/4.02  --bmc1_ucm_full_tr_after_sat            true
% 27.77/4.02  --bmc1_ucm_expand_neg_assumptions       false
% 27.77/4.02  --bmc1_ucm_layered_model                none
% 27.77/4.02  --bmc1_ucm_max_lemma_size               10
% 27.77/4.02  
% 27.77/4.02  ------ AIG Options
% 27.77/4.02  
% 27.77/4.02  --aig_mode                              false
% 27.77/4.02  
% 27.77/4.02  ------ Instantiation Options
% 27.77/4.02  
% 27.77/4.02  --instantiation_flag                    true
% 27.77/4.02  --inst_sos_flag                         true
% 27.77/4.02  --inst_sos_phase                        true
% 27.77/4.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.77/4.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.77/4.02  --inst_lit_sel_side                     none
% 27.77/4.02  --inst_solver_per_active                1400
% 27.77/4.02  --inst_solver_calls_frac                1.
% 27.77/4.02  --inst_passive_queue_type               priority_queues
% 27.77/4.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.77/4.02  --inst_passive_queues_freq              [25;2]
% 27.77/4.02  --inst_dismatching                      true
% 27.77/4.02  --inst_eager_unprocessed_to_passive     true
% 27.77/4.02  --inst_prop_sim_given                   true
% 27.77/4.02  --inst_prop_sim_new                     false
% 27.77/4.02  --inst_subs_new                         false
% 27.77/4.02  --inst_eq_res_simp                      false
% 27.77/4.02  --inst_subs_given                       false
% 27.77/4.02  --inst_orphan_elimination               true
% 27.77/4.02  --inst_learning_loop_flag               true
% 27.77/4.02  --inst_learning_start                   3000
% 27.77/4.02  --inst_learning_factor                  2
% 27.77/4.02  --inst_start_prop_sim_after_learn       3
% 27.77/4.02  --inst_sel_renew                        solver
% 27.77/4.02  --inst_lit_activity_flag                true
% 27.77/4.02  --inst_restr_to_given                   false
% 27.77/4.02  --inst_activity_threshold               500
% 27.77/4.02  --inst_out_proof                        true
% 27.77/4.02  
% 27.77/4.02  ------ Resolution Options
% 27.77/4.02  
% 27.77/4.02  --resolution_flag                       false
% 27.77/4.02  --res_lit_sel                           adaptive
% 27.77/4.02  --res_lit_sel_side                      none
% 27.77/4.02  --res_ordering                          kbo
% 27.77/4.02  --res_to_prop_solver                    active
% 27.77/4.02  --res_prop_simpl_new                    false
% 27.77/4.02  --res_prop_simpl_given                  true
% 27.77/4.02  --res_passive_queue_type                priority_queues
% 27.77/4.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.77/4.02  --res_passive_queues_freq               [15;5]
% 27.77/4.02  --res_forward_subs                      full
% 27.77/4.02  --res_backward_subs                     full
% 27.77/4.02  --res_forward_subs_resolution           true
% 27.77/4.02  --res_backward_subs_resolution          true
% 27.77/4.02  --res_orphan_elimination                true
% 27.77/4.02  --res_time_limit                        2.
% 27.77/4.02  --res_out_proof                         true
% 27.77/4.02  
% 27.77/4.02  ------ Superposition Options
% 27.77/4.02  
% 27.77/4.02  --superposition_flag                    true
% 27.77/4.02  --sup_passive_queue_type                priority_queues
% 27.77/4.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.77/4.02  --sup_passive_queues_freq               [8;1;4]
% 27.77/4.02  --demod_completeness_check              fast
% 27.77/4.02  --demod_use_ground                      true
% 27.77/4.02  --sup_to_prop_solver                    passive
% 27.77/4.02  --sup_prop_simpl_new                    true
% 27.77/4.02  --sup_prop_simpl_given                  true
% 27.77/4.02  --sup_fun_splitting                     true
% 27.77/4.02  --sup_smt_interval                      50000
% 27.77/4.02  
% 27.77/4.02  ------ Superposition Simplification Setup
% 27.77/4.02  
% 27.77/4.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.77/4.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.77/4.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.77/4.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.77/4.02  --sup_full_triv                         [TrivRules;PropSubs]
% 27.77/4.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.77/4.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.77/4.02  --sup_immed_triv                        [TrivRules]
% 27.77/4.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.77/4.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.77/4.02  --sup_immed_bw_main                     []
% 27.77/4.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.77/4.02  --sup_input_triv                        [Unflattening;TrivRules]
% 27.77/4.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.77/4.02  --sup_input_bw                          []
% 27.77/4.02  
% 27.77/4.02  ------ Combination Options
% 27.77/4.02  
% 27.77/4.02  --comb_res_mult                         3
% 27.77/4.02  --comb_sup_mult                         2
% 27.77/4.02  --comb_inst_mult                        10
% 27.77/4.02  
% 27.77/4.02  ------ Debug Options
% 27.77/4.02  
% 27.77/4.02  --dbg_backtrace                         false
% 27.77/4.02  --dbg_dump_prop_clauses                 false
% 27.77/4.02  --dbg_dump_prop_clauses_file            -
% 27.77/4.02  --dbg_out_stat                          false
% 27.77/4.02  
% 27.77/4.02  
% 27.77/4.02  
% 27.77/4.02  
% 27.77/4.02  ------ Proving...
% 27.77/4.02  
% 27.77/4.02  
% 27.77/4.02  % SZS status Theorem for theBenchmark.p
% 27.77/4.02  
% 27.77/4.02  % SZS output start CNFRefutation for theBenchmark.p
% 27.77/4.02  
% 27.77/4.02  fof(f2,axiom,(
% 27.77/4.02    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 27.77/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.77/4.02  
% 27.77/4.02  fof(f58,plain,(
% 27.77/4.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 27.77/4.02    inference(cnf_transformation,[],[f2])).
% 27.77/4.02  
% 27.77/4.02  fof(f3,axiom,(
% 27.77/4.02    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 27.77/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.77/4.02  
% 27.77/4.02  fof(f59,plain,(
% 27.77/4.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 27.77/4.02    inference(cnf_transformation,[],[f3])).
% 27.77/4.02  
% 27.77/4.02  fof(f4,axiom,(
% 27.77/4.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 27.77/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.77/4.02  
% 27.77/4.02  fof(f60,plain,(
% 27.77/4.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 27.77/4.02    inference(cnf_transformation,[],[f4])).
% 27.77/4.02  
% 27.77/4.02  fof(f90,plain,(
% 27.77/4.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 27.77/4.02    inference(definition_unfolding,[],[f59,f60])).
% 27.77/4.02  
% 27.77/4.02  fof(f92,plain,(
% 27.77/4.02    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 27.77/4.02    inference(definition_unfolding,[],[f58,f90,f90])).
% 27.77/4.02  
% 27.77/4.02  fof(f23,conjecture,(
% 27.77/4.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)) & k3_xboole_0(k1_relat_1(X2),X0) = k1_relat_1(X1)) => k7_relat_1(X2,X0) = X1)))),
% 27.77/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.77/4.02  
% 27.77/4.02  fof(f24,negated_conjecture,(
% 27.77/4.02    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X1,X3) = k1_funct_1(X2,X3)) & k3_xboole_0(k1_relat_1(X2),X0) = k1_relat_1(X1)) => k7_relat_1(X2,X0) = X1)))),
% 27.77/4.02    inference(negated_conjecture,[],[f23])).
% 27.77/4.02  
% 27.77/4.02  fof(f46,plain,(
% 27.77/4.02    ? [X0,X1] : (? [X2] : ((k7_relat_1(X2,X0) != X1 & (! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & k3_xboole_0(k1_relat_1(X2),X0) = k1_relat_1(X1))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 27.77/4.02    inference(ennf_transformation,[],[f24])).
% 27.77/4.02  
% 27.77/4.02  fof(f47,plain,(
% 27.77/4.02    ? [X0,X1] : (? [X2] : (k7_relat_1(X2,X0) != X1 & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & k3_xboole_0(k1_relat_1(X2),X0) = k1_relat_1(X1) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 27.77/4.02    inference(flattening,[],[f46])).
% 27.77/4.02  
% 27.77/4.02  fof(f53,plain,(
% 27.77/4.02    ( ! [X0,X1] : (? [X2] : (k7_relat_1(X2,X0) != X1 & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & k3_xboole_0(k1_relat_1(X2),X0) = k1_relat_1(X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (k7_relat_1(sK3,X0) != X1 & ! [X3] : (k1_funct_1(sK3,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & k3_xboole_0(k1_relat_1(sK3),X0) = k1_relat_1(X1) & v1_funct_1(sK3) & v1_relat_1(sK3))) )),
% 27.77/4.02    introduced(choice_axiom,[])).
% 27.77/4.02  
% 27.77/4.02  fof(f52,plain,(
% 27.77/4.02    ? [X0,X1] : (? [X2] : (k7_relat_1(X2,X0) != X1 & ! [X3] : (k1_funct_1(X1,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & k3_xboole_0(k1_relat_1(X2),X0) = k1_relat_1(X1) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : (k7_relat_1(X2,sK1) != sK2 & ! [X3] : (k1_funct_1(sK2,X3) = k1_funct_1(X2,X3) | ~r2_hidden(X3,k1_relat_1(sK2))) & k3_xboole_0(k1_relat_1(X2),sK1) = k1_relat_1(sK2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 27.77/4.02    introduced(choice_axiom,[])).
% 27.77/4.02  
% 27.77/4.02  fof(f54,plain,(
% 27.77/4.02    (k7_relat_1(sK3,sK1) != sK2 & ! [X3] : (k1_funct_1(sK2,X3) = k1_funct_1(sK3,X3) | ~r2_hidden(X3,k1_relat_1(sK2))) & k3_xboole_0(k1_relat_1(sK3),sK1) = k1_relat_1(sK2) & v1_funct_1(sK3) & v1_relat_1(sK3)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 27.77/4.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f47,f53,f52])).
% 27.77/4.02  
% 27.77/4.02  fof(f85,plain,(
% 27.77/4.02    v1_relat_1(sK3)),
% 27.77/4.02    inference(cnf_transformation,[],[f54])).
% 27.77/4.02  
% 27.77/4.02  fof(f15,axiom,(
% 27.77/4.02    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 27.77/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.77/4.02  
% 27.77/4.02  fof(f34,plain,(
% 27.77/4.02    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 27.77/4.02    inference(ennf_transformation,[],[f15])).
% 27.77/4.02  
% 27.77/4.02  fof(f72,plain,(
% 27.77/4.02    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 27.77/4.02    inference(cnf_transformation,[],[f34])).
% 27.77/4.02  
% 27.77/4.02  fof(f5,axiom,(
% 27.77/4.02    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 27.77/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.77/4.02  
% 27.77/4.02  fof(f61,plain,(
% 27.77/4.02    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 27.77/4.02    inference(cnf_transformation,[],[f5])).
% 27.77/4.02  
% 27.77/4.02  fof(f91,plain,(
% 27.77/4.02    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k3_xboole_0(X0,X1)) )),
% 27.77/4.02    inference(definition_unfolding,[],[f61,f90])).
% 27.77/4.02  
% 27.77/4.02  fof(f94,plain,(
% 27.77/4.02    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 27.77/4.02    inference(definition_unfolding,[],[f72,f91])).
% 27.77/4.02  
% 27.77/4.02  fof(f87,plain,(
% 27.77/4.02    k3_xboole_0(k1_relat_1(sK3),sK1) = k1_relat_1(sK2)),
% 27.77/4.02    inference(cnf_transformation,[],[f54])).
% 27.77/4.02  
% 27.77/4.02  fof(f96,plain,(
% 27.77/4.02    k1_setfam_1(k2_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),sK1)) = k1_relat_1(sK2)),
% 27.77/4.02    inference(definition_unfolding,[],[f87,f91])).
% 27.77/4.02  
% 27.77/4.02  fof(f83,plain,(
% 27.77/4.02    v1_relat_1(sK2)),
% 27.77/4.02    inference(cnf_transformation,[],[f54])).
% 27.77/4.02  
% 27.77/4.02  fof(f6,axiom,(
% 27.77/4.02    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 27.77/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.77/4.02  
% 27.77/4.02  fof(f25,plain,(
% 27.77/4.02    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 27.77/4.02    inference(ennf_transformation,[],[f6])).
% 27.77/4.02  
% 27.77/4.02  fof(f62,plain,(
% 27.77/4.02    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 27.77/4.02    inference(cnf_transformation,[],[f25])).
% 27.77/4.02  
% 27.77/4.02  fof(f8,axiom,(
% 27.77/4.02    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0))),
% 27.77/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.77/4.02  
% 27.77/4.02  fof(f27,plain,(
% 27.77/4.02    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) | ~v1_relat_1(X1))),
% 27.77/4.02    inference(ennf_transformation,[],[f8])).
% 27.77/4.02  
% 27.77/4.02  fof(f64,plain,(
% 27.77/4.02    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(k7_relat_1(X1,X0),X0) | ~v1_relat_1(X1)) )),
% 27.77/4.02    inference(cnf_transformation,[],[f27])).
% 27.77/4.02  
% 27.77/4.02  fof(f13,axiom,(
% 27.77/4.02    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 27.77/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.77/4.02  
% 27.77/4.02  fof(f32,plain,(
% 27.77/4.02    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 27.77/4.02    inference(ennf_transformation,[],[f13])).
% 27.77/4.02  
% 27.77/4.02  fof(f70,plain,(
% 27.77/4.02    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 27.77/4.02    inference(cnf_transformation,[],[f32])).
% 27.77/4.02  
% 27.77/4.02  fof(f16,axiom,(
% 27.77/4.02    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 27.77/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.77/4.02  
% 27.77/4.02  fof(f35,plain,(
% 27.77/4.02    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 27.77/4.02    inference(ennf_transformation,[],[f16])).
% 27.77/4.02  
% 27.77/4.02  fof(f36,plain,(
% 27.77/4.02    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 27.77/4.02    inference(flattening,[],[f35])).
% 27.77/4.02  
% 27.77/4.02  fof(f73,plain,(
% 27.77/4.02    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 27.77/4.02    inference(cnf_transformation,[],[f36])).
% 27.77/4.02  
% 27.77/4.02  fof(f22,axiom,(
% 27.77/4.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 27.77/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.77/4.02  
% 27.77/4.02  fof(f44,plain,(
% 27.77/4.02    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 27.77/4.02    inference(ennf_transformation,[],[f22])).
% 27.77/4.02  
% 27.77/4.02  fof(f45,plain,(
% 27.77/4.02    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.77/4.02    inference(flattening,[],[f44])).
% 27.77/4.02  
% 27.77/4.02  fof(f50,plain,(
% 27.77/4.02    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))))),
% 27.77/4.02    introduced(choice_axiom,[])).
% 27.77/4.02  
% 27.77/4.02  fof(f51,plain,(
% 27.77/4.02    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) & r2_hidden(sK0(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.77/4.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f50])).
% 27.77/4.02  
% 27.77/4.02  fof(f81,plain,(
% 27.77/4.02    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.77/4.02    inference(cnf_transformation,[],[f51])).
% 27.77/4.02  
% 27.77/4.02  fof(f18,axiom,(
% 27.77/4.02    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 27.77/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.77/4.02  
% 27.77/4.02  fof(f39,plain,(
% 27.77/4.02    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 27.77/4.02    inference(ennf_transformation,[],[f18])).
% 27.77/4.02  
% 27.77/4.02  fof(f75,plain,(
% 27.77/4.02    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 27.77/4.02    inference(cnf_transformation,[],[f39])).
% 27.77/4.02  
% 27.77/4.02  fof(f19,axiom,(
% 27.77/4.02    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 27.77/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.77/4.02  
% 27.77/4.02  fof(f76,plain,(
% 27.77/4.02    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 27.77/4.02    inference(cnf_transformation,[],[f19])).
% 27.77/4.02  
% 27.77/4.02  fof(f11,axiom,(
% 27.77/4.02    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 27.77/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.77/4.02  
% 27.77/4.02  fof(f67,plain,(
% 27.77/4.02    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 27.77/4.02    inference(cnf_transformation,[],[f11])).
% 27.77/4.02  
% 27.77/4.02  fof(f7,axiom,(
% 27.77/4.02    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 27.77/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.77/4.02  
% 27.77/4.02  fof(f26,plain,(
% 27.77/4.02    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 27.77/4.02    inference(ennf_transformation,[],[f7])).
% 27.77/4.02  
% 27.77/4.02  fof(f63,plain,(
% 27.77/4.02    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 27.77/4.02    inference(cnf_transformation,[],[f26])).
% 27.77/4.02  
% 27.77/4.02  fof(f93,plain,(
% 27.77/4.02    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 27.77/4.02    inference(definition_unfolding,[],[f63,f91])).
% 27.77/4.02  
% 27.77/4.02  fof(f84,plain,(
% 27.77/4.02    v1_funct_1(sK2)),
% 27.77/4.02    inference(cnf_transformation,[],[f54])).
% 27.77/4.02  
% 27.77/4.02  fof(f89,plain,(
% 27.77/4.02    k7_relat_1(sK3,sK1) != sK2),
% 27.77/4.02    inference(cnf_transformation,[],[f54])).
% 27.77/4.02  
% 27.77/4.02  fof(f86,plain,(
% 27.77/4.02    v1_funct_1(sK3)),
% 27.77/4.02    inference(cnf_transformation,[],[f54])).
% 27.77/4.02  
% 27.77/4.02  fof(f20,axiom,(
% 27.77/4.02    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 27.77/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.77/4.02  
% 27.77/4.02  fof(f40,plain,(
% 27.77/4.02    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 27.77/4.02    inference(ennf_transformation,[],[f20])).
% 27.77/4.02  
% 27.77/4.02  fof(f41,plain,(
% 27.77/4.02    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.77/4.02    inference(flattening,[],[f40])).
% 27.77/4.02  
% 27.77/4.02  fof(f79,plain,(
% 27.77/4.02    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.77/4.02    inference(cnf_transformation,[],[f41])).
% 27.77/4.02  
% 27.77/4.02  fof(f9,axiom,(
% 27.77/4.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 27.77/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.77/4.02  
% 27.77/4.02  fof(f28,plain,(
% 27.77/4.02    ! [X0] : (! [X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 27.77/4.02    inference(ennf_transformation,[],[f9])).
% 27.77/4.02  
% 27.77/4.02  fof(f65,plain,(
% 27.77/4.02    ( ! [X0,X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 27.77/4.02    inference(cnf_transformation,[],[f28])).
% 27.77/4.02  
% 27.77/4.02  fof(f21,axiom,(
% 27.77/4.02    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 27.77/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.77/4.02  
% 27.77/4.02  fof(f42,plain,(
% 27.77/4.02    ! [X0,X1,X2] : ((k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) | ~r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 27.77/4.02    inference(ennf_transformation,[],[f21])).
% 27.77/4.02  
% 27.77/4.02  fof(f43,plain,(
% 27.77/4.02    ! [X0,X1,X2] : (k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) | ~r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 27.77/4.02    inference(flattening,[],[f42])).
% 27.77/4.02  
% 27.77/4.02  fof(f80,plain,(
% 27.77/4.02    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) | ~r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 27.77/4.02    inference(cnf_transformation,[],[f43])).
% 27.77/4.02  
% 27.77/4.02  fof(f95,plain,(
% 27.77/4.02    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) | ~r2_hidden(X0,k1_setfam_1(k2_enumset1(k1_relat_1(X2),k1_relat_1(X2),k1_relat_1(X2),X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 27.77/4.02    inference(definition_unfolding,[],[f80,f91])).
% 27.77/4.02  
% 27.77/4.02  fof(f14,axiom,(
% 27.77/4.02    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 27.77/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.77/4.02  
% 27.77/4.02  fof(f33,plain,(
% 27.77/4.02    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 27.77/4.02    inference(ennf_transformation,[],[f14])).
% 27.77/4.02  
% 27.77/4.02  fof(f71,plain,(
% 27.77/4.02    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 27.77/4.02    inference(cnf_transformation,[],[f33])).
% 27.77/4.02  
% 27.77/4.02  fof(f68,plain,(
% 27.77/4.02    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 27.77/4.02    inference(cnf_transformation,[],[f11])).
% 27.77/4.02  
% 27.77/4.02  fof(f10,axiom,(
% 27.77/4.02    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)))))),
% 27.77/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.77/4.02  
% 27.77/4.02  fof(f29,plain,(
% 27.77/4.02    ! [X0,X1] : (! [X2] : ((k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 27.77/4.02    inference(ennf_transformation,[],[f10])).
% 27.77/4.02  
% 27.77/4.02  fof(f30,plain,(
% 27.77/4.02    ! [X0,X1] : (! [X2] : (k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 27.77/4.02    inference(flattening,[],[f29])).
% 27.77/4.02  
% 27.77/4.02  fof(f66,plain,(
% 27.77/4.02    ( ! [X2,X0,X1] : (k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 27.77/4.02    inference(cnf_transformation,[],[f30])).
% 27.77/4.02  
% 27.77/4.02  fof(f12,axiom,(
% 27.77/4.02    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 27.77/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.77/4.02  
% 27.77/4.02  fof(f31,plain,(
% 27.77/4.02    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 27.77/4.02    inference(ennf_transformation,[],[f12])).
% 27.77/4.02  
% 27.77/4.02  fof(f69,plain,(
% 27.77/4.02    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 27.77/4.02    inference(cnf_transformation,[],[f31])).
% 27.77/4.02  
% 27.77/4.02  fof(f82,plain,(
% 27.77/4.02    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK0(X0,X1)) != k1_funct_1(X1,sK0(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.77/4.02    inference(cnf_transformation,[],[f51])).
% 27.77/4.02  
% 27.77/4.02  fof(f88,plain,(
% 27.77/4.02    ( ! [X3] : (k1_funct_1(sK2,X3) = k1_funct_1(sK3,X3) | ~r2_hidden(X3,k1_relat_1(sK2))) )),
% 27.77/4.02    inference(cnf_transformation,[],[f54])).
% 27.77/4.02  
% 27.77/4.02  cnf(c_3,plain,
% 27.77/4.02      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 27.77/4.02      inference(cnf_transformation,[],[f92]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_29,negated_conjecture,
% 27.77/4.02      ( v1_relat_1(sK3) ),
% 27.77/4.02      inference(cnf_transformation,[],[f85]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_1079,plain,
% 27.77/4.02      ( v1_relat_1(sK3) = iProver_top ),
% 27.77/4.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_14,plain,
% 27.77/4.02      ( ~ v1_relat_1(X0)
% 27.77/4.02      | k1_setfam_1(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 27.77/4.02      inference(cnf_transformation,[],[f94]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_1091,plain,
% 27.77/4.02      ( k1_setfam_1(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 27.77/4.02      | v1_relat_1(X0) != iProver_top ),
% 27.77/4.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_3642,plain,
% 27.77/4.02      ( k1_setfam_1(k2_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_1079,c_1091]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_4415,plain,
% 27.77/4.02      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k1_relat_1(sK3))) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_3,c_3642]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_27,negated_conjecture,
% 27.77/4.02      ( k1_setfam_1(k2_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),k1_relat_1(sK3),sK1)) = k1_relat_1(sK2) ),
% 27.77/4.02      inference(cnf_transformation,[],[f96]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_1564,plain,
% 27.77/4.02      ( k1_setfam_1(k2_enumset1(sK1,sK1,sK1,k1_relat_1(sK3))) = k1_relat_1(sK2) ),
% 27.77/4.02      inference(demodulation,[status(thm)],[c_3,c_27]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_4658,plain,
% 27.77/4.02      ( k1_relat_1(k7_relat_1(sK3,sK1)) = k1_relat_1(sK2) ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_4415,c_1564]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_31,negated_conjecture,
% 27.77/4.02      ( v1_relat_1(sK2) ),
% 27.77/4.02      inference(cnf_transformation,[],[f83]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_1077,plain,
% 27.77/4.02      ( v1_relat_1(sK2) = iProver_top ),
% 27.77/4.02      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_4,plain,
% 27.77/4.02      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 27.77/4.02      inference(cnf_transformation,[],[f62]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_1099,plain,
% 27.77/4.02      ( v1_relat_1(X0) != iProver_top
% 27.77/4.02      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 27.77/4.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_6,plain,
% 27.77/4.02      ( ~ v1_relat_1(X0)
% 27.77/4.02      | k7_relat_1(k7_relat_1(X0,X1),X1) = k7_relat_1(X0,X1) ),
% 27.77/4.02      inference(cnf_transformation,[],[f64]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_1097,plain,
% 27.77/4.02      ( k7_relat_1(k7_relat_1(X0,X1),X1) = k7_relat_1(X0,X1)
% 27.77/4.02      | v1_relat_1(X0) != iProver_top ),
% 27.77/4.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_2207,plain,
% 27.77/4.02      ( k7_relat_1(k7_relat_1(sK3,X0),X0) = k7_relat_1(sK3,X0) ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_1079,c_1097]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_12,plain,
% 27.77/4.02      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 27.77/4.02      inference(cnf_transformation,[],[f70]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_1093,plain,
% 27.77/4.02      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 27.77/4.02      | v1_relat_1(X0) != iProver_top ),
% 27.77/4.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_2439,plain,
% 27.77/4.02      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) = iProver_top
% 27.77/4.02      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_2207,c_1093]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_15,plain,
% 27.77/4.02      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 27.77/4.02      | ~ v1_relat_1(X1)
% 27.77/4.02      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 27.77/4.02      inference(cnf_transformation,[],[f73]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_1090,plain,
% 27.77/4.02      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 27.77/4.02      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 27.77/4.02      | v1_relat_1(X0) != iProver_top ),
% 27.77/4.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_3194,plain,
% 27.77/4.02      ( k1_relat_1(k7_relat_1(X0,k1_relat_1(k7_relat_1(sK3,k1_relat_1(X0))))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(X0)))
% 27.77/4.02      | v1_relat_1(X0) != iProver_top
% 27.77/4.02      | v1_relat_1(k7_relat_1(sK3,k1_relat_1(X0))) != iProver_top ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_2439,c_1090]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_3311,plain,
% 27.77/4.02      ( k1_relat_1(k7_relat_1(X0,k1_relat_1(k7_relat_1(sK3,k1_relat_1(X0))))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(X0)))
% 27.77/4.02      | v1_relat_1(X0) != iProver_top
% 27.77/4.02      | v1_relat_1(sK3) != iProver_top ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_1099,c_3194]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_34,plain,
% 27.77/4.02      ( v1_relat_1(sK3) = iProver_top ),
% 27.77/4.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_3427,plain,
% 27.77/4.02      ( v1_relat_1(X0) != iProver_top
% 27.77/4.02      | k1_relat_1(k7_relat_1(X0,k1_relat_1(k7_relat_1(sK3,k1_relat_1(X0))))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(X0))) ),
% 27.77/4.02      inference(global_propositional_subsumption,
% 27.77/4.02                [status(thm)],
% 27.77/4.02                [c_3311,c_34]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_3428,plain,
% 27.77/4.02      ( k1_relat_1(k7_relat_1(X0,k1_relat_1(k7_relat_1(sK3,k1_relat_1(X0))))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(X0)))
% 27.77/4.02      | v1_relat_1(X0) != iProver_top ),
% 27.77/4.02      inference(renaming,[status(thm)],[c_3427]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_3434,plain,
% 27.77/4.02      ( k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2))))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2))) ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_1077,c_3428]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_24,plain,
% 27.77/4.02      ( r2_hidden(sK0(X0,X1),k1_relat_1(X0))
% 27.77/4.02      | ~ v1_funct_1(X0)
% 27.77/4.02      | ~ v1_funct_1(X1)
% 27.77/4.02      | ~ v1_relat_1(X0)
% 27.77/4.02      | ~ v1_relat_1(X1)
% 27.77/4.02      | X1 = X0
% 27.77/4.02      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 27.77/4.02      inference(cnf_transformation,[],[f81]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_1082,plain,
% 27.77/4.02      ( X0 = X1
% 27.77/4.02      | k1_relat_1(X1) != k1_relat_1(X0)
% 27.77/4.02      | r2_hidden(sK0(X1,X0),k1_relat_1(X1)) = iProver_top
% 27.77/4.02      | v1_funct_1(X1) != iProver_top
% 27.77/4.02      | v1_funct_1(X0) != iProver_top
% 27.77/4.02      | v1_relat_1(X1) != iProver_top
% 27.77/4.02      | v1_relat_1(X0) != iProver_top ),
% 27.77/4.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_3512,plain,
% 27.77/4.02      ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2)))) = X0
% 27.77/4.02      | k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2))) != k1_relat_1(X0)
% 27.77/4.02      | r2_hidden(sK0(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2)))),X0),k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2)))))) = iProver_top
% 27.77/4.02      | v1_funct_1(X0) != iProver_top
% 27.77/4.02      | v1_funct_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2))))) != iProver_top
% 27.77/4.02      | v1_relat_1(X0) != iProver_top
% 27.77/4.02      | v1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2))))) != iProver_top ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_3434,c_1082]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_3524,plain,
% 27.77/4.02      ( k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2)))) = X0
% 27.77/4.02      | k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2))) != k1_relat_1(X0)
% 27.77/4.02      | r2_hidden(sK0(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2)))),X0),k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2)))) = iProver_top
% 27.77/4.02      | v1_funct_1(X0) != iProver_top
% 27.77/4.02      | v1_funct_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2))))) != iProver_top
% 27.77/4.02      | v1_relat_1(X0) != iProver_top
% 27.77/4.02      | v1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2))))) != iProver_top ),
% 27.77/4.02      inference(light_normalisation,[status(thm)],[c_3512,c_3434]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_17,plain,
% 27.77/4.02      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 27.77/4.02      inference(cnf_transformation,[],[f75]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_1088,plain,
% 27.77/4.02      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 27.77/4.02      | v1_relat_1(X0) != iProver_top ),
% 27.77/4.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_1712,plain,
% 27.77/4.02      ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_1077,c_1088]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_19,plain,
% 27.77/4.02      ( v1_relat_1(k6_relat_1(X0)) ),
% 27.77/4.02      inference(cnf_transformation,[],[f76]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_1086,plain,
% 27.77/4.02      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 27.77/4.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_3641,plain,
% 27.77/4.02      ( k1_setfam_1(k2_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_1086,c_1091]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_10,plain,
% 27.77/4.02      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 27.77/4.02      inference(cnf_transformation,[],[f67]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_3644,plain,
% 27.77/4.02      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 27.77/4.02      inference(light_normalisation,[status(thm)],[c_3641,c_10]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_3734,plain,
% 27.77/4.02      ( k1_relat_1(k7_relat_1(k6_relat_1(sK1),k1_relat_1(sK3))) = k1_relat_1(sK2) ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_3644,c_1564]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_5,plain,
% 27.77/4.02      ( ~ v1_relat_1(X0)
% 27.77/4.02      | k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 27.77/4.02      inference(cnf_transformation,[],[f93]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_1098,plain,
% 27.77/4.02      ( k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
% 27.77/4.02      | v1_relat_1(X0) != iProver_top ),
% 27.77/4.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_3732,plain,
% 27.77/4.02      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_3,c_3644]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_3930,plain,
% 27.77/4.02      ( k7_relat_1(X0,k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k7_relat_1(X0,X2),X1)
% 27.77/4.02      | v1_relat_1(X0) != iProver_top ),
% 27.77/4.02      inference(demodulation,[status(thm)],[c_1098,c_3732]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_3936,plain,
% 27.77/4.02      ( k7_relat_1(sK3,k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k7_relat_1(sK3,X1),X0) ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_1079,c_3930]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_4213,plain,
% 27.77/4.02      ( k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),sK1) = k7_relat_1(sK3,k1_relat_1(sK2)) ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_3734,c_3936]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_1711,plain,
% 27.77/4.02      ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_1079,c_1088]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_4227,plain,
% 27.77/4.02      ( k7_relat_1(sK3,k1_relat_1(sK2)) = k7_relat_1(sK3,sK1) ),
% 27.77/4.02      inference(light_normalisation,[status(thm)],[c_4213,c_1711]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_35508,plain,
% 27.77/4.02      ( k1_relat_1(X0) != k1_relat_1(sK2)
% 27.77/4.02      | sK2 = X0
% 27.77/4.02      | r2_hidden(sK0(sK2,X0),k1_relat_1(sK2)) = iProver_top
% 27.77/4.02      | v1_funct_1(X0) != iProver_top
% 27.77/4.02      | v1_funct_1(sK2) != iProver_top
% 27.77/4.02      | v1_relat_1(X0) != iProver_top
% 27.77/4.02      | v1_relat_1(sK2) != iProver_top ),
% 27.77/4.02      inference(light_normalisation,
% 27.77/4.02                [status(thm)],
% 27.77/4.02                [c_3524,c_1712,c_4227,c_4658]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_32,plain,
% 27.77/4.02      ( v1_relat_1(sK2) = iProver_top ),
% 27.77/4.02      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_30,negated_conjecture,
% 27.77/4.02      ( v1_funct_1(sK2) ),
% 27.77/4.02      inference(cnf_transformation,[],[f84]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_33,plain,
% 27.77/4.02      ( v1_funct_1(sK2) = iProver_top ),
% 27.77/4.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_35512,plain,
% 27.77/4.02      ( v1_relat_1(X0) != iProver_top
% 27.77/4.02      | k1_relat_1(X0) != k1_relat_1(sK2)
% 27.77/4.02      | sK2 = X0
% 27.77/4.02      | r2_hidden(sK0(sK2,X0),k1_relat_1(sK2)) = iProver_top
% 27.77/4.02      | v1_funct_1(X0) != iProver_top ),
% 27.77/4.02      inference(global_propositional_subsumption,
% 27.77/4.02                [status(thm)],
% 27.77/4.02                [c_35508,c_32,c_33]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_35513,plain,
% 27.77/4.02      ( k1_relat_1(X0) != k1_relat_1(sK2)
% 27.77/4.02      | sK2 = X0
% 27.77/4.02      | r2_hidden(sK0(sK2,X0),k1_relat_1(sK2)) = iProver_top
% 27.77/4.02      | v1_funct_1(X0) != iProver_top
% 27.77/4.02      | v1_relat_1(X0) != iProver_top ),
% 27.77/4.02      inference(renaming,[status(thm)],[c_35512]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_35519,plain,
% 27.77/4.02      ( k7_relat_1(sK3,sK1) = sK2
% 27.77/4.02      | r2_hidden(sK0(sK2,k7_relat_1(sK3,sK1)),k1_relat_1(sK2)) = iProver_top
% 27.77/4.02      | v1_funct_1(k7_relat_1(sK3,sK1)) != iProver_top
% 27.77/4.02      | v1_relat_1(k7_relat_1(sK3,sK1)) != iProver_top ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_4658,c_35513]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_25,negated_conjecture,
% 27.77/4.02      ( k7_relat_1(sK3,sK1) != sK2 ),
% 27.77/4.02      inference(cnf_transformation,[],[f89]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_4902,plain,
% 27.77/4.02      ( k7_relat_1(sK3,sK1) = X0
% 27.77/4.02      | k1_relat_1(X0) != k1_relat_1(sK2)
% 27.77/4.02      | r2_hidden(sK0(X0,k7_relat_1(sK3,sK1)),k1_relat_1(X0)) = iProver_top
% 27.77/4.02      | v1_funct_1(X0) != iProver_top
% 27.77/4.02      | v1_funct_1(k7_relat_1(sK3,sK1)) != iProver_top
% 27.77/4.02      | v1_relat_1(X0) != iProver_top
% 27.77/4.02      | v1_relat_1(k7_relat_1(sK3,sK1)) != iProver_top ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_4658,c_1082]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_28,negated_conjecture,
% 27.77/4.02      ( v1_funct_1(sK3) ),
% 27.77/4.02      inference(cnf_transformation,[],[f86]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_35,plain,
% 27.77/4.02      ( v1_funct_1(sK3) = iProver_top ),
% 27.77/4.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_20,plain,
% 27.77/4.02      ( ~ v1_funct_1(X0)
% 27.77/4.02      | v1_funct_1(k7_relat_1(X0,X1))
% 27.77/4.02      | ~ v1_relat_1(X0) ),
% 27.77/4.02      inference(cnf_transformation,[],[f79]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_1153,plain,
% 27.77/4.02      ( v1_funct_1(k7_relat_1(sK3,sK1))
% 27.77/4.02      | ~ v1_funct_1(sK3)
% 27.77/4.02      | ~ v1_relat_1(sK3) ),
% 27.77/4.02      inference(instantiation,[status(thm)],[c_20]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_1154,plain,
% 27.77/4.02      ( v1_funct_1(k7_relat_1(sK3,sK1)) = iProver_top
% 27.77/4.02      | v1_funct_1(sK3) != iProver_top
% 27.77/4.02      | v1_relat_1(sK3) != iProver_top ),
% 27.77/4.02      inference(predicate_to_equality,[status(thm)],[c_1153]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_1208,plain,
% 27.77/4.02      ( v1_relat_1(k7_relat_1(sK3,sK1)) | ~ v1_relat_1(sK3) ),
% 27.77/4.02      inference(instantiation,[status(thm)],[c_4]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_1209,plain,
% 27.77/4.02      ( v1_relat_1(k7_relat_1(sK3,sK1)) = iProver_top
% 27.77/4.02      | v1_relat_1(sK3) != iProver_top ),
% 27.77/4.02      inference(predicate_to_equality,[status(thm)],[c_1208]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_34936,plain,
% 27.77/4.02      ( v1_relat_1(X0) != iProver_top
% 27.77/4.02      | k7_relat_1(sK3,sK1) = X0
% 27.77/4.02      | k1_relat_1(X0) != k1_relat_1(sK2)
% 27.77/4.02      | r2_hidden(sK0(X0,k7_relat_1(sK3,sK1)),k1_relat_1(X0)) = iProver_top
% 27.77/4.02      | v1_funct_1(X0) != iProver_top ),
% 27.77/4.02      inference(global_propositional_subsumption,
% 27.77/4.02                [status(thm)],
% 27.77/4.02                [c_4902,c_34,c_35,c_1154,c_1209]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_34937,plain,
% 27.77/4.02      ( k7_relat_1(sK3,sK1) = X0
% 27.77/4.02      | k1_relat_1(X0) != k1_relat_1(sK2)
% 27.77/4.02      | r2_hidden(sK0(X0,k7_relat_1(sK3,sK1)),k1_relat_1(X0)) = iProver_top
% 27.77/4.02      | v1_funct_1(X0) != iProver_top
% 27.77/4.02      | v1_relat_1(X0) != iProver_top ),
% 27.77/4.02      inference(renaming,[status(thm)],[c_34936]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_34960,plain,
% 27.77/4.02      ( k7_relat_1(sK3,sK1) = sK2
% 27.77/4.02      | r2_hidden(sK0(sK2,k7_relat_1(sK3,sK1)),k1_relat_1(sK2)) = iProver_top
% 27.77/4.02      | v1_funct_1(sK2) != iProver_top
% 27.77/4.02      | v1_relat_1(sK2) != iProver_top ),
% 27.77/4.02      inference(equality_resolution,[status(thm)],[c_34937]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_35707,plain,
% 27.77/4.02      ( r2_hidden(sK0(sK2,k7_relat_1(sK3,sK1)),k1_relat_1(sK2)) = iProver_top ),
% 27.77/4.02      inference(global_propositional_subsumption,
% 27.77/4.02                [status(thm)],
% 27.77/4.02                [c_35519,c_32,c_33,c_25,c_34960]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_7,plain,
% 27.77/4.02      ( ~ v1_relat_1(X0)
% 27.77/4.02      | ~ v1_relat_1(X1)
% 27.77/4.02      | k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(X1)) ),
% 27.77/4.02      inference(cnf_transformation,[],[f65]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_1096,plain,
% 27.77/4.02      ( k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(X1))
% 27.77/4.02      | v1_relat_1(X0) != iProver_top
% 27.77/4.02      | v1_relat_1(X1) != iProver_top ),
% 27.77/4.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_5670,plain,
% 27.77/4.02      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(X1,k1_relat_1(k6_relat_1(X0))))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(X1))
% 27.77/4.02      | v1_relat_1(X1) != iProver_top ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_1086,c_1096]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_5673,plain,
% 27.77/4.02      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(X1,X0))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(X1))
% 27.77/4.02      | v1_relat_1(X1) != iProver_top ),
% 27.77/4.02      inference(light_normalisation,[status(thm)],[c_5670,c_10]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_5994,plain,
% 27.77/4.02      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_1086,c_5673]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_3935,plain,
% 27.77/4.02      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_1086,c_3930]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_5997,plain,
% 27.77/4.02      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 27.77/4.02      inference(demodulation,[status(thm)],[c_5994,c_10,c_3935]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_6006,plain,
% 27.77/4.02      ( k7_relat_1(k6_relat_1(k1_relat_1(sK3)),k1_relat_1(sK2)) = k7_relat_1(k6_relat_1(k1_relat_1(sK3)),sK1) ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_3734,c_5997]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_22,plain,
% 27.77/4.02      ( ~ r2_hidden(X0,k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X2)))
% 27.77/4.02      | ~ v1_funct_1(X1)
% 27.77/4.02      | ~ v1_relat_1(X1)
% 27.77/4.02      | k1_funct_1(k5_relat_1(k6_relat_1(X2),X1),X0) = k1_funct_1(X1,X0) ),
% 27.77/4.02      inference(cnf_transformation,[],[f95]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_1084,plain,
% 27.77/4.02      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,X2)
% 27.77/4.02      | r2_hidden(X2,k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) != iProver_top
% 27.77/4.02      | v1_funct_1(X1) != iProver_top
% 27.77/4.02      | v1_relat_1(X1) != iProver_top ),
% 27.77/4.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_3720,plain,
% 27.77/4.02      ( k1_funct_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k1_funct_1(X1,X2)
% 27.77/4.02      | r2_hidden(X2,k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(X1)),X0))) != iProver_top
% 27.77/4.02      | v1_funct_1(X1) != iProver_top
% 27.77/4.02      | v1_relat_1(X1) != iProver_top ),
% 27.77/4.02      inference(demodulation,[status(thm)],[c_3644,c_1084]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_41902,plain,
% 27.77/4.02      ( k1_funct_1(k5_relat_1(k6_relat_1(k1_relat_1(sK2)),sK3),X0) = k1_funct_1(sK3,X0)
% 27.77/4.02      | r2_hidden(X0,k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(sK3)),sK1))) != iProver_top
% 27.77/4.02      | v1_funct_1(sK3) != iProver_top
% 27.77/4.02      | v1_relat_1(sK3) != iProver_top ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_6006,c_3720]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_3740,plain,
% 27.77/4.02      ( k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(sK3)),sK1)) = k1_relat_1(sK2) ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_3732,c_1564]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_3432,plain,
% 27.77/4.02      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK3,k1_relat_1(k6_relat_1(X0)))))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(k6_relat_1(X0)))) ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_1086,c_3428]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_3436,plain,
% 27.77/4.02      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK3,X0)))) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 27.77/4.02      inference(light_normalisation,[status(thm)],[c_3432,c_10]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_13,plain,
% 27.77/4.02      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
% 27.77/4.02      | ~ v1_relat_1(X0) ),
% 27.77/4.02      inference(cnf_transformation,[],[f71]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_1092,plain,
% 27.77/4.02      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 27.77/4.02      | v1_relat_1(X0) != iProver_top ),
% 27.77/4.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_2199,plain,
% 27.77/4.02      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top
% 27.77/4.02      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_10,c_1092]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_54,plain,
% 27.77/4.02      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 27.77/4.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_2639,plain,
% 27.77/4.02      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) = iProver_top ),
% 27.77/4.02      inference(global_propositional_subsumption,
% 27.77/4.02                [status(thm)],
% 27.77/4.02                [c_2199,c_54]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_3902,plain,
% 27.77/4.02      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) = iProver_top ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_3436,c_2639]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_9,plain,
% 27.77/4.02      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 27.77/4.02      inference(cnf_transformation,[],[f68]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_8,plain,
% 27.77/4.02      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(k7_relat_1(X1,X2)))
% 27.77/4.02      | ~ v1_relat_1(X1)
% 27.77/4.02      | ~ v1_relat_1(X0)
% 27.77/4.02      | k5_relat_1(X0,k7_relat_1(X1,X2)) = k5_relat_1(X0,X1) ),
% 27.77/4.02      inference(cnf_transformation,[],[f66]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_1095,plain,
% 27.77/4.02      ( k5_relat_1(X0,k7_relat_1(X1,X2)) = k5_relat_1(X0,X1)
% 27.77/4.02      | r1_tarski(k2_relat_1(X0),k1_relat_1(k7_relat_1(X1,X2))) != iProver_top
% 27.77/4.02      | v1_relat_1(X0) != iProver_top
% 27.77/4.02      | v1_relat_1(X1) != iProver_top ),
% 27.77/4.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_4607,plain,
% 27.77/4.02      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(X1,X2)) = k5_relat_1(k6_relat_1(X0),X1)
% 27.77/4.02      | r1_tarski(X0,k1_relat_1(k7_relat_1(X1,X2))) != iProver_top
% 27.77/4.02      | v1_relat_1(X1) != iProver_top
% 27.77/4.02      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_9,c_1095]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_6924,plain,
% 27.77/4.02      ( v1_relat_1(X1) != iProver_top
% 27.77/4.02      | r1_tarski(X0,k1_relat_1(k7_relat_1(X1,X2))) != iProver_top
% 27.77/4.02      | k5_relat_1(k6_relat_1(X0),k7_relat_1(X1,X2)) = k5_relat_1(k6_relat_1(X0),X1) ),
% 27.77/4.02      inference(global_propositional_subsumption,
% 27.77/4.02                [status(thm)],
% 27.77/4.02                [c_4607,c_54]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_6925,plain,
% 27.77/4.02      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(X1,X2)) = k5_relat_1(k6_relat_1(X0),X1)
% 27.77/4.02      | r1_tarski(X0,k1_relat_1(k7_relat_1(X1,X2))) != iProver_top
% 27.77/4.02      | v1_relat_1(X1) != iProver_top ),
% 27.77/4.02      inference(renaming,[status(thm)],[c_6924]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_6942,plain,
% 27.77/4.02      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(sK3,k1_relat_1(sK2))) = k5_relat_1(k6_relat_1(X0),sK3)
% 27.77/4.02      | r1_tarski(X0,k1_relat_1(k7_relat_1(sK3,sK1))) != iProver_top
% 27.77/4.02      | v1_relat_1(sK3) != iProver_top ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_4227,c_6925]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_6973,plain,
% 27.77/4.02      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(sK3,sK1)) = k5_relat_1(k6_relat_1(X0),sK3)
% 27.77/4.02      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 27.77/4.02      | v1_relat_1(sK3) != iProver_top ),
% 27.77/4.02      inference(light_normalisation,[status(thm)],[c_6942,c_4227,c_4658]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_18754,plain,
% 27.77/4.02      ( r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 27.77/4.02      | k5_relat_1(k6_relat_1(X0),k7_relat_1(sK3,sK1)) = k5_relat_1(k6_relat_1(X0),sK3) ),
% 27.77/4.02      inference(global_propositional_subsumption,
% 27.77/4.02                [status(thm)],
% 27.77/4.02                [c_6973,c_34]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_18755,plain,
% 27.77/4.02      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(sK3,sK1)) = k5_relat_1(k6_relat_1(X0),sK3)
% 27.77/4.02      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
% 27.77/4.02      inference(renaming,[status(thm)],[c_18754]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_18764,plain,
% 27.77/4.02      ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2)))),k7_relat_1(sK3,sK1)) = k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK2)))),sK3) ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_3902,c_18755]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_4219,plain,
% 27.77/4.02      ( v1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),X1)) = iProver_top
% 27.77/4.02      | v1_relat_1(sK3) != iProver_top ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_3936,c_1099]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_7674,plain,
% 27.77/4.02      ( v1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),X1)) = iProver_top ),
% 27.77/4.02      inference(global_propositional_subsumption,
% 27.77/4.02                [status(thm)],
% 27.77/4.02                [c_4219,c_34]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_7680,plain,
% 27.77/4.02      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_2207,c_7674]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_11,plain,
% 27.77/4.02      ( ~ v1_relat_1(X0)
% 27.77/4.02      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ),
% 27.77/4.02      inference(cnf_transformation,[],[f69]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_1094,plain,
% 27.77/4.02      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
% 27.77/4.02      | v1_relat_1(X0) != iProver_top ),
% 27.77/4.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_7725,plain,
% 27.77/4.02      ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(sK3,X0))),k7_relat_1(sK3,X0)) = k7_relat_1(sK3,X0) ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_7680,c_1094]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_11371,plain,
% 27.77/4.02      ( k5_relat_1(k6_relat_1(k1_relat_1(sK2)),k7_relat_1(sK3,sK1)) = k7_relat_1(sK3,sK1) ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_4658,c_7725]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_18769,plain,
% 27.77/4.02      ( k5_relat_1(k6_relat_1(k1_relat_1(sK2)),sK3) = k7_relat_1(sK3,sK1) ),
% 27.77/4.02      inference(light_normalisation,
% 27.77/4.02                [status(thm)],
% 27.77/4.02                [c_18764,c_4227,c_4658,c_11371]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_41984,plain,
% 27.77/4.02      ( k1_funct_1(k7_relat_1(sK3,sK1),X0) = k1_funct_1(sK3,X0)
% 27.77/4.02      | r2_hidden(X0,k1_relat_1(sK2)) != iProver_top
% 27.77/4.02      | v1_funct_1(sK3) != iProver_top
% 27.77/4.02      | v1_relat_1(sK3) != iProver_top ),
% 27.77/4.02      inference(light_normalisation,
% 27.77/4.02                [status(thm)],
% 27.77/4.02                [c_41902,c_3740,c_18769]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_43153,plain,
% 27.77/4.02      ( k1_funct_1(k7_relat_1(sK3,sK1),X0) = k1_funct_1(sK3,X0)
% 27.77/4.02      | r2_hidden(X0,k1_relat_1(sK2)) != iProver_top ),
% 27.77/4.02      inference(global_propositional_subsumption,
% 27.77/4.02                [status(thm)],
% 27.77/4.02                [c_41984,c_34,c_35]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_43159,plain,
% 27.77/4.02      ( k1_funct_1(k7_relat_1(sK3,sK1),sK0(sK2,k7_relat_1(sK3,sK1))) = k1_funct_1(sK3,sK0(sK2,k7_relat_1(sK3,sK1))) ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_35707,c_43153]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_23,plain,
% 27.77/4.02      ( ~ v1_funct_1(X0)
% 27.77/4.02      | ~ v1_funct_1(X1)
% 27.77/4.02      | ~ v1_relat_1(X0)
% 27.77/4.02      | ~ v1_relat_1(X1)
% 27.77/4.02      | X1 = X0
% 27.77/4.02      | k1_funct_1(X1,sK0(X0,X1)) != k1_funct_1(X0,sK0(X0,X1))
% 27.77/4.02      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 27.77/4.02      inference(cnf_transformation,[],[f82]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_1083,plain,
% 27.77/4.02      ( X0 = X1
% 27.77/4.02      | k1_funct_1(X0,sK0(X1,X0)) != k1_funct_1(X1,sK0(X1,X0))
% 27.77/4.02      | k1_relat_1(X1) != k1_relat_1(X0)
% 27.77/4.02      | v1_funct_1(X1) != iProver_top
% 27.77/4.02      | v1_funct_1(X0) != iProver_top
% 27.77/4.02      | v1_relat_1(X1) != iProver_top
% 27.77/4.02      | v1_relat_1(X0) != iProver_top ),
% 27.77/4.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_105969,plain,
% 27.77/4.02      ( k1_funct_1(sK3,sK0(sK2,k7_relat_1(sK3,sK1))) != k1_funct_1(sK2,sK0(sK2,k7_relat_1(sK3,sK1)))
% 27.77/4.02      | k7_relat_1(sK3,sK1) = sK2
% 27.77/4.02      | k1_relat_1(k7_relat_1(sK3,sK1)) != k1_relat_1(sK2)
% 27.77/4.02      | v1_funct_1(k7_relat_1(sK3,sK1)) != iProver_top
% 27.77/4.02      | v1_funct_1(sK2) != iProver_top
% 27.77/4.02      | v1_relat_1(k7_relat_1(sK3,sK1)) != iProver_top
% 27.77/4.02      | v1_relat_1(sK2) != iProver_top ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_43159,c_1083]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_26,negated_conjecture,
% 27.77/4.02      ( ~ r2_hidden(X0,k1_relat_1(sK2))
% 27.77/4.02      | k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0) ),
% 27.77/4.02      inference(cnf_transformation,[],[f88]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_1081,plain,
% 27.77/4.02      ( k1_funct_1(sK2,X0) = k1_funct_1(sK3,X0)
% 27.77/4.02      | r2_hidden(X0,k1_relat_1(sK2)) != iProver_top ),
% 27.77/4.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_35716,plain,
% 27.77/4.02      ( k1_funct_1(sK3,sK0(sK2,k7_relat_1(sK3,sK1))) = k1_funct_1(sK2,sK0(sK2,k7_relat_1(sK3,sK1))) ),
% 27.77/4.02      inference(superposition,[status(thm)],[c_35707,c_1081]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_105970,plain,
% 27.77/4.02      ( k1_funct_1(sK3,sK0(sK2,k7_relat_1(sK3,sK1))) != k1_funct_1(sK3,sK0(sK2,k7_relat_1(sK3,sK1)))
% 27.77/4.02      | k7_relat_1(sK3,sK1) = sK2
% 27.77/4.02      | k1_relat_1(sK2) != k1_relat_1(sK2)
% 27.77/4.02      | v1_funct_1(k7_relat_1(sK3,sK1)) != iProver_top
% 27.77/4.02      | v1_funct_1(sK2) != iProver_top
% 27.77/4.02      | v1_relat_1(k7_relat_1(sK3,sK1)) != iProver_top
% 27.77/4.02      | v1_relat_1(sK2) != iProver_top ),
% 27.77/4.02      inference(light_normalisation,
% 27.77/4.02                [status(thm)],
% 27.77/4.02                [c_105969,c_4658,c_35716]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(c_105971,plain,
% 27.77/4.02      ( k7_relat_1(sK3,sK1) = sK2
% 27.77/4.02      | v1_funct_1(k7_relat_1(sK3,sK1)) != iProver_top
% 27.77/4.02      | v1_funct_1(sK2) != iProver_top
% 27.77/4.02      | v1_relat_1(k7_relat_1(sK3,sK1)) != iProver_top
% 27.77/4.02      | v1_relat_1(sK2) != iProver_top ),
% 27.77/4.02      inference(equality_resolution_simp,[status(thm)],[c_105970]) ).
% 27.77/4.02  
% 27.77/4.02  cnf(contradiction,plain,
% 27.77/4.02      ( $false ),
% 27.77/4.02      inference(minisat,
% 27.77/4.02                [status(thm)],
% 27.77/4.02                [c_105971,c_1209,c_1154,c_25,c_35,c_34,c_33,c_32]) ).
% 27.77/4.02  
% 27.77/4.02  
% 27.77/4.02  % SZS output end CNFRefutation for theBenchmark.p
% 27.77/4.02  
% 27.77/4.02  ------                               Statistics
% 27.77/4.02  
% 27.77/4.02  ------ General
% 27.77/4.02  
% 27.77/4.02  abstr_ref_over_cycles:                  0
% 27.77/4.02  abstr_ref_under_cycles:                 0
% 27.77/4.02  gc_basic_clause_elim:                   0
% 27.77/4.02  forced_gc_time:                         0
% 27.77/4.02  parsing_time:                           0.008
% 27.77/4.02  unif_index_cands_time:                  0.
% 27.77/4.02  unif_index_add_time:                    0.
% 27.77/4.02  orderings_time:                         0.
% 27.77/4.02  out_proof_time:                         0.023
% 27.77/4.02  total_time:                             3.408
% 27.77/4.02  num_of_symbols:                         47
% 27.77/4.02  num_of_terms:                           128779
% 27.77/4.02  
% 27.77/4.02  ------ Preprocessing
% 27.77/4.02  
% 27.77/4.02  num_of_splits:                          0
% 27.77/4.02  num_of_split_atoms:                     0
% 27.77/4.02  num_of_reused_defs:                     0
% 27.77/4.02  num_eq_ax_congr_red:                    6
% 27.77/4.02  num_of_sem_filtered_clauses:            1
% 27.77/4.02  num_of_subtypes:                        0
% 27.77/4.02  monotx_restored_types:                  0
% 27.77/4.02  sat_num_of_epr_types:                   0
% 27.77/4.02  sat_num_of_non_cyclic_types:            0
% 27.77/4.02  sat_guarded_non_collapsed_types:        0
% 27.77/4.02  num_pure_diseq_elim:                    0
% 27.77/4.02  simp_replaced_by:                       0
% 27.77/4.02  res_preprocessed:                       149
% 27.77/4.02  prep_upred:                             0
% 27.77/4.02  prep_unflattend:                        4
% 27.77/4.02  smt_new_axioms:                         0
% 27.77/4.02  pred_elim_cands:                        4
% 27.77/4.02  pred_elim:                              0
% 27.77/4.02  pred_elim_cl:                           0
% 27.77/4.02  pred_elim_cycles:                       2
% 27.77/4.02  merged_defs:                            0
% 27.77/4.02  merged_defs_ncl:                        0
% 27.77/4.02  bin_hyper_res:                          0
% 27.77/4.02  prep_cycles:                            4
% 27.77/4.02  pred_elim_time:                         0.004
% 27.77/4.02  splitting_time:                         0.
% 27.77/4.02  sem_filter_time:                        0.
% 27.77/4.02  monotx_time:                            0.
% 27.77/4.02  subtype_inf_time:                       0.
% 27.77/4.02  
% 27.77/4.02  ------ Problem properties
% 27.77/4.02  
% 27.77/4.02  clauses:                                30
% 27.77/4.02  conjectures:                            7
% 27.77/4.02  epr:                                    6
% 27.77/4.02  horn:                                   29
% 27.77/4.02  ground:                                 6
% 27.77/4.02  unary:                                  12
% 27.77/4.02  binary:                                 9
% 27.77/4.02  lits:                                   67
% 27.77/4.02  lits_eq:                                22
% 27.77/4.02  fd_pure:                                0
% 27.77/4.02  fd_pseudo:                              0
% 27.77/4.02  fd_cond:                                0
% 27.77/4.02  fd_pseudo_cond:                         3
% 27.77/4.02  ac_symbols:                             0
% 27.77/4.02  
% 27.77/4.02  ------ Propositional Solver
% 27.77/4.02  
% 27.77/4.02  prop_solver_calls:                      35
% 27.77/4.02  prop_fast_solver_calls:                 2041
% 27.77/4.02  smt_solver_calls:                       0
% 27.77/4.02  smt_fast_solver_calls:                  0
% 27.77/4.02  prop_num_of_clauses:                    32615
% 27.77/4.02  prop_preprocess_simplified:             41993
% 27.77/4.02  prop_fo_subsumed:                       101
% 27.77/4.02  prop_solver_time:                       0.
% 27.77/4.02  smt_solver_time:                        0.
% 27.77/4.02  smt_fast_solver_time:                   0.
% 27.77/4.02  prop_fast_solver_time:                  0.
% 27.77/4.02  prop_unsat_core_time:                   0.004
% 27.77/4.02  
% 27.77/4.02  ------ QBF
% 27.77/4.02  
% 27.77/4.02  qbf_q_res:                              0
% 27.77/4.02  qbf_num_tautologies:                    0
% 27.77/4.02  qbf_prep_cycles:                        0
% 27.77/4.02  
% 27.77/4.02  ------ BMC1
% 27.77/4.02  
% 27.77/4.02  bmc1_current_bound:                     -1
% 27.77/4.02  bmc1_last_solved_bound:                 -1
% 27.77/4.02  bmc1_unsat_core_size:                   -1
% 27.77/4.02  bmc1_unsat_core_parents_size:           -1
% 27.77/4.02  bmc1_merge_next_fun:                    0
% 27.77/4.02  bmc1_unsat_core_clauses_time:           0.
% 27.77/4.02  
% 27.77/4.02  ------ Instantiation
% 27.77/4.02  
% 27.77/4.02  inst_num_of_clauses:                    8335
% 27.77/4.02  inst_num_in_passive:                    3650
% 27.77/4.02  inst_num_in_active:                     2175
% 27.77/4.02  inst_num_in_unprocessed:                2510
% 27.77/4.02  inst_num_of_loops:                      2630
% 27.77/4.02  inst_num_of_learning_restarts:          0
% 27.77/4.02  inst_num_moves_active_passive:          452
% 27.77/4.02  inst_lit_activity:                      0
% 27.77/4.02  inst_lit_activity_moves:                1
% 27.77/4.02  inst_num_tautologies:                   0
% 27.77/4.02  inst_num_prop_implied:                  0
% 27.77/4.02  inst_num_existing_simplified:           0
% 27.77/4.02  inst_num_eq_res_simplified:             0
% 27.77/4.02  inst_num_child_elim:                    0
% 27.77/4.02  inst_num_of_dismatching_blockings:      6288
% 27.77/4.02  inst_num_of_non_proper_insts:           10650
% 27.77/4.02  inst_num_of_duplicates:                 0
% 27.77/4.02  inst_inst_num_from_inst_to_res:         0
% 27.77/4.02  inst_dismatching_checking_time:         0.
% 27.77/4.02  
% 27.77/4.02  ------ Resolution
% 27.77/4.02  
% 27.77/4.02  res_num_of_clauses:                     0
% 27.77/4.02  res_num_in_passive:                     0
% 27.77/4.02  res_num_in_active:                      0
% 27.77/4.02  res_num_of_loops:                       153
% 27.77/4.02  res_forward_subset_subsumed:            2400
% 27.77/4.02  res_backward_subset_subsumed:           0
% 27.77/4.02  res_forward_subsumed:                   0
% 27.77/4.02  res_backward_subsumed:                  0
% 27.77/4.02  res_forward_subsumption_resolution:     0
% 27.77/4.02  res_backward_subsumption_resolution:    0
% 27.77/4.02  res_clause_to_clause_subsumption:       22266
% 27.77/4.02  res_orphan_elimination:                 0
% 27.77/4.02  res_tautology_del:                      573
% 27.77/4.02  res_num_eq_res_simplified:              0
% 27.77/4.02  res_num_sel_changes:                    0
% 27.77/4.02  res_moves_from_active_to_pass:          0
% 27.77/4.02  
% 27.77/4.02  ------ Superposition
% 27.77/4.02  
% 27.77/4.02  sup_time_total:                         0.
% 27.77/4.02  sup_time_generating:                    0.
% 27.77/4.02  sup_time_sim_full:                      0.
% 27.77/4.02  sup_time_sim_immed:                     0.
% 27.77/4.02  
% 27.77/4.02  sup_num_of_clauses:                     5002
% 27.77/4.02  sup_num_in_active:                      485
% 27.77/4.02  sup_num_in_passive:                     4517
% 27.77/4.02  sup_num_of_loops:                       525
% 27.77/4.02  sup_fw_superposition:                   12427
% 27.77/4.02  sup_bw_superposition:                   11949
% 27.77/4.02  sup_immediate_simplified:               17010
% 27.77/4.02  sup_given_eliminated:                   4
% 27.77/4.02  comparisons_done:                       0
% 27.77/4.02  comparisons_avoided:                    48
% 27.77/4.02  
% 27.77/4.02  ------ Simplifications
% 27.77/4.02  
% 27.77/4.02  
% 27.77/4.02  sim_fw_subset_subsumed:                 365
% 27.77/4.02  sim_bw_subset_subsumed:                 172
% 27.77/4.02  sim_fw_subsumed:                        1433
% 27.77/4.02  sim_bw_subsumed:                        34
% 27.77/4.02  sim_fw_subsumption_res:                 0
% 27.77/4.02  sim_bw_subsumption_res:                 0
% 27.77/4.02  sim_tautology_del:                      140
% 27.77/4.02  sim_eq_tautology_del:                   4240
% 27.77/4.02  sim_eq_res_simp:                        1
% 27.77/4.02  sim_fw_demodulated:                     9309
% 27.77/4.02  sim_bw_demodulated:                     124
% 27.77/4.02  sim_light_normalised:                   10241
% 27.77/4.02  sim_joinable_taut:                      0
% 27.77/4.02  sim_joinable_simp:                      0
% 27.77/4.02  sim_ac_normalised:                      0
% 27.77/4.02  sim_smt_subsumption:                    0
% 27.77/4.02  
%------------------------------------------------------------------------------
