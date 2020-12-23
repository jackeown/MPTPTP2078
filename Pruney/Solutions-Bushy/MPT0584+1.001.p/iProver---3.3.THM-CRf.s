%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0584+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:39 EST 2020

% Result     : Theorem 1.24s
% Output     : CNFRefutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 106 expanded)
%              Number of clauses        :   28 (  36 expanded)
%              Number of leaves         :    7 (  30 expanded)
%              Depth                    :   17
%              Number of atoms          :  102 ( 374 expanded)
%              Number of equality atoms :   60 ( 187 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2,X3] :
              ( ( k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                & r1_tarski(X2,X3) )
             => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2,X3] :
                ( ( k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                  & r1_tarski(X2,X3) )
               => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
              & r1_tarski(X2,X3) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
              & r1_tarski(X2,X3) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
          & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
          & r1_tarski(X2,X3) )
     => ( k7_relat_1(X0,sK2) != k7_relat_1(X1,sK2)
        & k7_relat_1(X0,sK3) = k7_relat_1(X1,sK3)
        & r1_tarski(sK2,sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
              & r1_tarski(X2,X3) )
          & v1_relat_1(X1) )
     => ( ? [X3,X2] :
            ( k7_relat_1(sK1,X2) != k7_relat_1(X0,X2)
            & k7_relat_1(sK1,X3) = k7_relat_1(X0,X3)
            & r1_tarski(X2,X3) )
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
                & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                & r1_tarski(X2,X3) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( k7_relat_1(sK0,X2) != k7_relat_1(X1,X2)
              & k7_relat_1(sK0,X3) = k7_relat_1(X1,X3)
              & r1_tarski(X2,X3) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2)
    & k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f12,f11,f10])).

fof(f19,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f20,plain,(
    k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f18,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f17,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f21,plain,(
    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_90,plain,
    ( k3_xboole_0(X0_37,X1_37) = k3_xboole_0(X1_37,X0_37) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_5,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_61,plain,
    ( k3_xboole_0(X0,X1) = X0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_5])).

cnf(c_62,plain,
    ( k3_xboole_0(sK2,sK3) = sK2 ),
    inference(unflattening,[status(thm)],[c_61])).

cnf(c_87,plain,
    ( k3_xboole_0(sK2,sK3) = sK2 ),
    inference(subtyping,[status(esa)],[c_62])).

cnf(c_4,negated_conjecture,
    ( k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_88,negated_conjecture,
    ( k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_6,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_67,plain,
    ( k7_relat_1(X0,k3_xboole_0(X1,X2)) = k7_relat_1(k7_relat_1(X0,X1),X2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_6])).

cnf(c_68,plain,
    ( k7_relat_1(sK1,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(sK1,X0),X1) ),
    inference(unflattening,[status(thm)],[c_67])).

cnf(c_86,plain,
    ( k7_relat_1(sK1,k3_xboole_0(X0_37,X1_37)) = k7_relat_1(k7_relat_1(sK1,X0_37),X1_37) ),
    inference(subtyping,[status(esa)],[c_68])).

cnf(c_104,plain,
    ( k7_relat_1(sK1,k3_xboole_0(sK3,X0_37)) = k7_relat_1(k7_relat_1(sK0,sK3),X0_37) ),
    inference(superposition,[status(thm)],[c_88,c_86])).

cnf(c_7,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_73,plain,
    ( k7_relat_1(X0,k3_xboole_0(X1,X2)) = k7_relat_1(k7_relat_1(X0,X1),X2)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_7])).

cnf(c_74,plain,
    ( k7_relat_1(sK0,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(sK0,X0),X1) ),
    inference(unflattening,[status(thm)],[c_73])).

cnf(c_85,plain,
    ( k7_relat_1(sK0,k3_xboole_0(X0_37,X1_37)) = k7_relat_1(k7_relat_1(sK0,X0_37),X1_37) ),
    inference(subtyping,[status(esa)],[c_74])).

cnf(c_105,plain,
    ( k7_relat_1(sK0,k3_xboole_0(sK3,X0_37)) = k7_relat_1(sK1,k3_xboole_0(sK3,X0_37)) ),
    inference(demodulation,[status(thm)],[c_104,c_85])).

cnf(c_131,plain,
    ( k7_relat_1(sK1,k3_xboole_0(X0_37,sK3)) = k7_relat_1(sK0,k3_xboole_0(sK3,X0_37)) ),
    inference(superposition,[status(thm)],[c_90,c_105])).

cnf(c_142,plain,
    ( k7_relat_1(sK0,k3_xboole_0(sK3,sK2)) = k7_relat_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_87,c_131])).

cnf(c_181,plain,
    ( k7_relat_1(sK0,k3_xboole_0(sK2,sK3)) = k7_relat_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_90,c_142])).

cnf(c_185,plain,
    ( k7_relat_1(sK1,sK2) = k7_relat_1(sK0,sK2) ),
    inference(light_normalisation,[status(thm)],[c_181,c_87])).

cnf(c_3,negated_conjecture,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_89,negated_conjecture,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_188,plain,
    ( k7_relat_1(sK0,sK2) != k7_relat_1(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_185,c_89])).

cnf(c_189,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_188])).


%------------------------------------------------------------------------------
