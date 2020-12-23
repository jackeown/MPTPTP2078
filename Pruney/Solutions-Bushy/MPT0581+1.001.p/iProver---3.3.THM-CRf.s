%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0581+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:39 EST 2020

% Result     : Theorem 0.81s
% Output     : CNFRefutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :   36 (  72 expanded)
%              Number of clauses        :   20 (  21 expanded)
%              Number of leaves         :    5 (  22 expanded)
%              Depth                    :   14
%              Number of atoms          :   83 ( 287 expanded)
%              Number of equality atoms :   58 ( 194 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2,X3] :
              ( ( k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                & k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
             => k7_relat_1(X0,k2_xboole_0(X2,X3)) = k7_relat_1(X1,k2_xboole_0(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2,X3] :
                ( ( k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                  & k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
               => k7_relat_1(X0,k2_xboole_0(X2,X3)) = k7_relat_1(X1,k2_xboole_0(X2,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( k7_relat_1(X0,k2_xboole_0(X2,X3)) != k7_relat_1(X1,k2_xboole_0(X2,X3))
              & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
              & k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( k7_relat_1(X0,k2_xboole_0(X2,X3)) != k7_relat_1(X1,k2_xboole_0(X2,X3))
              & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
              & k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f5])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( k7_relat_1(X0,k2_xboole_0(X2,X3)) != k7_relat_1(X1,k2_xboole_0(X2,X3))
          & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
          & k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
     => ( k7_relat_1(X0,k2_xboole_0(sK2,sK3)) != k7_relat_1(X1,k2_xboole_0(sK2,sK3))
        & k7_relat_1(X0,sK3) = k7_relat_1(X1,sK3)
        & k7_relat_1(X0,sK2) = k7_relat_1(X1,sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( k7_relat_1(X0,k2_xboole_0(X2,X3)) != k7_relat_1(X1,k2_xboole_0(X2,X3))
              & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
              & k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
          & v1_relat_1(X1) )
     => ( ? [X3,X2] :
            ( k7_relat_1(sK1,k2_xboole_0(X2,X3)) != k7_relat_1(X0,k2_xboole_0(X2,X3))
            & k7_relat_1(sK1,X3) = k7_relat_1(X0,X3)
            & k7_relat_1(sK1,X2) = k7_relat_1(X0,X2) )
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( k7_relat_1(X0,k2_xboole_0(X2,X3)) != k7_relat_1(X1,k2_xboole_0(X2,X3))
                & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                & k7_relat_1(X0,X2) = k7_relat_1(X1,X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( k7_relat_1(sK0,k2_xboole_0(X2,X3)) != k7_relat_1(X1,k2_xboole_0(X2,X3))
              & k7_relat_1(sK0,X3) = k7_relat_1(X1,X3)
              & k7_relat_1(sK0,X2) = k7_relat_1(X1,X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( k7_relat_1(sK0,k2_xboole_0(sK2,sK3)) != k7_relat_1(sK1,k2_xboole_0(sK2,sK3))
    & k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3)
    & k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f9,f8,f7])).

fof(f15,plain,(
    k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f14,plain,(
    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f12,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f16,plain,(
    k7_relat_1(sK0,k2_xboole_0(sK2,sK3)) != k7_relat_1(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_2,negated_conjecture,
    ( k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_60,negated_conjecture,
    ( k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3,negated_conjecture,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_59,negated_conjecture,
    ( k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_4,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_39,plain,
    ( k2_xboole_0(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k2_xboole_0(X1,X2))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_40,plain,
    ( k2_xboole_0(k7_relat_1(sK1,X0),k7_relat_1(sK1,X1)) = k7_relat_1(sK1,k2_xboole_0(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_39])).

cnf(c_58,plain,
    ( k2_xboole_0(k7_relat_1(sK1,X0_35),k7_relat_1(sK1,X1_35)) = k7_relat_1(sK1,k2_xboole_0(X0_35,X1_35)) ),
    inference(subtyping,[status(esa)],[c_40])).

cnf(c_72,plain,
    ( k2_xboole_0(k7_relat_1(sK0,sK2),k7_relat_1(sK1,X0_35)) = k7_relat_1(sK1,k2_xboole_0(sK2,X0_35)) ),
    inference(superposition,[status(thm)],[c_59,c_58])).

cnf(c_81,plain,
    ( k2_xboole_0(k7_relat_1(sK0,sK2),k7_relat_1(sK0,sK3)) = k7_relat_1(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_60,c_72])).

cnf(c_5,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_45,plain,
    ( k2_xboole_0(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k2_xboole_0(X1,X2))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_5])).

cnf(c_46,plain,
    ( k2_xboole_0(k7_relat_1(sK0,X0),k7_relat_1(sK0,X1)) = k7_relat_1(sK0,k2_xboole_0(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_45])).

cnf(c_57,plain,
    ( k2_xboole_0(k7_relat_1(sK0,X0_35),k7_relat_1(sK0,X1_35)) = k7_relat_1(sK0,k2_xboole_0(X0_35,X1_35)) ),
    inference(subtyping,[status(esa)],[c_46])).

cnf(c_84,plain,
    ( k7_relat_1(sK1,k2_xboole_0(sK2,sK3)) = k7_relat_1(sK0,k2_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_81,c_57])).

cnf(c_1,negated_conjecture,
    ( k7_relat_1(sK0,k2_xboole_0(sK2,sK3)) != k7_relat_1(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_61,negated_conjecture,
    ( k7_relat_1(sK0,k2_xboole_0(sK2,sK3)) != k7_relat_1(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_121,plain,
    ( k7_relat_1(sK0,k2_xboole_0(sK2,sK3)) != k7_relat_1(sK0,k2_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_84,c_61])).

cnf(c_132,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_121])).


%------------------------------------------------------------------------------
