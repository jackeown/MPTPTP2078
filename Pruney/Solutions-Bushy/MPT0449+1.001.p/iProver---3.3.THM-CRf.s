%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0449+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:19 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 201 expanded)
%              Number of clauses        :   38 (  73 expanded)
%              Number of leaves         :    9 (  53 expanded)
%              Depth                    :   16
%              Number of atoms          :  123 ( 483 expanded)
%              Number of equality atoms :   69 ( 217 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k3_relat_1(X0),k3_relat_1(X1)) = k3_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k2_xboole_0(k3_relat_1(X0),k3_relat_1(X1)) = k3_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_xboole_0(k3_relat_1(X0),k3_relat_1(X1)) != k3_relat_1(k2_xboole_0(X0,X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_xboole_0(k3_relat_1(X0),k3_relat_1(X1)) != k3_relat_1(k2_xboole_0(X0,X1))
          & v1_relat_1(X1) )
     => ( k2_xboole_0(k3_relat_1(X0),k3_relat_1(sK1)) != k3_relat_1(k2_xboole_0(X0,sK1))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_xboole_0(k3_relat_1(X0),k3_relat_1(X1)) != k3_relat_1(k2_xboole_0(X0,X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)) != k3_relat_1(k2_xboole_0(sK0,X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( k2_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)) != k3_relat_1(k2_xboole_0(sK0,sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16,f15])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
    k2_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)) != k3_relat_1(k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_7,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_190,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_189,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_191,plain,
    ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_415,plain,
    ( k2_xboole_0(k2_relat_1(sK0),k2_relat_1(X0)) = k2_relat_1(k2_xboole_0(sK0,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_189,c_191])).

cnf(c_1066,plain,
    ( k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) = k2_relat_1(k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_190,c_415])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_194,plain,
    ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_432,plain,
    ( k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) = k3_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_189,c_194])).

cnf(c_5,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_235,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_835,plain,
    ( k2_xboole_0(k1_relat_1(sK0),k2_xboole_0(k2_relat_1(sK0),X0)) = k2_xboole_0(X0,k3_relat_1(sK0)) ),
    inference(superposition,[status(thm)],[c_432,c_235])).

cnf(c_3814,plain,
    ( k2_xboole_0(k1_relat_1(sK0),k2_relat_1(k2_xboole_0(sK0,sK1))) = k2_xboole_0(k2_relat_1(sK1),k3_relat_1(sK0)) ),
    inference(superposition,[status(thm)],[c_1066,c_835])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_192,plain,
    ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_544,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(X0)) = k1_relat_1(k2_xboole_0(sK1,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_190,c_192])).

cnf(c_1901,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_189,c_544])).

cnf(c_2067,plain,
    ( k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_1901,c_0])).

cnf(c_545,plain,
    ( k2_xboole_0(k1_relat_1(sK0),k1_relat_1(X0)) = k1_relat_1(k2_xboole_0(sK0,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_189,c_192])).

cnf(c_2121,plain,
    ( k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) = k1_relat_1(k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_190,c_545])).

cnf(c_2414,plain,
    ( k1_relat_1(k2_xboole_0(sK1,sK0)) = k1_relat_1(k2_xboole_0(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_2067,c_2121])).

cnf(c_2416,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) = k1_relat_1(k2_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_2414,c_1901])).

cnf(c_3202,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k2_xboole_0(k1_relat_1(sK0),X0)) = k2_xboole_0(k1_relat_1(k2_xboole_0(sK0,sK1)),X0) ),
    inference(superposition,[status(thm)],[c_2416,c_5])).

cnf(c_7950,plain,
    ( k2_xboole_0(k1_relat_1(k2_xboole_0(sK0,sK1)),k2_relat_1(k2_xboole_0(sK0,sK1))) = k2_xboole_0(k1_relat_1(sK1),k2_xboole_0(k2_relat_1(sK1),k3_relat_1(sK0))) ),
    inference(superposition,[status(thm)],[c_3814,c_3202])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_193,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_486,plain,
    ( k2_xboole_0(k1_relat_1(k2_xboole_0(X0,X1)),k2_relat_1(k2_xboole_0(X0,X1))) = k3_relat_1(k2_xboole_0(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_193,c_194])).

cnf(c_6401,plain,
    ( k2_xboole_0(k1_relat_1(k2_xboole_0(sK0,X0)),k2_relat_1(k2_xboole_0(sK0,X0))) = k3_relat_1(k2_xboole_0(sK0,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_189,c_486])).

cnf(c_7480,plain,
    ( k2_xboole_0(k1_relat_1(k2_xboole_0(sK0,sK1)),k2_relat_1(k2_xboole_0(sK0,sK1))) = k3_relat_1(k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_190,c_6401])).

cnf(c_7957,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k2_xboole_0(k2_relat_1(sK1),k3_relat_1(sK0))) = k3_relat_1(k2_xboole_0(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_7950,c_7480])).

cnf(c_431,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) = k3_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_190,c_194])).

cnf(c_723,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k2_xboole_0(k2_relat_1(sK1),X0)) = k2_xboole_0(X0,k3_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_431,c_235])).

cnf(c_14119,plain,
    ( k2_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)) = k3_relat_1(k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_7957,c_723])).

cnf(c_6,negated_conjecture,
    ( k2_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)) != k3_relat_1(k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14119,c_6])).


%------------------------------------------------------------------------------
