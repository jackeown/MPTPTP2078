%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:05 EST 2020

% Result     : Theorem 51.85s
% Output     : CNFRefutation 51.85s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 156 expanded)
%              Number of clauses        :   66 (  72 expanded)
%              Number of leaves         :   18 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  271 ( 375 expanded)
%              Number of equality atoms :   70 (  92 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_tarski(k2_tarski(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f35,f30])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f28,f30])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0))) ),
    inference(definition_unfolding,[],[f26,f30,f30,f31])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f27,f31,f30])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_tarski(k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(k3_tarski(k2_tarski(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f38,f30,f30])).

fof(f12,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(X0,sK1)))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24,f23])).

fof(f41,plain,(
    ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_160,plain,
    ( ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39)
    | v1_relat_1(k3_tarski(k2_tarski(X0_39,X1_39))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_219890,plain,
    ( ~ v1_relat_1(k6_subset_1(sK0,sK1))
    | v1_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_135,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_6,c_4])).

cnf(c_136,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_135])).

cnf(c_153,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | r1_tarski(k2_relat_1(X0_39),k2_relat_1(X1_39))
    | ~ v1_relat_1(X1_39) ),
    inference(subtyping,[status(esa)],[c_136])).

cnf(c_191557,plain,
    ( ~ r1_tarski(X0_39,k3_tarski(k2_tarski(X1_39,X2_39)))
    | r1_tarski(k2_relat_1(X0_39),k2_relat_1(k3_tarski(k2_tarski(X1_39,X2_39))))
    | ~ v1_relat_1(k3_tarski(k2_tarski(X1_39,X2_39))) ),
    inference(instantiation,[status(thm)],[c_153])).

cnf(c_217265,plain,
    ( ~ r1_tarski(X0_39,k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))
    | r1_tarski(k2_relat_1(X0_39),k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))))
    | ~ v1_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_191557])).

cnf(c_217267,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))))
    | ~ r1_tarski(sK0,k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))
    | ~ v1_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_217265])).

cnf(c_2,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_164,plain,
    ( r1_tarski(X0_39,k3_tarski(k2_tarski(X0_39,X1_39))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_93395,plain,
    ( r1_tarski(X0_39,k3_tarski(k2_tarski(X0_39,sK1))) ),
    inference(instantiation,[status(thm)],[c_164])).

cnf(c_93397,plain,
    ( r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_93395])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_166,plain,
    ( k3_tarski(k2_tarski(X0_39,k6_subset_1(X1_39,X0_39))) = k3_tarski(k2_tarski(X0_39,X1_39)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_92805,plain,
    ( k3_tarski(k2_tarski(sK1,k6_subset_1(X0_39,sK1))) = k3_tarski(k2_tarski(sK1,X0_39)) ),
    inference(instantiation,[status(thm)],[c_166])).

cnf(c_92806,plain,
    ( k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))) = k3_tarski(k2_tarski(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_92805])).

cnf(c_3,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_163,plain,
    ( k2_tarski(X0_39,X1_39) = k2_tarski(X1_39,X0_39) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_91595,plain,
    ( k2_tarski(sK1,X0_39) = k2_tarski(X0_39,sK1) ),
    inference(instantiation,[status(thm)],[c_163])).

cnf(c_91596,plain,
    ( k2_tarski(sK1,sK0) = k2_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_91595])).

cnf(c_174,plain,
    ( X0_40 != X1_40
    | k3_tarski(X0_40) = k3_tarski(X1_40) ),
    theory(equality)).

cnf(c_1003,plain,
    ( X0_40 != k2_tarski(X0_39,X1_39)
    | k3_tarski(X0_40) = k3_tarski(k2_tarski(X0_39,X1_39)) ),
    inference(instantiation,[status(thm)],[c_174])).

cnf(c_1389,plain,
    ( k2_tarski(X0_39,X1_39) != k2_tarski(X1_39,X0_39)
    | k3_tarski(k2_tarski(X0_39,X1_39)) = k3_tarski(k2_tarski(X1_39,X0_39)) ),
    inference(instantiation,[status(thm)],[c_1003])).

cnf(c_30467,plain,
    ( k2_tarski(sK1,X0_39) != k2_tarski(X0_39,sK1)
    | k3_tarski(k2_tarski(sK1,X0_39)) = k3_tarski(k2_tarski(X0_39,sK1)) ),
    inference(instantiation,[status(thm)],[c_1389])).

cnf(c_30468,plain,
    ( k2_tarski(sK1,sK0) != k2_tarski(sK0,sK1)
    | k3_tarski(k2_tarski(sK1,sK0)) = k3_tarski(k2_tarski(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_30467])).

cnf(c_176,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | r1_tarski(X2_39,X3_39)
    | X2_39 != X0_39
    | X3_39 != X1_39 ),
    theory(equality)).

cnf(c_1619,plain,
    ( r1_tarski(X0_39,X1_39)
    | ~ r1_tarski(X2_39,k3_tarski(k2_tarski(X3_39,X4_39)))
    | X0_39 != X2_39
    | X1_39 != k3_tarski(k2_tarski(X3_39,X4_39)) ),
    inference(instantiation,[status(thm)],[c_176])).

cnf(c_2284,plain,
    ( ~ r1_tarski(X0_39,k3_tarski(k2_tarski(X1_39,X2_39)))
    | r1_tarski(X3_39,k3_tarski(k2_tarski(X1_39,k6_subset_1(X2_39,X1_39))))
    | X3_39 != X0_39
    | k3_tarski(k2_tarski(X1_39,k6_subset_1(X2_39,X1_39))) != k3_tarski(k2_tarski(X1_39,X2_39)) ),
    inference(instantiation,[status(thm)],[c_1619])).

cnf(c_30064,plain,
    ( ~ r1_tarski(X0_39,k3_tarski(k2_tarski(sK1,X1_39)))
    | r1_tarski(sK0,k3_tarski(k2_tarski(sK1,k6_subset_1(X1_39,sK1))))
    | k3_tarski(k2_tarski(sK1,k6_subset_1(X1_39,sK1))) != k3_tarski(k2_tarski(sK1,X1_39))
    | sK0 != X0_39 ),
    inference(instantiation,[status(thm)],[c_2284])).

cnf(c_30066,plain,
    ( r1_tarski(sK0,k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))
    | ~ r1_tarski(sK0,k3_tarski(k2_tarski(sK1,sK0)))
    | k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))) != k3_tarski(k2_tarski(sK1,sK0))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_30064])).

cnf(c_2075,plain,
    ( r1_tarski(X0_39,X1_39)
    | ~ r1_tarski(k2_relat_1(X2_39),k2_relat_1(k3_tarski(k2_tarski(X3_39,X4_39))))
    | X0_39 != k2_relat_1(X2_39)
    | X1_39 != k2_relat_1(k3_tarski(k2_tarski(X3_39,X4_39))) ),
    inference(instantiation,[status(thm)],[c_176])).

cnf(c_3363,plain,
    ( r1_tarski(X0_39,k3_tarski(k2_tarski(k2_relat_1(X1_39),k2_relat_1(X2_39))))
    | ~ r1_tarski(k2_relat_1(X3_39),k2_relat_1(k3_tarski(k2_tarski(X1_39,X2_39))))
    | X0_39 != k2_relat_1(X3_39)
    | k3_tarski(k2_tarski(k2_relat_1(X1_39),k2_relat_1(X2_39))) != k2_relat_1(k3_tarski(k2_tarski(X1_39,X2_39))) ),
    inference(instantiation,[status(thm)],[c_2075])).

cnf(c_7179,plain,
    ( ~ r1_tarski(k2_relat_1(X0_39),k2_relat_1(k3_tarski(k2_tarski(X1_39,X2_39))))
    | r1_tarski(k2_relat_1(X3_39),k3_tarski(k2_tarski(k2_relat_1(X1_39),k2_relat_1(X2_39))))
    | k2_relat_1(X3_39) != k2_relat_1(X0_39)
    | k3_tarski(k2_tarski(k2_relat_1(X1_39),k2_relat_1(X2_39))) != k2_relat_1(k3_tarski(k2_tarski(X1_39,X2_39))) ),
    inference(instantiation,[status(thm)],[c_3363])).

cnf(c_17233,plain,
    ( ~ r1_tarski(k2_relat_1(X0_39),k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))))
    | r1_tarski(k2_relat_1(sK0),k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))))
    | k2_relat_1(sK0) != k2_relat_1(X0_39)
    | k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_7179])).

cnf(c_17235,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))))
    | r1_tarski(k2_relat_1(sK0),k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))))
    | k2_relat_1(sK0) != k2_relat_1(sK0)
    | k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_17233])).

cnf(c_648,plain,
    ( r1_tarski(X0_39,X1_39)
    | ~ r1_tarski(X2_39,k3_tarski(k2_tarski(X2_39,X3_39)))
    | X0_39 != X2_39
    | X1_39 != k3_tarski(k2_tarski(X2_39,X3_39)) ),
    inference(instantiation,[status(thm)],[c_176])).

cnf(c_1002,plain,
    ( r1_tarski(X0_39,k3_tarski(X0_40))
    | ~ r1_tarski(X1_39,k3_tarski(k2_tarski(X1_39,X2_39)))
    | X0_39 != X1_39
    | k3_tarski(X0_40) != k3_tarski(k2_tarski(X1_39,X2_39)) ),
    inference(instantiation,[status(thm)],[c_648])).

cnf(c_2786,plain,
    ( ~ r1_tarski(X0_39,k3_tarski(k2_tarski(X0_39,X1_39)))
    | r1_tarski(X2_39,k3_tarski(k2_tarski(X1_39,X0_39)))
    | X2_39 != X0_39
    | k3_tarski(k2_tarski(X1_39,X0_39)) != k3_tarski(k2_tarski(X0_39,X1_39)) ),
    inference(instantiation,[status(thm)],[c_1002])).

cnf(c_11594,plain,
    ( ~ r1_tarski(X0_39,k3_tarski(k2_tarski(X0_39,sK1)))
    | r1_tarski(sK0,k3_tarski(k2_tarski(sK1,X0_39)))
    | k3_tarski(k2_tarski(sK1,X0_39)) != k3_tarski(k2_tarski(X0_39,sK1))
    | sK0 != X0_39 ),
    inference(instantiation,[status(thm)],[c_2786])).

cnf(c_11596,plain,
    ( r1_tarski(sK0,k3_tarski(k2_tarski(sK1,sK0)))
    | ~ r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1)))
    | k3_tarski(k2_tarski(sK1,sK0)) != k3_tarski(k2_tarski(sK0,sK1))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_11594])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
    | r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_165,plain,
    ( ~ r1_tarski(X0_39,k3_tarski(k2_tarski(X1_39,X2_39)))
    | r1_tarski(k6_subset_1(X0_39,X1_39),X2_39) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_6003,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),X0_39)
    | ~ r1_tarski(sK0,k3_tarski(k2_tarski(sK1,X0_39))) ),
    inference(instantiation,[status(thm)],[c_165])).

cnf(c_6005,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),sK0)
    | ~ r1_tarski(sK0,k3_tarski(k2_tarski(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_6003])).

cnf(c_85,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_86,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_85])).

cnf(c_108,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_86])).

cnf(c_155,plain,
    ( ~ r1_tarski(X0_39,X1_39)
    | ~ v1_relat_1(X1_39)
    | v1_relat_1(X0_39) ),
    inference(subtyping,[status(esa)],[c_108])).

cnf(c_4195,plain,
    ( ~ r1_tarski(k6_subset_1(sK0,sK1),X0_39)
    | ~ v1_relat_1(X0_39)
    | v1_relat_1(k6_subset_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_155])).

cnf(c_4197,plain,
    ( ~ r1_tarski(k6_subset_1(sK0,sK1),sK0)
    | v1_relat_1(k6_subset_1(sK0,sK1))
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_4195])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k3_tarski(k2_tarski(k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_159,plain,
    ( ~ v1_relat_1(X0_39)
    | ~ v1_relat_1(X1_39)
    | k3_tarski(k2_tarski(k2_relat_1(X0_39),k2_relat_1(X1_39))) = k2_relat_1(k3_tarski(k2_tarski(X0_39,X1_39))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2663,plain,
    ( ~ v1_relat_1(k6_subset_1(sK0,sK1))
    | ~ v1_relat_1(sK1)
    | k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) = k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_159])).

cnf(c_630,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))
    | ~ r1_tarski(k2_relat_1(sK0),k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))))) ),
    inference(instantiation,[status(thm)],[c_165])).

cnf(c_168,plain,
    ( X0_39 = X0_39 ),
    theory(equality)).

cnf(c_188,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_168])).

cnf(c_179,plain,
    ( X0_39 != X1_39
    | k2_relat_1(X0_39) = k2_relat_1(X1_39) ),
    theory(equality)).

cnf(c_186,plain,
    ( k2_relat_1(sK0) = k2_relat_1(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_179])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_219890,c_217267,c_93397,c_92806,c_91596,c_30468,c_30066,c_17235,c_11596,c_6005,c_4197,c_2663,c_630,c_188,c_186,c_11,c_12,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:38:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 51.85/7.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 51.85/7.00  
% 51.85/7.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.85/7.00  
% 51.85/7.00  ------  iProver source info
% 51.85/7.00  
% 51.85/7.00  git: date: 2020-06-30 10:37:57 +0100
% 51.85/7.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.85/7.00  git: non_committed_changes: false
% 51.85/7.00  git: last_make_outside_of_git: false
% 51.85/7.00  
% 51.85/7.00  ------ 
% 51.85/7.00  
% 51.85/7.00  ------ Input Options
% 51.85/7.00  
% 51.85/7.00  --out_options                           all
% 51.85/7.00  --tptp_safe_out                         true
% 51.85/7.00  --problem_path                          ""
% 51.85/7.00  --include_path                          ""
% 51.85/7.00  --clausifier                            res/vclausify_rel
% 51.85/7.00  --clausifier_options                    --mode clausify
% 51.85/7.00  --stdin                                 false
% 51.85/7.00  --stats_out                             sel
% 51.85/7.00  
% 51.85/7.00  ------ General Options
% 51.85/7.00  
% 51.85/7.00  --fof                                   false
% 51.85/7.00  --time_out_real                         604.99
% 51.85/7.00  --time_out_virtual                      -1.
% 51.85/7.00  --symbol_type_check                     false
% 51.85/7.00  --clausify_out                          false
% 51.85/7.00  --sig_cnt_out                           false
% 51.85/7.00  --trig_cnt_out                          false
% 51.85/7.00  --trig_cnt_out_tolerance                1.
% 51.85/7.00  --trig_cnt_out_sk_spl                   false
% 51.85/7.00  --abstr_cl_out                          false
% 51.85/7.00  
% 51.85/7.00  ------ Global Options
% 51.85/7.00  
% 51.85/7.00  --schedule                              none
% 51.85/7.00  --add_important_lit                     false
% 51.85/7.00  --prop_solver_per_cl                    1000
% 51.85/7.00  --min_unsat_core                        false
% 51.85/7.00  --soft_assumptions                      false
% 51.85/7.00  --soft_lemma_size                       3
% 51.85/7.00  --prop_impl_unit_size                   0
% 51.85/7.00  --prop_impl_unit                        []
% 51.85/7.00  --share_sel_clauses                     true
% 51.85/7.00  --reset_solvers                         false
% 51.85/7.00  --bc_imp_inh                            [conj_cone]
% 51.85/7.00  --conj_cone_tolerance                   3.
% 51.85/7.00  --extra_neg_conj                        none
% 51.85/7.00  --large_theory_mode                     true
% 51.85/7.00  --prolific_symb_bound                   200
% 51.85/7.00  --lt_threshold                          2000
% 51.85/7.00  --clause_weak_htbl                      true
% 51.85/7.00  --gc_record_bc_elim                     false
% 51.85/7.00  
% 51.85/7.00  ------ Preprocessing Options
% 51.85/7.00  
% 51.85/7.00  --preprocessing_flag                    true
% 51.85/7.00  --time_out_prep_mult                    0.1
% 51.85/7.00  --splitting_mode                        input
% 51.85/7.00  --splitting_grd                         true
% 51.85/7.00  --splitting_cvd                         false
% 51.85/7.00  --splitting_cvd_svl                     false
% 51.85/7.00  --splitting_nvd                         32
% 51.85/7.00  --sub_typing                            true
% 51.85/7.00  --prep_gs_sim                           false
% 51.85/7.00  --prep_unflatten                        true
% 51.85/7.00  --prep_res_sim                          true
% 51.85/7.00  --prep_upred                            true
% 51.85/7.00  --prep_sem_filter                       exhaustive
% 51.85/7.00  --prep_sem_filter_out                   false
% 51.85/7.00  --pred_elim                             false
% 51.85/7.00  --res_sim_input                         true
% 51.85/7.00  --eq_ax_congr_red                       true
% 51.85/7.00  --pure_diseq_elim                       true
% 51.85/7.00  --brand_transform                       false
% 51.85/7.00  --non_eq_to_eq                          false
% 51.85/7.00  --prep_def_merge                        true
% 51.85/7.00  --prep_def_merge_prop_impl              false
% 51.85/7.00  --prep_def_merge_mbd                    true
% 51.85/7.00  --prep_def_merge_tr_red                 false
% 51.85/7.00  --prep_def_merge_tr_cl                  false
% 51.85/7.00  --smt_preprocessing                     true
% 51.85/7.00  --smt_ac_axioms                         fast
% 51.85/7.00  --preprocessed_out                      false
% 51.85/7.00  --preprocessed_stats                    false
% 51.85/7.00  
% 51.85/7.00  ------ Abstraction refinement Options
% 51.85/7.00  
% 51.85/7.00  --abstr_ref                             []
% 51.85/7.00  --abstr_ref_prep                        false
% 51.85/7.00  --abstr_ref_until_sat                   false
% 51.85/7.00  --abstr_ref_sig_restrict                funpre
% 51.85/7.00  --abstr_ref_af_restrict_to_split_sk     false
% 51.85/7.00  --abstr_ref_under                       []
% 51.85/7.00  
% 51.85/7.00  ------ SAT Options
% 51.85/7.00  
% 51.85/7.00  --sat_mode                              false
% 51.85/7.00  --sat_fm_restart_options                ""
% 51.85/7.00  --sat_gr_def                            false
% 51.85/7.00  --sat_epr_types                         true
% 51.85/7.00  --sat_non_cyclic_types                  false
% 51.85/7.00  --sat_finite_models                     false
% 51.85/7.00  --sat_fm_lemmas                         false
% 51.85/7.00  --sat_fm_prep                           false
% 51.85/7.00  --sat_fm_uc_incr                        true
% 51.85/7.00  --sat_out_model                         small
% 51.85/7.00  --sat_out_clauses                       false
% 51.85/7.00  
% 51.85/7.00  ------ QBF Options
% 51.85/7.00  
% 51.85/7.00  --qbf_mode                              false
% 51.85/7.00  --qbf_elim_univ                         false
% 51.85/7.00  --qbf_dom_inst                          none
% 51.85/7.00  --qbf_dom_pre_inst                      false
% 51.85/7.00  --qbf_sk_in                             false
% 51.85/7.00  --qbf_pred_elim                         true
% 51.85/7.00  --qbf_split                             512
% 51.85/7.00  
% 51.85/7.00  ------ BMC1 Options
% 51.85/7.00  
% 51.85/7.00  --bmc1_incremental                      false
% 51.85/7.00  --bmc1_axioms                           reachable_all
% 51.85/7.00  --bmc1_min_bound                        0
% 51.85/7.00  --bmc1_max_bound                        -1
% 51.85/7.00  --bmc1_max_bound_default                -1
% 51.85/7.00  --bmc1_symbol_reachability              true
% 51.85/7.00  --bmc1_property_lemmas                  false
% 51.85/7.00  --bmc1_k_induction                      false
% 51.85/7.00  --bmc1_non_equiv_states                 false
% 51.85/7.00  --bmc1_deadlock                         false
% 51.85/7.00  --bmc1_ucm                              false
% 51.85/7.00  --bmc1_add_unsat_core                   none
% 51.85/7.00  --bmc1_unsat_core_children              false
% 51.85/7.00  --bmc1_unsat_core_extrapolate_axioms    false
% 51.85/7.00  --bmc1_out_stat                         full
% 51.85/7.00  --bmc1_ground_init                      false
% 51.85/7.00  --bmc1_pre_inst_next_state              false
% 51.85/7.00  --bmc1_pre_inst_state                   false
% 51.85/7.00  --bmc1_pre_inst_reach_state             false
% 51.85/7.00  --bmc1_out_unsat_core                   false
% 51.85/7.00  --bmc1_aig_witness_out                  false
% 51.85/7.00  --bmc1_verbose                          false
% 51.85/7.00  --bmc1_dump_clauses_tptp                false
% 51.85/7.00  --bmc1_dump_unsat_core_tptp             false
% 51.85/7.00  --bmc1_dump_file                        -
% 51.85/7.00  --bmc1_ucm_expand_uc_limit              128
% 51.85/7.00  --bmc1_ucm_n_expand_iterations          6
% 51.85/7.00  --bmc1_ucm_extend_mode                  1
% 51.85/7.00  --bmc1_ucm_init_mode                    2
% 51.85/7.00  --bmc1_ucm_cone_mode                    none
% 51.85/7.00  --bmc1_ucm_reduced_relation_type        0
% 51.85/7.00  --bmc1_ucm_relax_model                  4
% 51.85/7.00  --bmc1_ucm_full_tr_after_sat            true
% 51.85/7.00  --bmc1_ucm_expand_neg_assumptions       false
% 51.85/7.00  --bmc1_ucm_layered_model                none
% 51.85/7.00  --bmc1_ucm_max_lemma_size               10
% 51.85/7.00  
% 51.85/7.00  ------ AIG Options
% 51.85/7.00  
% 51.85/7.00  --aig_mode                              false
% 51.85/7.00  
% 51.85/7.00  ------ Instantiation Options
% 51.85/7.00  
% 51.85/7.00  --instantiation_flag                    true
% 51.85/7.00  --inst_sos_flag                         false
% 51.85/7.00  --inst_sos_phase                        true
% 51.85/7.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.85/7.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.85/7.00  --inst_lit_sel_side                     num_symb
% 51.85/7.00  --inst_solver_per_active                1400
% 51.85/7.00  --inst_solver_calls_frac                1.
% 51.85/7.00  --inst_passive_queue_type               priority_queues
% 51.85/7.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.85/7.00  --inst_passive_queues_freq              [25;2]
% 51.85/7.00  --inst_dismatching                      true
% 51.85/7.00  --inst_eager_unprocessed_to_passive     true
% 51.85/7.00  --inst_prop_sim_given                   true
% 51.85/7.00  --inst_prop_sim_new                     false
% 51.85/7.00  --inst_subs_new                         false
% 51.85/7.00  --inst_eq_res_simp                      false
% 51.85/7.00  --inst_subs_given                       false
% 51.85/7.00  --inst_orphan_elimination               true
% 51.85/7.00  --inst_learning_loop_flag               true
% 51.85/7.00  --inst_learning_start                   3000
% 51.85/7.00  --inst_learning_factor                  2
% 51.85/7.00  --inst_start_prop_sim_after_learn       3
% 51.85/7.00  --inst_sel_renew                        solver
% 51.85/7.00  --inst_lit_activity_flag                true
% 51.85/7.00  --inst_restr_to_given                   false
% 51.85/7.00  --inst_activity_threshold               500
% 51.85/7.00  --inst_out_proof                        true
% 51.85/7.00  
% 51.85/7.00  ------ Resolution Options
% 51.85/7.00  
% 51.85/7.00  --resolution_flag                       true
% 51.85/7.00  --res_lit_sel                           adaptive
% 51.85/7.00  --res_lit_sel_side                      none
% 51.85/7.00  --res_ordering                          kbo
% 51.85/7.00  --res_to_prop_solver                    active
% 51.85/7.00  --res_prop_simpl_new                    false
% 51.85/7.00  --res_prop_simpl_given                  true
% 51.85/7.00  --res_passive_queue_type                priority_queues
% 51.85/7.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.85/7.00  --res_passive_queues_freq               [15;5]
% 51.85/7.00  --res_forward_subs                      full
% 51.85/7.00  --res_backward_subs                     full
% 51.85/7.00  --res_forward_subs_resolution           true
% 51.85/7.00  --res_backward_subs_resolution          true
% 51.85/7.00  --res_orphan_elimination                true
% 51.85/7.00  --res_time_limit                        2.
% 51.85/7.00  --res_out_proof                         true
% 51.85/7.00  
% 51.85/7.00  ------ Superposition Options
% 51.85/7.00  
% 51.85/7.00  --superposition_flag                    true
% 51.85/7.00  --sup_passive_queue_type                priority_queues
% 51.85/7.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.85/7.00  --sup_passive_queues_freq               [1;4]
% 51.85/7.00  --demod_completeness_check              fast
% 51.85/7.00  --demod_use_ground                      true
% 51.85/7.00  --sup_to_prop_solver                    passive
% 51.85/7.00  --sup_prop_simpl_new                    true
% 51.85/7.00  --sup_prop_simpl_given                  true
% 51.85/7.00  --sup_fun_splitting                     false
% 51.85/7.00  --sup_smt_interval                      50000
% 51.85/7.00  
% 51.85/7.00  ------ Superposition Simplification Setup
% 51.85/7.00  
% 51.85/7.00  --sup_indices_passive                   []
% 51.85/7.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.85/7.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.85/7.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.85/7.00  --sup_full_triv                         [TrivRules;PropSubs]
% 51.85/7.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.85/7.00  --sup_full_bw                           [BwDemod]
% 51.85/7.00  --sup_immed_triv                        [TrivRules]
% 51.85/7.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.85/7.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.85/7.00  --sup_immed_bw_main                     []
% 51.85/7.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.85/7.00  --sup_input_triv                        [Unflattening;TrivRules]
% 51.85/7.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.85/7.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.85/7.00  
% 51.85/7.00  ------ Combination Options
% 51.85/7.00  
% 51.85/7.00  --comb_res_mult                         3
% 51.85/7.00  --comb_sup_mult                         2
% 51.85/7.00  --comb_inst_mult                        10
% 51.85/7.00  
% 51.85/7.00  ------ Debug Options
% 51.85/7.00  
% 51.85/7.00  --dbg_backtrace                         false
% 51.85/7.00  --dbg_dump_prop_clauses                 false
% 51.85/7.00  --dbg_dump_prop_clauses_file            -
% 51.85/7.00  --dbg_out_stat                          false
% 51.85/7.00  ------ Parsing...
% 51.85/7.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.85/7.00  
% 51.85/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 51.85/7.00  
% 51.85/7.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.85/7.00  
% 51.85/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.85/7.00  ------ Proving...
% 51.85/7.00  ------ Problem Properties 
% 51.85/7.00  
% 51.85/7.00  
% 51.85/7.00  clauses                                 14
% 51.85/7.00  conjectures                             3
% 51.85/7.00  EPR                                     3
% 51.85/7.00  Horn                                    14
% 51.85/7.00  unary                                   6
% 51.85/7.00  binary                                  3
% 51.85/7.00  lits                                    27
% 51.85/7.00  lits eq                                 3
% 51.85/7.00  fd_pure                                 0
% 51.85/7.00  fd_pseudo                               0
% 51.85/7.00  fd_cond                                 0
% 51.85/7.00  fd_pseudo_cond                          0
% 51.85/7.00  AC symbols                              0
% 51.85/7.00  
% 51.85/7.00  ------ Input Options Time Limit: Unbounded
% 51.85/7.00  
% 51.85/7.00  
% 51.85/7.00  ------ 
% 51.85/7.00  Current options:
% 51.85/7.00  ------ 
% 51.85/7.00  
% 51.85/7.00  ------ Input Options
% 51.85/7.00  
% 51.85/7.00  --out_options                           all
% 51.85/7.00  --tptp_safe_out                         true
% 51.85/7.00  --problem_path                          ""
% 51.85/7.00  --include_path                          ""
% 51.85/7.00  --clausifier                            res/vclausify_rel
% 51.85/7.00  --clausifier_options                    --mode clausify
% 51.85/7.00  --stdin                                 false
% 51.85/7.00  --stats_out                             sel
% 51.85/7.00  
% 51.85/7.00  ------ General Options
% 51.85/7.00  
% 51.85/7.00  --fof                                   false
% 51.85/7.00  --time_out_real                         604.99
% 51.85/7.00  --time_out_virtual                      -1.
% 51.85/7.00  --symbol_type_check                     false
% 51.85/7.00  --clausify_out                          false
% 51.85/7.00  --sig_cnt_out                           false
% 51.85/7.00  --trig_cnt_out                          false
% 51.85/7.00  --trig_cnt_out_tolerance                1.
% 51.85/7.00  --trig_cnt_out_sk_spl                   false
% 51.85/7.00  --abstr_cl_out                          false
% 51.85/7.00  
% 51.85/7.00  ------ Global Options
% 51.85/7.00  
% 51.85/7.00  --schedule                              none
% 51.85/7.00  --add_important_lit                     false
% 51.85/7.00  --prop_solver_per_cl                    1000
% 51.85/7.00  --min_unsat_core                        false
% 51.85/7.00  --soft_assumptions                      false
% 51.85/7.00  --soft_lemma_size                       3
% 51.85/7.00  --prop_impl_unit_size                   0
% 51.85/7.00  --prop_impl_unit                        []
% 51.85/7.00  --share_sel_clauses                     true
% 51.85/7.00  --reset_solvers                         false
% 51.85/7.00  --bc_imp_inh                            [conj_cone]
% 51.85/7.00  --conj_cone_tolerance                   3.
% 51.85/7.00  --extra_neg_conj                        none
% 51.85/7.00  --large_theory_mode                     true
% 51.85/7.00  --prolific_symb_bound                   200
% 51.85/7.00  --lt_threshold                          2000
% 51.85/7.00  --clause_weak_htbl                      true
% 51.85/7.00  --gc_record_bc_elim                     false
% 51.85/7.00  
% 51.85/7.00  ------ Preprocessing Options
% 51.85/7.00  
% 51.85/7.00  --preprocessing_flag                    true
% 51.85/7.00  --time_out_prep_mult                    0.1
% 51.85/7.00  --splitting_mode                        input
% 51.85/7.00  --splitting_grd                         true
% 51.85/7.00  --splitting_cvd                         false
% 51.85/7.00  --splitting_cvd_svl                     false
% 51.85/7.00  --splitting_nvd                         32
% 51.85/7.00  --sub_typing                            true
% 51.85/7.00  --prep_gs_sim                           false
% 51.85/7.00  --prep_unflatten                        true
% 51.85/7.00  --prep_res_sim                          true
% 51.85/7.00  --prep_upred                            true
% 51.85/7.00  --prep_sem_filter                       exhaustive
% 51.85/7.00  --prep_sem_filter_out                   false
% 51.85/7.00  --pred_elim                             false
% 51.85/7.00  --res_sim_input                         true
% 51.85/7.00  --eq_ax_congr_red                       true
% 51.85/7.00  --pure_diseq_elim                       true
% 51.85/7.00  --brand_transform                       false
% 51.85/7.00  --non_eq_to_eq                          false
% 51.85/7.00  --prep_def_merge                        true
% 51.85/7.00  --prep_def_merge_prop_impl              false
% 51.85/7.00  --prep_def_merge_mbd                    true
% 51.85/7.00  --prep_def_merge_tr_red                 false
% 51.85/7.00  --prep_def_merge_tr_cl                  false
% 51.85/7.00  --smt_preprocessing                     true
% 51.85/7.00  --smt_ac_axioms                         fast
% 51.85/7.00  --preprocessed_out                      false
% 51.85/7.00  --preprocessed_stats                    false
% 51.85/7.00  
% 51.85/7.00  ------ Abstraction refinement Options
% 51.85/7.00  
% 51.85/7.00  --abstr_ref                             []
% 51.85/7.00  --abstr_ref_prep                        false
% 51.85/7.00  --abstr_ref_until_sat                   false
% 51.85/7.00  --abstr_ref_sig_restrict                funpre
% 51.85/7.00  --abstr_ref_af_restrict_to_split_sk     false
% 51.85/7.00  --abstr_ref_under                       []
% 51.85/7.00  
% 51.85/7.00  ------ SAT Options
% 51.85/7.00  
% 51.85/7.00  --sat_mode                              false
% 51.85/7.00  --sat_fm_restart_options                ""
% 51.85/7.00  --sat_gr_def                            false
% 51.85/7.00  --sat_epr_types                         true
% 51.85/7.00  --sat_non_cyclic_types                  false
% 51.85/7.00  --sat_finite_models                     false
% 51.85/7.00  --sat_fm_lemmas                         false
% 51.85/7.00  --sat_fm_prep                           false
% 51.85/7.00  --sat_fm_uc_incr                        true
% 51.85/7.00  --sat_out_model                         small
% 51.85/7.00  --sat_out_clauses                       false
% 51.85/7.00  
% 51.85/7.00  ------ QBF Options
% 51.85/7.00  
% 51.85/7.00  --qbf_mode                              false
% 51.85/7.00  --qbf_elim_univ                         false
% 51.85/7.00  --qbf_dom_inst                          none
% 51.85/7.00  --qbf_dom_pre_inst                      false
% 51.85/7.00  --qbf_sk_in                             false
% 51.85/7.00  --qbf_pred_elim                         true
% 51.85/7.00  --qbf_split                             512
% 51.85/7.00  
% 51.85/7.00  ------ BMC1 Options
% 51.85/7.00  
% 51.85/7.00  --bmc1_incremental                      false
% 51.85/7.00  --bmc1_axioms                           reachable_all
% 51.85/7.00  --bmc1_min_bound                        0
% 51.85/7.00  --bmc1_max_bound                        -1
% 51.85/7.00  --bmc1_max_bound_default                -1
% 51.85/7.00  --bmc1_symbol_reachability              true
% 51.85/7.00  --bmc1_property_lemmas                  false
% 51.85/7.00  --bmc1_k_induction                      false
% 51.85/7.00  --bmc1_non_equiv_states                 false
% 51.85/7.00  --bmc1_deadlock                         false
% 51.85/7.00  --bmc1_ucm                              false
% 51.85/7.00  --bmc1_add_unsat_core                   none
% 51.85/7.00  --bmc1_unsat_core_children              false
% 51.85/7.00  --bmc1_unsat_core_extrapolate_axioms    false
% 51.85/7.00  --bmc1_out_stat                         full
% 51.85/7.00  --bmc1_ground_init                      false
% 51.85/7.00  --bmc1_pre_inst_next_state              false
% 51.85/7.00  --bmc1_pre_inst_state                   false
% 51.85/7.00  --bmc1_pre_inst_reach_state             false
% 51.85/7.00  --bmc1_out_unsat_core                   false
% 51.85/7.00  --bmc1_aig_witness_out                  false
% 51.85/7.00  --bmc1_verbose                          false
% 51.85/7.00  --bmc1_dump_clauses_tptp                false
% 51.85/7.00  --bmc1_dump_unsat_core_tptp             false
% 51.85/7.00  --bmc1_dump_file                        -
% 51.85/7.00  --bmc1_ucm_expand_uc_limit              128
% 51.85/7.00  --bmc1_ucm_n_expand_iterations          6
% 51.85/7.00  --bmc1_ucm_extend_mode                  1
% 51.85/7.00  --bmc1_ucm_init_mode                    2
% 51.85/7.00  --bmc1_ucm_cone_mode                    none
% 51.85/7.00  --bmc1_ucm_reduced_relation_type        0
% 51.85/7.00  --bmc1_ucm_relax_model                  4
% 51.85/7.00  --bmc1_ucm_full_tr_after_sat            true
% 51.85/7.00  --bmc1_ucm_expand_neg_assumptions       false
% 51.85/7.00  --bmc1_ucm_layered_model                none
% 51.85/7.00  --bmc1_ucm_max_lemma_size               10
% 51.85/7.00  
% 51.85/7.00  ------ AIG Options
% 51.85/7.00  
% 51.85/7.00  --aig_mode                              false
% 51.85/7.00  
% 51.85/7.00  ------ Instantiation Options
% 51.85/7.00  
% 51.85/7.00  --instantiation_flag                    true
% 51.85/7.00  --inst_sos_flag                         false
% 51.85/7.00  --inst_sos_phase                        true
% 51.85/7.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.85/7.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.85/7.00  --inst_lit_sel_side                     num_symb
% 51.85/7.00  --inst_solver_per_active                1400
% 51.85/7.00  --inst_solver_calls_frac                1.
% 51.85/7.00  --inst_passive_queue_type               priority_queues
% 51.85/7.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.85/7.00  --inst_passive_queues_freq              [25;2]
% 51.85/7.00  --inst_dismatching                      true
% 51.85/7.00  --inst_eager_unprocessed_to_passive     true
% 51.85/7.00  --inst_prop_sim_given                   true
% 51.85/7.00  --inst_prop_sim_new                     false
% 51.85/7.00  --inst_subs_new                         false
% 51.85/7.00  --inst_eq_res_simp                      false
% 51.85/7.00  --inst_subs_given                       false
% 51.85/7.00  --inst_orphan_elimination               true
% 51.85/7.00  --inst_learning_loop_flag               true
% 51.85/7.00  --inst_learning_start                   3000
% 51.85/7.00  --inst_learning_factor                  2
% 51.85/7.00  --inst_start_prop_sim_after_learn       3
% 51.85/7.00  --inst_sel_renew                        solver
% 51.85/7.00  --inst_lit_activity_flag                true
% 51.85/7.00  --inst_restr_to_given                   false
% 51.85/7.00  --inst_activity_threshold               500
% 51.85/7.00  --inst_out_proof                        true
% 51.85/7.00  
% 51.85/7.00  ------ Resolution Options
% 51.85/7.00  
% 51.85/7.00  --resolution_flag                       true
% 51.85/7.00  --res_lit_sel                           adaptive
% 51.85/7.00  --res_lit_sel_side                      none
% 51.85/7.00  --res_ordering                          kbo
% 51.85/7.00  --res_to_prop_solver                    active
% 51.85/7.00  --res_prop_simpl_new                    false
% 51.85/7.00  --res_prop_simpl_given                  true
% 51.85/7.00  --res_passive_queue_type                priority_queues
% 51.85/7.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.85/7.00  --res_passive_queues_freq               [15;5]
% 51.85/7.00  --res_forward_subs                      full
% 51.85/7.00  --res_backward_subs                     full
% 51.85/7.00  --res_forward_subs_resolution           true
% 51.85/7.00  --res_backward_subs_resolution          true
% 51.85/7.00  --res_orphan_elimination                true
% 51.85/7.00  --res_time_limit                        2.
% 51.85/7.00  --res_out_proof                         true
% 51.85/7.00  
% 51.85/7.00  ------ Superposition Options
% 51.85/7.00  
% 51.85/7.00  --superposition_flag                    true
% 51.85/7.00  --sup_passive_queue_type                priority_queues
% 51.85/7.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.85/7.00  --sup_passive_queues_freq               [1;4]
% 51.85/7.00  --demod_completeness_check              fast
% 51.85/7.00  --demod_use_ground                      true
% 51.85/7.00  --sup_to_prop_solver                    passive
% 51.85/7.00  --sup_prop_simpl_new                    true
% 51.85/7.00  --sup_prop_simpl_given                  true
% 51.85/7.00  --sup_fun_splitting                     false
% 51.85/7.00  --sup_smt_interval                      50000
% 51.85/7.00  
% 51.85/7.00  ------ Superposition Simplification Setup
% 51.85/7.00  
% 51.85/7.00  --sup_indices_passive                   []
% 51.85/7.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.85/7.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.85/7.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.85/7.00  --sup_full_triv                         [TrivRules;PropSubs]
% 51.85/7.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.85/7.00  --sup_full_bw                           [BwDemod]
% 51.85/7.00  --sup_immed_triv                        [TrivRules]
% 51.85/7.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.85/7.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.85/7.00  --sup_immed_bw_main                     []
% 51.85/7.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.85/7.00  --sup_input_triv                        [Unflattening;TrivRules]
% 51.85/7.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.85/7.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.85/7.00  
% 51.85/7.00  ------ Combination Options
% 51.85/7.00  
% 51.85/7.00  --comb_res_mult                         3
% 51.85/7.00  --comb_sup_mult                         2
% 51.85/7.00  --comb_inst_mult                        10
% 51.85/7.00  
% 51.85/7.00  ------ Debug Options
% 51.85/7.00  
% 51.85/7.00  --dbg_backtrace                         false
% 51.85/7.00  --dbg_dump_prop_clauses                 false
% 51.85/7.00  --dbg_dump_prop_clauses_file            -
% 51.85/7.00  --dbg_out_stat                          false
% 51.85/7.00  
% 51.85/7.00  
% 51.85/7.00  
% 51.85/7.00  
% 51.85/7.00  ------ Proving...
% 51.85/7.00  
% 51.85/7.00  
% 51.85/7.00  % SZS status Theorem for theBenchmark.p
% 51.85/7.00  
% 51.85/7.00  % SZS output start CNFRefutation for theBenchmark.p
% 51.85/7.00  
% 51.85/7.00  fof(f9,axiom,(
% 51.85/7.00    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k2_xboole_0(X0,X1)))),
% 51.85/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.85/7.00  
% 51.85/7.00  fof(f16,plain,(
% 51.85/7.00    ! [X0,X1] : (v1_relat_1(k2_xboole_0(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 51.85/7.00    inference(ennf_transformation,[],[f9])).
% 51.85/7.00  
% 51.85/7.00  fof(f17,plain,(
% 51.85/7.00    ! [X0,X1] : (v1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 51.85/7.00    inference(flattening,[],[f16])).
% 51.85/7.00  
% 51.85/7.00  fof(f35,plain,(
% 51.85/7.00    ( ! [X0,X1] : (v1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 51.85/7.00    inference(cnf_transformation,[],[f17])).
% 51.85/7.00  
% 51.85/7.00  fof(f5,axiom,(
% 51.85/7.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 51.85/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.85/7.00  
% 51.85/7.00  fof(f30,plain,(
% 51.85/7.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 51.85/7.00    inference(cnf_transformation,[],[f5])).
% 51.85/7.00  
% 51.85/7.00  fof(f45,plain,(
% 51.85/7.00    ( ! [X0,X1] : (v1_relat_1(k3_tarski(k2_tarski(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 51.85/7.00    inference(definition_unfolding,[],[f35,f30])).
% 51.85/7.00  
% 51.85/7.00  fof(f10,axiom,(
% 51.85/7.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 51.85/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.85/7.00  
% 51.85/7.00  fof(f18,plain,(
% 51.85/7.00    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 51.85/7.00    inference(ennf_transformation,[],[f10])).
% 51.85/7.00  
% 51.85/7.00  fof(f19,plain,(
% 51.85/7.00    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 51.85/7.00    inference(flattening,[],[f18])).
% 51.85/7.00  
% 51.85/7.00  fof(f37,plain,(
% 51.85/7.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 51.85/7.00    inference(cnf_transformation,[],[f19])).
% 51.85/7.00  
% 51.85/7.00  fof(f8,axiom,(
% 51.85/7.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 51.85/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.85/7.00  
% 51.85/7.00  fof(f15,plain,(
% 51.85/7.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 51.85/7.00    inference(ennf_transformation,[],[f8])).
% 51.85/7.00  
% 51.85/7.00  fof(f34,plain,(
% 51.85/7.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 51.85/7.00    inference(cnf_transformation,[],[f15])).
% 51.85/7.00  
% 51.85/7.00  fof(f7,axiom,(
% 51.85/7.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 51.85/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.85/7.00  
% 51.85/7.00  fof(f22,plain,(
% 51.85/7.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 51.85/7.00    inference(nnf_transformation,[],[f7])).
% 51.85/7.00  
% 51.85/7.00  fof(f33,plain,(
% 51.85/7.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 51.85/7.00    inference(cnf_transformation,[],[f22])).
% 51.85/7.00  
% 51.85/7.00  fof(f3,axiom,(
% 51.85/7.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 51.85/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.85/7.00  
% 51.85/7.00  fof(f28,plain,(
% 51.85/7.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 51.85/7.00    inference(cnf_transformation,[],[f3])).
% 51.85/7.00  
% 51.85/7.00  fof(f44,plain,(
% 51.85/7.00    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 51.85/7.00    inference(definition_unfolding,[],[f28,f30])).
% 51.85/7.00  
% 51.85/7.00  fof(f1,axiom,(
% 51.85/7.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 51.85/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.85/7.00  
% 51.85/7.00  fof(f26,plain,(
% 51.85/7.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 51.85/7.00    inference(cnf_transformation,[],[f1])).
% 51.85/7.00  
% 51.85/7.00  fof(f6,axiom,(
% 51.85/7.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 51.85/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.85/7.00  
% 51.85/7.00  fof(f31,plain,(
% 51.85/7.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 51.85/7.00    inference(cnf_transformation,[],[f6])).
% 51.85/7.00  
% 51.85/7.00  fof(f42,plain,(
% 51.85/7.00    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0)))) )),
% 51.85/7.00    inference(definition_unfolding,[],[f26,f30,f30,f31])).
% 51.85/7.00  
% 51.85/7.00  fof(f4,axiom,(
% 51.85/7.00    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 51.85/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.85/7.00  
% 51.85/7.00  fof(f29,plain,(
% 51.85/7.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 51.85/7.00    inference(cnf_transformation,[],[f4])).
% 51.85/7.00  
% 51.85/7.00  fof(f2,axiom,(
% 51.85/7.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 51.85/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.85/7.00  
% 51.85/7.00  fof(f14,plain,(
% 51.85/7.00    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 51.85/7.00    inference(ennf_transformation,[],[f2])).
% 51.85/7.00  
% 51.85/7.00  fof(f27,plain,(
% 51.85/7.00    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 51.85/7.00    inference(cnf_transformation,[],[f14])).
% 51.85/7.00  
% 51.85/7.00  fof(f43,plain,(
% 51.85/7.00    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) )),
% 51.85/7.00    inference(definition_unfolding,[],[f27,f31,f30])).
% 51.85/7.00  
% 51.85/7.00  fof(f11,axiom,(
% 51.85/7.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))))),
% 51.85/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.85/7.00  
% 51.85/7.00  fof(f20,plain,(
% 51.85/7.00    ! [X0] : (! [X1] : (k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 51.85/7.00    inference(ennf_transformation,[],[f11])).
% 51.85/7.00  
% 51.85/7.00  fof(f38,plain,(
% 51.85/7.00    ( ! [X0,X1] : (k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 51.85/7.00    inference(cnf_transformation,[],[f20])).
% 51.85/7.00  
% 51.85/7.00  fof(f46,plain,(
% 51.85/7.00    ( ! [X0,X1] : (k3_tarski(k2_tarski(k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(k3_tarski(k2_tarski(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 51.85/7.00    inference(definition_unfolding,[],[f38,f30,f30])).
% 51.85/7.00  
% 51.85/7.00  fof(f12,conjecture,(
% 51.85/7.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 51.85/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.85/7.00  
% 51.85/7.00  fof(f13,negated_conjecture,(
% 51.85/7.00    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 51.85/7.00    inference(negated_conjecture,[],[f12])).
% 51.85/7.00  
% 51.85/7.00  fof(f21,plain,(
% 51.85/7.00    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 51.85/7.00    inference(ennf_transformation,[],[f13])).
% 51.85/7.00  
% 51.85/7.00  fof(f24,plain,(
% 51.85/7.00    ( ! [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) => (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(X0,sK1))) & v1_relat_1(sK1))) )),
% 51.85/7.00    introduced(choice_axiom,[])).
% 51.85/7.00  
% 51.85/7.00  fof(f23,plain,(
% 51.85/7.00    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 51.85/7.00    introduced(choice_axiom,[])).
% 51.85/7.00  
% 51.85/7.00  fof(f25,plain,(
% 51.85/7.00    (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 51.85/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24,f23])).
% 51.85/7.00  
% 51.85/7.00  fof(f41,plain,(
% 51.85/7.00    ~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))),
% 51.85/7.00    inference(cnf_transformation,[],[f25])).
% 51.85/7.00  
% 51.85/7.00  fof(f40,plain,(
% 51.85/7.00    v1_relat_1(sK1)),
% 51.85/7.00    inference(cnf_transformation,[],[f25])).
% 51.85/7.00  
% 51.85/7.00  fof(f39,plain,(
% 51.85/7.00    v1_relat_1(sK0)),
% 51.85/7.00    inference(cnf_transformation,[],[f25])).
% 51.85/7.00  
% 51.85/7.00  cnf(c_7,plain,
% 51.85/7.00      ( ~ v1_relat_1(X0)
% 51.85/7.00      | ~ v1_relat_1(X1)
% 51.85/7.00      | v1_relat_1(k3_tarski(k2_tarski(X0,X1))) ),
% 51.85/7.00      inference(cnf_transformation,[],[f45]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_160,plain,
% 51.85/7.00      ( ~ v1_relat_1(X0_39)
% 51.85/7.00      | ~ v1_relat_1(X1_39)
% 51.85/7.00      | v1_relat_1(k3_tarski(k2_tarski(X0_39,X1_39))) ),
% 51.85/7.00      inference(subtyping,[status(esa)],[c_7]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_219890,plain,
% 51.85/7.00      ( ~ v1_relat_1(k6_subset_1(sK0,sK1))
% 51.85/7.00      | v1_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))
% 51.85/7.00      | ~ v1_relat_1(sK1) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_160]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_8,plain,
% 51.85/7.00      ( ~ r1_tarski(X0,X1)
% 51.85/7.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 51.85/7.00      | ~ v1_relat_1(X0)
% 51.85/7.00      | ~ v1_relat_1(X1) ),
% 51.85/7.00      inference(cnf_transformation,[],[f37]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_6,plain,
% 51.85/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 51.85/7.00      | ~ v1_relat_1(X1)
% 51.85/7.00      | v1_relat_1(X0) ),
% 51.85/7.00      inference(cnf_transformation,[],[f34]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_4,plain,
% 51.85/7.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 51.85/7.00      inference(cnf_transformation,[],[f33]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_135,plain,
% 51.85/7.00      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 51.85/7.00      | ~ r1_tarski(X0,X1)
% 51.85/7.00      | ~ v1_relat_1(X1) ),
% 51.85/7.00      inference(global_propositional_subsumption,
% 51.85/7.00                [status(thm)],
% 51.85/7.00                [c_8,c_6,c_4]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_136,plain,
% 51.85/7.00      ( ~ r1_tarski(X0,X1)
% 51.85/7.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 51.85/7.00      | ~ v1_relat_1(X1) ),
% 51.85/7.00      inference(renaming,[status(thm)],[c_135]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_153,plain,
% 51.85/7.00      ( ~ r1_tarski(X0_39,X1_39)
% 51.85/7.00      | r1_tarski(k2_relat_1(X0_39),k2_relat_1(X1_39))
% 51.85/7.00      | ~ v1_relat_1(X1_39) ),
% 51.85/7.00      inference(subtyping,[status(esa)],[c_136]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_191557,plain,
% 51.85/7.00      ( ~ r1_tarski(X0_39,k3_tarski(k2_tarski(X1_39,X2_39)))
% 51.85/7.00      | r1_tarski(k2_relat_1(X0_39),k2_relat_1(k3_tarski(k2_tarski(X1_39,X2_39))))
% 51.85/7.00      | ~ v1_relat_1(k3_tarski(k2_tarski(X1_39,X2_39))) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_153]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_217265,plain,
% 51.85/7.00      ( ~ r1_tarski(X0_39,k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))
% 51.85/7.00      | r1_tarski(k2_relat_1(X0_39),k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))))
% 51.85/7.00      | ~ v1_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_191557]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_217267,plain,
% 51.85/7.00      ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))))
% 51.85/7.00      | ~ r1_tarski(sK0,k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))
% 51.85/7.00      | ~ v1_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_217265]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_2,plain,
% 51.85/7.00      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
% 51.85/7.00      inference(cnf_transformation,[],[f44]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_164,plain,
% 51.85/7.00      ( r1_tarski(X0_39,k3_tarski(k2_tarski(X0_39,X1_39))) ),
% 51.85/7.00      inference(subtyping,[status(esa)],[c_2]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_93395,plain,
% 51.85/7.00      ( r1_tarski(X0_39,k3_tarski(k2_tarski(X0_39,sK1))) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_164]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_93397,plain,
% 51.85/7.00      ( r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1))) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_93395]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_0,plain,
% 51.85/7.00      ( k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
% 51.85/7.00      inference(cnf_transformation,[],[f42]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_166,plain,
% 51.85/7.00      ( k3_tarski(k2_tarski(X0_39,k6_subset_1(X1_39,X0_39))) = k3_tarski(k2_tarski(X0_39,X1_39)) ),
% 51.85/7.00      inference(subtyping,[status(esa)],[c_0]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_92805,plain,
% 51.85/7.00      ( k3_tarski(k2_tarski(sK1,k6_subset_1(X0_39,sK1))) = k3_tarski(k2_tarski(sK1,X0_39)) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_166]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_92806,plain,
% 51.85/7.00      ( k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))) = k3_tarski(k2_tarski(sK1,sK0)) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_92805]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_3,plain,
% 51.85/7.00      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 51.85/7.00      inference(cnf_transformation,[],[f29]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_163,plain,
% 51.85/7.00      ( k2_tarski(X0_39,X1_39) = k2_tarski(X1_39,X0_39) ),
% 51.85/7.00      inference(subtyping,[status(esa)],[c_3]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_91595,plain,
% 51.85/7.00      ( k2_tarski(sK1,X0_39) = k2_tarski(X0_39,sK1) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_163]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_91596,plain,
% 51.85/7.00      ( k2_tarski(sK1,sK0) = k2_tarski(sK0,sK1) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_91595]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_174,plain,
% 51.85/7.00      ( X0_40 != X1_40 | k3_tarski(X0_40) = k3_tarski(X1_40) ),
% 51.85/7.00      theory(equality) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_1003,plain,
% 51.85/7.00      ( X0_40 != k2_tarski(X0_39,X1_39)
% 51.85/7.00      | k3_tarski(X0_40) = k3_tarski(k2_tarski(X0_39,X1_39)) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_174]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_1389,plain,
% 51.85/7.00      ( k2_tarski(X0_39,X1_39) != k2_tarski(X1_39,X0_39)
% 51.85/7.00      | k3_tarski(k2_tarski(X0_39,X1_39)) = k3_tarski(k2_tarski(X1_39,X0_39)) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_1003]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_30467,plain,
% 51.85/7.00      ( k2_tarski(sK1,X0_39) != k2_tarski(X0_39,sK1)
% 51.85/7.00      | k3_tarski(k2_tarski(sK1,X0_39)) = k3_tarski(k2_tarski(X0_39,sK1)) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_1389]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_30468,plain,
% 51.85/7.00      ( k2_tarski(sK1,sK0) != k2_tarski(sK0,sK1)
% 51.85/7.00      | k3_tarski(k2_tarski(sK1,sK0)) = k3_tarski(k2_tarski(sK0,sK1)) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_30467]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_176,plain,
% 51.85/7.00      ( ~ r1_tarski(X0_39,X1_39)
% 51.85/7.00      | r1_tarski(X2_39,X3_39)
% 51.85/7.00      | X2_39 != X0_39
% 51.85/7.00      | X3_39 != X1_39 ),
% 51.85/7.00      theory(equality) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_1619,plain,
% 51.85/7.00      ( r1_tarski(X0_39,X1_39)
% 51.85/7.00      | ~ r1_tarski(X2_39,k3_tarski(k2_tarski(X3_39,X4_39)))
% 51.85/7.00      | X0_39 != X2_39
% 51.85/7.00      | X1_39 != k3_tarski(k2_tarski(X3_39,X4_39)) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_176]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_2284,plain,
% 51.85/7.00      ( ~ r1_tarski(X0_39,k3_tarski(k2_tarski(X1_39,X2_39)))
% 51.85/7.00      | r1_tarski(X3_39,k3_tarski(k2_tarski(X1_39,k6_subset_1(X2_39,X1_39))))
% 51.85/7.00      | X3_39 != X0_39
% 51.85/7.00      | k3_tarski(k2_tarski(X1_39,k6_subset_1(X2_39,X1_39))) != k3_tarski(k2_tarski(X1_39,X2_39)) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_1619]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_30064,plain,
% 51.85/7.00      ( ~ r1_tarski(X0_39,k3_tarski(k2_tarski(sK1,X1_39)))
% 51.85/7.00      | r1_tarski(sK0,k3_tarski(k2_tarski(sK1,k6_subset_1(X1_39,sK1))))
% 51.85/7.00      | k3_tarski(k2_tarski(sK1,k6_subset_1(X1_39,sK1))) != k3_tarski(k2_tarski(sK1,X1_39))
% 51.85/7.00      | sK0 != X0_39 ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_2284]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_30066,plain,
% 51.85/7.00      ( r1_tarski(sK0,k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))))
% 51.85/7.00      | ~ r1_tarski(sK0,k3_tarski(k2_tarski(sK1,sK0)))
% 51.85/7.00      | k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1))) != k3_tarski(k2_tarski(sK1,sK0))
% 51.85/7.00      | sK0 != sK0 ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_30064]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_2075,plain,
% 51.85/7.00      ( r1_tarski(X0_39,X1_39)
% 51.85/7.00      | ~ r1_tarski(k2_relat_1(X2_39),k2_relat_1(k3_tarski(k2_tarski(X3_39,X4_39))))
% 51.85/7.00      | X0_39 != k2_relat_1(X2_39)
% 51.85/7.00      | X1_39 != k2_relat_1(k3_tarski(k2_tarski(X3_39,X4_39))) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_176]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_3363,plain,
% 51.85/7.00      ( r1_tarski(X0_39,k3_tarski(k2_tarski(k2_relat_1(X1_39),k2_relat_1(X2_39))))
% 51.85/7.00      | ~ r1_tarski(k2_relat_1(X3_39),k2_relat_1(k3_tarski(k2_tarski(X1_39,X2_39))))
% 51.85/7.00      | X0_39 != k2_relat_1(X3_39)
% 51.85/7.00      | k3_tarski(k2_tarski(k2_relat_1(X1_39),k2_relat_1(X2_39))) != k2_relat_1(k3_tarski(k2_tarski(X1_39,X2_39))) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_2075]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_7179,plain,
% 51.85/7.00      ( ~ r1_tarski(k2_relat_1(X0_39),k2_relat_1(k3_tarski(k2_tarski(X1_39,X2_39))))
% 51.85/7.00      | r1_tarski(k2_relat_1(X3_39),k3_tarski(k2_tarski(k2_relat_1(X1_39),k2_relat_1(X2_39))))
% 51.85/7.00      | k2_relat_1(X3_39) != k2_relat_1(X0_39)
% 51.85/7.00      | k3_tarski(k2_tarski(k2_relat_1(X1_39),k2_relat_1(X2_39))) != k2_relat_1(k3_tarski(k2_tarski(X1_39,X2_39))) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_3363]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_17233,plain,
% 51.85/7.00      ( ~ r1_tarski(k2_relat_1(X0_39),k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))))
% 51.85/7.00      | r1_tarski(k2_relat_1(sK0),k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))))
% 51.85/7.00      | k2_relat_1(sK0) != k2_relat_1(X0_39)
% 51.85/7.00      | k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_7179]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_17235,plain,
% 51.85/7.00      ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))))
% 51.85/7.00      | r1_tarski(k2_relat_1(sK0),k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))))
% 51.85/7.00      | k2_relat_1(sK0) != k2_relat_1(sK0)
% 51.85/7.00      | k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) != k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_17233]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_648,plain,
% 51.85/7.00      ( r1_tarski(X0_39,X1_39)
% 51.85/7.00      | ~ r1_tarski(X2_39,k3_tarski(k2_tarski(X2_39,X3_39)))
% 51.85/7.00      | X0_39 != X2_39
% 51.85/7.00      | X1_39 != k3_tarski(k2_tarski(X2_39,X3_39)) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_176]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_1002,plain,
% 51.85/7.00      ( r1_tarski(X0_39,k3_tarski(X0_40))
% 51.85/7.00      | ~ r1_tarski(X1_39,k3_tarski(k2_tarski(X1_39,X2_39)))
% 51.85/7.00      | X0_39 != X1_39
% 51.85/7.00      | k3_tarski(X0_40) != k3_tarski(k2_tarski(X1_39,X2_39)) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_648]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_2786,plain,
% 51.85/7.00      ( ~ r1_tarski(X0_39,k3_tarski(k2_tarski(X0_39,X1_39)))
% 51.85/7.00      | r1_tarski(X2_39,k3_tarski(k2_tarski(X1_39,X0_39)))
% 51.85/7.00      | X2_39 != X0_39
% 51.85/7.00      | k3_tarski(k2_tarski(X1_39,X0_39)) != k3_tarski(k2_tarski(X0_39,X1_39)) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_1002]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_11594,plain,
% 51.85/7.00      ( ~ r1_tarski(X0_39,k3_tarski(k2_tarski(X0_39,sK1)))
% 51.85/7.00      | r1_tarski(sK0,k3_tarski(k2_tarski(sK1,X0_39)))
% 51.85/7.00      | k3_tarski(k2_tarski(sK1,X0_39)) != k3_tarski(k2_tarski(X0_39,sK1))
% 51.85/7.00      | sK0 != X0_39 ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_2786]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_11596,plain,
% 51.85/7.00      ( r1_tarski(sK0,k3_tarski(k2_tarski(sK1,sK0)))
% 51.85/7.00      | ~ r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1)))
% 51.85/7.00      | k3_tarski(k2_tarski(sK1,sK0)) != k3_tarski(k2_tarski(sK0,sK1))
% 51.85/7.00      | sK0 != sK0 ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_11594]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_1,plain,
% 51.85/7.00      ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
% 51.85/7.00      | r1_tarski(k6_subset_1(X0,X1),X2) ),
% 51.85/7.00      inference(cnf_transformation,[],[f43]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_165,plain,
% 51.85/7.00      ( ~ r1_tarski(X0_39,k3_tarski(k2_tarski(X1_39,X2_39)))
% 51.85/7.00      | r1_tarski(k6_subset_1(X0_39,X1_39),X2_39) ),
% 51.85/7.00      inference(subtyping,[status(esa)],[c_1]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_6003,plain,
% 51.85/7.00      ( r1_tarski(k6_subset_1(sK0,sK1),X0_39)
% 51.85/7.00      | ~ r1_tarski(sK0,k3_tarski(k2_tarski(sK1,X0_39))) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_165]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_6005,plain,
% 51.85/7.00      ( r1_tarski(k6_subset_1(sK0,sK1),sK0)
% 51.85/7.00      | ~ r1_tarski(sK0,k3_tarski(k2_tarski(sK1,sK0))) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_6003]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_85,plain,
% 51.85/7.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 51.85/7.00      inference(prop_impl,[status(thm)],[c_4]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_86,plain,
% 51.85/7.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 51.85/7.00      inference(renaming,[status(thm)],[c_85]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_108,plain,
% 51.85/7.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 51.85/7.00      inference(bin_hyper_res,[status(thm)],[c_6,c_86]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_155,plain,
% 51.85/7.00      ( ~ r1_tarski(X0_39,X1_39)
% 51.85/7.00      | ~ v1_relat_1(X1_39)
% 51.85/7.00      | v1_relat_1(X0_39) ),
% 51.85/7.00      inference(subtyping,[status(esa)],[c_108]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_4195,plain,
% 51.85/7.00      ( ~ r1_tarski(k6_subset_1(sK0,sK1),X0_39)
% 51.85/7.00      | ~ v1_relat_1(X0_39)
% 51.85/7.00      | v1_relat_1(k6_subset_1(sK0,sK1)) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_155]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_4197,plain,
% 51.85/7.00      ( ~ r1_tarski(k6_subset_1(sK0,sK1),sK0)
% 51.85/7.00      | v1_relat_1(k6_subset_1(sK0,sK1))
% 51.85/7.00      | ~ v1_relat_1(sK0) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_4195]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_10,plain,
% 51.85/7.00      ( ~ v1_relat_1(X0)
% 51.85/7.00      | ~ v1_relat_1(X1)
% 51.85/7.00      | k3_tarski(k2_tarski(k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(k3_tarski(k2_tarski(X0,X1))) ),
% 51.85/7.00      inference(cnf_transformation,[],[f46]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_159,plain,
% 51.85/7.00      ( ~ v1_relat_1(X0_39)
% 51.85/7.00      | ~ v1_relat_1(X1_39)
% 51.85/7.00      | k3_tarski(k2_tarski(k2_relat_1(X0_39),k2_relat_1(X1_39))) = k2_relat_1(k3_tarski(k2_tarski(X0_39,X1_39))) ),
% 51.85/7.00      inference(subtyping,[status(esa)],[c_10]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_2663,plain,
% 51.85/7.00      ( ~ v1_relat_1(k6_subset_1(sK0,sK1))
% 51.85/7.00      | ~ v1_relat_1(sK1)
% 51.85/7.00      | k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) = k2_relat_1(k3_tarski(k2_tarski(sK1,k6_subset_1(sK0,sK1)))) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_159]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_630,plain,
% 51.85/7.00      ( r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))
% 51.85/7.00      | ~ r1_tarski(k2_relat_1(sK0),k3_tarski(k2_tarski(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))))) ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_165]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_168,plain,( X0_39 = X0_39 ),theory(equality) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_188,plain,
% 51.85/7.00      ( sK0 = sK0 ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_168]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_179,plain,
% 51.85/7.00      ( X0_39 != X1_39 | k2_relat_1(X0_39) = k2_relat_1(X1_39) ),
% 51.85/7.00      theory(equality) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_186,plain,
% 51.85/7.00      ( k2_relat_1(sK0) = k2_relat_1(sK0) | sK0 != sK0 ),
% 51.85/7.00      inference(instantiation,[status(thm)],[c_179]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_11,negated_conjecture,
% 51.85/7.00      ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
% 51.85/7.00      inference(cnf_transformation,[],[f41]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_12,negated_conjecture,
% 51.85/7.00      ( v1_relat_1(sK1) ),
% 51.85/7.00      inference(cnf_transformation,[],[f40]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(c_13,negated_conjecture,
% 51.85/7.00      ( v1_relat_1(sK0) ),
% 51.85/7.00      inference(cnf_transformation,[],[f39]) ).
% 51.85/7.00  
% 51.85/7.00  cnf(contradiction,plain,
% 51.85/7.00      ( $false ),
% 51.85/7.00      inference(minisat,
% 51.85/7.00                [status(thm)],
% 51.85/7.00                [c_219890,c_217267,c_93397,c_92806,c_91596,c_30468,
% 51.85/7.00                 c_30066,c_17235,c_11596,c_6005,c_4197,c_2663,c_630,
% 51.85/7.00                 c_188,c_186,c_11,c_12,c_13]) ).
% 51.85/7.00  
% 51.85/7.00  
% 51.85/7.00  % SZS output end CNFRefutation for theBenchmark.p
% 51.85/7.00  
% 51.85/7.00  ------                               Statistics
% 51.85/7.00  
% 51.85/7.00  ------ Selected
% 51.85/7.00  
% 51.85/7.00  total_time:                             6.412
% 51.85/7.00  
%------------------------------------------------------------------------------
