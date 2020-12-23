%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:59 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 190 expanded)
%              Number of clauses        :   76 (  87 expanded)
%              Number of leaves         :   20 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  300 ( 411 expanded)
%              Number of equality atoms :   93 ( 122 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f49])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f49])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f34,f49])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f30])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X0] :
      ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f41,f49])).

fof(f48,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f48,f49])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_355,plain,
    ( ~ r1_tarski(X0_44,X1_44)
    | r1_tarski(X0_44,k3_tarski(k1_enumset1(X2_44,X2_44,X1_44))) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2008,plain,
    ( r1_tarski(X0_44,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | ~ r1_tarski(X0_44,sK1) ),
    inference(instantiation,[status(thm)],[c_355])).

cnf(c_11394,plain,
    ( r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | ~ r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_2008])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_352,plain,
    ( ~ r1_tarski(X0_44,X1_44)
    | ~ r1_tarski(X2_44,X1_44)
    | r1_tarski(k3_tarski(k1_enumset1(X0_44,X0_44,X2_44)),X1_44) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_705,plain,
    ( ~ r1_tarski(X0_44,k3_tarski(k1_enumset1(X1_44,X1_44,X2_44)))
    | ~ r1_tarski(X3_44,k3_tarski(k1_enumset1(X1_44,X1_44,X2_44)))
    | r1_tarski(k3_tarski(k1_enumset1(X0_44,X0_44,X3_44)),k3_tarski(k1_enumset1(X1_44,X1_44,X2_44))) ),
    inference(instantiation,[status(thm)],[c_352])).

cnf(c_2024,plain,
    ( ~ r1_tarski(X0_44,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | ~ r1_tarski(X1_44,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | r1_tarski(k3_tarski(k1_enumset1(X0_44,X0_44,X1_44)),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_5174,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | ~ r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_2024])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_354,plain,
    ( ~ r1_tarski(X0_44,X1_44)
    | ~ r1_tarski(X1_44,X2_44)
    | r1_tarski(X0_44,X2_44) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1518,plain,
    ( ~ r1_tarski(X0_44,X1_44)
    | ~ r1_tarski(k1_relat_1(X0_45),X0_44)
    | r1_tarski(k1_relat_1(X0_45),X1_44) ),
    inference(instantiation,[status(thm)],[c_354])).

cnf(c_4947,plain,
    ( ~ r1_tarski(X0_44,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | ~ r1_tarski(k1_relat_1(X0_45),X0_44)
    | r1_tarski(k1_relat_1(X0_45),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_1518])).

cnf(c_4949,plain,
    ( r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_4947])).

cnf(c_366,plain,
    ( ~ r1_tarski(X0_44,X1_44)
    | r1_tarski(X2_44,X3_44)
    | X2_44 != X0_44
    | X3_44 != X1_44 ),
    theory(equality)).

cnf(c_713,plain,
    ( r1_tarski(X0_44,X1_44)
    | ~ r1_tarski(X2_44,k3_tarski(k1_enumset1(X3_44,X3_44,X4_44)))
    | X0_44 != X2_44
    | X1_44 != k3_tarski(k1_enumset1(X3_44,X3_44,X4_44)) ),
    inference(instantiation,[status(thm)],[c_366])).

cnf(c_853,plain,
    ( ~ r1_tarski(X0_44,k3_tarski(k1_enumset1(X1_44,X1_44,X2_44)))
    | r1_tarski(X3_44,k3_tarski(k1_enumset1(X1_44,X1_44,X2_44)))
    | X3_44 != X0_44
    | k3_tarski(k1_enumset1(X1_44,X1_44,X2_44)) != k3_tarski(k1_enumset1(X1_44,X1_44,X2_44)) ),
    inference(instantiation,[status(thm)],[c_713])).

cnf(c_1620,plain,
    ( ~ r1_tarski(X0_44,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | k3_relat_1(sK2) != X0_44
    | k3_tarski(k1_enumset1(sK0,sK0,sK1)) != k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_853])).

cnf(c_3272,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | ~ r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | k3_relat_1(sK2) != k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2)))
    | k3_tarski(k1_enumset1(sK0,sK0,sK1)) != k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1620])).

cnf(c_2,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_353,plain,
    ( r1_tarski(X0_44,k3_tarski(k1_enumset1(X0_44,X0_44,X1_44))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1950,plain,
    ( r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_353])).

cnf(c_357,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_789,plain,
    ( k3_tarski(k1_enumset1(X0_44,X0_44,X1_44)) = k3_tarski(k1_enumset1(X0_44,X0_44,X1_44)) ),
    inference(instantiation,[status(thm)],[c_357])).

cnf(c_1867,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_789])).

cnf(c_361,plain,
    ( X0_44 != X1_44
    | X2_44 != X1_44
    | X2_44 = X0_44 ),
    theory(equality)).

cnf(c_793,plain,
    ( X0_44 != X1_44
    | X0_44 = k3_tarski(k1_enumset1(X2_44,X2_44,X3_44))
    | k3_tarski(k1_enumset1(X2_44,X2_44,X3_44)) != X1_44 ),
    inference(instantiation,[status(thm)],[c_361])).

cnf(c_1116,plain,
    ( X0_44 != k3_relat_1(X0_45)
    | X0_44 = k3_tarski(k1_enumset1(k1_relat_1(X0_45),k1_relat_1(X0_45),k2_relat_1(X0_45)))
    | k3_tarski(k1_enumset1(k1_relat_1(X0_45),k1_relat_1(X0_45),k2_relat_1(X0_45))) != k3_relat_1(X0_45) ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_1398,plain,
    ( k3_relat_1(X0_45) != k3_relat_1(X0_45)
    | k3_relat_1(X0_45) = k3_tarski(k1_enumset1(k1_relat_1(X0_45),k1_relat_1(X0_45),k2_relat_1(X0_45)))
    | k3_tarski(k1_enumset1(k1_relat_1(X0_45),k1_relat_1(X0_45),k2_relat_1(X0_45))) != k3_relat_1(X0_45) ),
    inference(instantiation,[status(thm)],[c_1116])).

cnf(c_1400,plain,
    ( k3_relat_1(sK2) != k3_relat_1(sK2)
    | k3_relat_1(sK2) = k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2)))
    | k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))) != k3_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1398])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_350,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_44,X1_44)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_588,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_44,X1_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_350])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_190,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_14])).

cnf(c_191,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_190])).

cnf(c_347,plain,
    ( ~ v1_relat_1(X0_45)
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_191])).

cnf(c_591,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0_45)
    | v1_relat_1(X0_45) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_347])).

cnf(c_682,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_591])).

cnf(c_837,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_588,c_682])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_172,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_12,c_9])).

cnf(c_217,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_172,c_14])).

cnf(c_218,plain,
    ( ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,X0) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_346,plain,
    ( ~ v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k7_relat_1(sK2,X0_44) = sK2 ),
    inference(subtyping,[status(esa)],[c_218])).

cnf(c_592,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k7_relat_1(sK2,X0_44) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_720,plain,
    ( k7_relat_1(sK2,sK0) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_592])).

cnf(c_1144,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(superposition,[status(thm)],[c_837,c_720])).

cnf(c_10,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_349,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_45,X0_44)),X0_44)
    | ~ v1_relat_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_589,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_45,X0_44)),X0_44) = iProver_top
    | v1_relat_1(X0_45) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_349])).

cnf(c_1151,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1144,c_589])).

cnf(c_1152,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1151])).

cnf(c_826,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_6,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_11,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_205,plain,
    ( v5_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_14])).

cnf(c_206,plain,
    ( v5_relat_1(sK2,X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_205])).

cnf(c_244,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_zfmisc_1(k2_zfmisc_1(X3,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_206])).

cnf(c_245,plain,
    ( r1_tarski(k2_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_244])).

cnf(c_345,plain,
    ( r1_tarski(k2_relat_1(sK2),X0_44)
    | ~ v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X1_44,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(subtyping,[status(esa)],[c_245])).

cnf(c_593,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | r1_tarski(k2_relat_1(sK2),X1_44) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_345])).

cnf(c_737,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_593])).

cnf(c_738,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_737])).

cnf(c_683,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_682])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_351,plain,
    ( ~ v1_relat_1(X0_45)
    | k3_tarski(k1_enumset1(k1_relat_1(X0_45),k1_relat_1(X0_45),k2_relat_1(X0_45))) = k3_relat_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_394,plain,
    ( ~ v1_relat_1(sK2)
    | k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))) = k3_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_358,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_386,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_358])).

cnf(c_371,plain,
    ( X0_45 != X1_45
    | k3_relat_1(X0_45) = k3_relat_1(X1_45) ),
    theory(equality)).

cnf(c_381,plain,
    ( sK2 != sK2
    | k3_relat_1(sK2) = k3_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_371])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11394,c_5174,c_4949,c_3272,c_1950,c_1867,c_1400,c_1152,c_826,c_738,c_683,c_394,c_386,c_381,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:09:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.29/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.01  
% 3.29/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.29/1.01  
% 3.29/1.01  ------  iProver source info
% 3.29/1.01  
% 3.29/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.29/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.29/1.01  git: non_committed_changes: false
% 3.29/1.01  git: last_make_outside_of_git: false
% 3.29/1.01  
% 3.29/1.01  ------ 
% 3.29/1.01  
% 3.29/1.01  ------ Input Options
% 3.29/1.01  
% 3.29/1.01  --out_options                           all
% 3.29/1.01  --tptp_safe_out                         true
% 3.29/1.01  --problem_path                          ""
% 3.29/1.01  --include_path                          ""
% 3.29/1.01  --clausifier                            res/vclausify_rel
% 3.29/1.01  --clausifier_options                    --mode clausify
% 3.29/1.01  --stdin                                 false
% 3.29/1.01  --stats_out                             all
% 3.29/1.01  
% 3.29/1.01  ------ General Options
% 3.29/1.01  
% 3.29/1.01  --fof                                   false
% 3.29/1.01  --time_out_real                         305.
% 3.29/1.01  --time_out_virtual                      -1.
% 3.29/1.01  --symbol_type_check                     false
% 3.29/1.01  --clausify_out                          false
% 3.29/1.01  --sig_cnt_out                           false
% 3.29/1.01  --trig_cnt_out                          false
% 3.29/1.01  --trig_cnt_out_tolerance                1.
% 3.29/1.01  --trig_cnt_out_sk_spl                   false
% 3.29/1.01  --abstr_cl_out                          false
% 3.29/1.01  
% 3.29/1.01  ------ Global Options
% 3.29/1.01  
% 3.29/1.01  --schedule                              default
% 3.29/1.01  --add_important_lit                     false
% 3.29/1.01  --prop_solver_per_cl                    1000
% 3.29/1.01  --min_unsat_core                        false
% 3.29/1.01  --soft_assumptions                      false
% 3.29/1.01  --soft_lemma_size                       3
% 3.29/1.01  --prop_impl_unit_size                   0
% 3.29/1.01  --prop_impl_unit                        []
% 3.29/1.01  --share_sel_clauses                     true
% 3.29/1.01  --reset_solvers                         false
% 3.29/1.01  --bc_imp_inh                            [conj_cone]
% 3.29/1.01  --conj_cone_tolerance                   3.
% 3.29/1.01  --extra_neg_conj                        none
% 3.29/1.01  --large_theory_mode                     true
% 3.29/1.01  --prolific_symb_bound                   200
% 3.29/1.01  --lt_threshold                          2000
% 3.29/1.01  --clause_weak_htbl                      true
% 3.29/1.01  --gc_record_bc_elim                     false
% 3.29/1.01  
% 3.29/1.01  ------ Preprocessing Options
% 3.29/1.01  
% 3.29/1.01  --preprocessing_flag                    true
% 3.29/1.01  --time_out_prep_mult                    0.1
% 3.29/1.01  --splitting_mode                        input
% 3.29/1.01  --splitting_grd                         true
% 3.29/1.01  --splitting_cvd                         false
% 3.29/1.01  --splitting_cvd_svl                     false
% 3.29/1.01  --splitting_nvd                         32
% 3.29/1.01  --sub_typing                            true
% 3.29/1.01  --prep_gs_sim                           true
% 3.29/1.01  --prep_unflatten                        true
% 3.29/1.01  --prep_res_sim                          true
% 3.29/1.01  --prep_upred                            true
% 3.29/1.01  --prep_sem_filter                       exhaustive
% 3.29/1.01  --prep_sem_filter_out                   false
% 3.29/1.01  --pred_elim                             true
% 3.29/1.01  --res_sim_input                         true
% 3.29/1.01  --eq_ax_congr_red                       true
% 3.29/1.01  --pure_diseq_elim                       true
% 3.29/1.01  --brand_transform                       false
% 3.29/1.01  --non_eq_to_eq                          false
% 3.29/1.01  --prep_def_merge                        true
% 3.29/1.01  --prep_def_merge_prop_impl              false
% 3.29/1.01  --prep_def_merge_mbd                    true
% 3.29/1.01  --prep_def_merge_tr_red                 false
% 3.29/1.01  --prep_def_merge_tr_cl                  false
% 3.29/1.01  --smt_preprocessing                     true
% 3.29/1.01  --smt_ac_axioms                         fast
% 3.29/1.01  --preprocessed_out                      false
% 3.29/1.01  --preprocessed_stats                    false
% 3.29/1.01  
% 3.29/1.01  ------ Abstraction refinement Options
% 3.29/1.01  
% 3.29/1.01  --abstr_ref                             []
% 3.29/1.01  --abstr_ref_prep                        false
% 3.29/1.01  --abstr_ref_until_sat                   false
% 3.29/1.01  --abstr_ref_sig_restrict                funpre
% 3.29/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.29/1.01  --abstr_ref_under                       []
% 3.29/1.01  
% 3.29/1.01  ------ SAT Options
% 3.29/1.01  
% 3.29/1.01  --sat_mode                              false
% 3.29/1.01  --sat_fm_restart_options                ""
% 3.29/1.01  --sat_gr_def                            false
% 3.29/1.01  --sat_epr_types                         true
% 3.29/1.01  --sat_non_cyclic_types                  false
% 3.29/1.01  --sat_finite_models                     false
% 3.29/1.01  --sat_fm_lemmas                         false
% 3.29/1.01  --sat_fm_prep                           false
% 3.29/1.01  --sat_fm_uc_incr                        true
% 3.29/1.01  --sat_out_model                         small
% 3.29/1.01  --sat_out_clauses                       false
% 3.29/1.01  
% 3.29/1.01  ------ QBF Options
% 3.29/1.01  
% 3.29/1.01  --qbf_mode                              false
% 3.29/1.01  --qbf_elim_univ                         false
% 3.29/1.01  --qbf_dom_inst                          none
% 3.29/1.01  --qbf_dom_pre_inst                      false
% 3.29/1.01  --qbf_sk_in                             false
% 3.29/1.01  --qbf_pred_elim                         true
% 3.29/1.01  --qbf_split                             512
% 3.29/1.01  
% 3.29/1.01  ------ BMC1 Options
% 3.29/1.01  
% 3.29/1.01  --bmc1_incremental                      false
% 3.29/1.01  --bmc1_axioms                           reachable_all
% 3.29/1.01  --bmc1_min_bound                        0
% 3.29/1.01  --bmc1_max_bound                        -1
% 3.29/1.01  --bmc1_max_bound_default                -1
% 3.29/1.01  --bmc1_symbol_reachability              true
% 3.29/1.01  --bmc1_property_lemmas                  false
% 3.29/1.01  --bmc1_k_induction                      false
% 3.29/1.01  --bmc1_non_equiv_states                 false
% 3.29/1.01  --bmc1_deadlock                         false
% 3.29/1.01  --bmc1_ucm                              false
% 3.29/1.01  --bmc1_add_unsat_core                   none
% 3.29/1.01  --bmc1_unsat_core_children              false
% 3.29/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.29/1.01  --bmc1_out_stat                         full
% 3.29/1.01  --bmc1_ground_init                      false
% 3.29/1.01  --bmc1_pre_inst_next_state              false
% 3.29/1.01  --bmc1_pre_inst_state                   false
% 3.29/1.01  --bmc1_pre_inst_reach_state             false
% 3.29/1.01  --bmc1_out_unsat_core                   false
% 3.29/1.01  --bmc1_aig_witness_out                  false
% 3.29/1.01  --bmc1_verbose                          false
% 3.29/1.01  --bmc1_dump_clauses_tptp                false
% 3.29/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.29/1.01  --bmc1_dump_file                        -
% 3.29/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.29/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.29/1.01  --bmc1_ucm_extend_mode                  1
% 3.29/1.01  --bmc1_ucm_init_mode                    2
% 3.29/1.01  --bmc1_ucm_cone_mode                    none
% 3.29/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.29/1.01  --bmc1_ucm_relax_model                  4
% 3.29/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.29/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.29/1.01  --bmc1_ucm_layered_model                none
% 3.29/1.01  --bmc1_ucm_max_lemma_size               10
% 3.29/1.01  
% 3.29/1.01  ------ AIG Options
% 3.29/1.01  
% 3.29/1.01  --aig_mode                              false
% 3.29/1.01  
% 3.29/1.01  ------ Instantiation Options
% 3.29/1.01  
% 3.29/1.01  --instantiation_flag                    true
% 3.29/1.01  --inst_sos_flag                         false
% 3.29/1.01  --inst_sos_phase                        true
% 3.29/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.29/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.29/1.01  --inst_lit_sel_side                     num_symb
% 3.29/1.01  --inst_solver_per_active                1400
% 3.29/1.01  --inst_solver_calls_frac                1.
% 3.29/1.01  --inst_passive_queue_type               priority_queues
% 3.29/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.29/1.01  --inst_passive_queues_freq              [25;2]
% 3.29/1.01  --inst_dismatching                      true
% 3.29/1.01  --inst_eager_unprocessed_to_passive     true
% 3.29/1.01  --inst_prop_sim_given                   true
% 3.29/1.01  --inst_prop_sim_new                     false
% 3.29/1.01  --inst_subs_new                         false
% 3.29/1.01  --inst_eq_res_simp                      false
% 3.29/1.01  --inst_subs_given                       false
% 3.29/1.01  --inst_orphan_elimination               true
% 3.29/1.01  --inst_learning_loop_flag               true
% 3.29/1.01  --inst_learning_start                   3000
% 3.29/1.01  --inst_learning_factor                  2
% 3.29/1.01  --inst_start_prop_sim_after_learn       3
% 3.29/1.01  --inst_sel_renew                        solver
% 3.29/1.01  --inst_lit_activity_flag                true
% 3.29/1.01  --inst_restr_to_given                   false
% 3.29/1.01  --inst_activity_threshold               500
% 3.29/1.01  --inst_out_proof                        true
% 3.29/1.01  
% 3.29/1.01  ------ Resolution Options
% 3.29/1.01  
% 3.29/1.01  --resolution_flag                       true
% 3.29/1.01  --res_lit_sel                           adaptive
% 3.29/1.01  --res_lit_sel_side                      none
% 3.29/1.01  --res_ordering                          kbo
% 3.29/1.01  --res_to_prop_solver                    active
% 3.29/1.01  --res_prop_simpl_new                    false
% 3.29/1.01  --res_prop_simpl_given                  true
% 3.29/1.01  --res_passive_queue_type                priority_queues
% 3.29/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.29/1.01  --res_passive_queues_freq               [15;5]
% 3.29/1.01  --res_forward_subs                      full
% 3.29/1.01  --res_backward_subs                     full
% 3.29/1.01  --res_forward_subs_resolution           true
% 3.29/1.01  --res_backward_subs_resolution          true
% 3.29/1.01  --res_orphan_elimination                true
% 3.29/1.01  --res_time_limit                        2.
% 3.29/1.01  --res_out_proof                         true
% 3.29/1.01  
% 3.29/1.01  ------ Superposition Options
% 3.29/1.01  
% 3.29/1.01  --superposition_flag                    true
% 3.29/1.01  --sup_passive_queue_type                priority_queues
% 3.29/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.29/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.29/1.01  --demod_completeness_check              fast
% 3.29/1.01  --demod_use_ground                      true
% 3.29/1.01  --sup_to_prop_solver                    passive
% 3.29/1.01  --sup_prop_simpl_new                    true
% 3.29/1.01  --sup_prop_simpl_given                  true
% 3.29/1.01  --sup_fun_splitting                     false
% 3.29/1.01  --sup_smt_interval                      50000
% 3.29/1.01  
% 3.29/1.01  ------ Superposition Simplification Setup
% 3.29/1.01  
% 3.29/1.01  --sup_indices_passive                   []
% 3.29/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.29/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/1.01  --sup_full_bw                           [BwDemod]
% 3.29/1.01  --sup_immed_triv                        [TrivRules]
% 3.29/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.29/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/1.01  --sup_immed_bw_main                     []
% 3.29/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.29/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/1.01  
% 3.29/1.01  ------ Combination Options
% 3.29/1.01  
% 3.29/1.01  --comb_res_mult                         3
% 3.29/1.01  --comb_sup_mult                         2
% 3.29/1.01  --comb_inst_mult                        10
% 3.29/1.01  
% 3.29/1.01  ------ Debug Options
% 3.29/1.01  
% 3.29/1.01  --dbg_backtrace                         false
% 3.29/1.01  --dbg_dump_prop_clauses                 false
% 3.29/1.01  --dbg_dump_prop_clauses_file            -
% 3.29/1.01  --dbg_out_stat                          false
% 3.29/1.01  ------ Parsing...
% 3.29/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.29/1.01  
% 3.29/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.29/1.01  
% 3.29/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.29/1.01  
% 3.29/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.29/1.01  ------ Proving...
% 3.29/1.01  ------ Problem Properties 
% 3.29/1.01  
% 3.29/1.01  
% 3.29/1.01  clauses                                 11
% 3.29/1.01  conjectures                             1
% 3.29/1.01  EPR                                     1
% 3.29/1.01  Horn                                    11
% 3.29/1.01  unary                                   3
% 3.29/1.01  binary                                  3
% 3.29/1.01  lits                                    24
% 3.29/1.01  lits eq                                 5
% 3.29/1.01  fd_pure                                 0
% 3.29/1.01  fd_pseudo                               0
% 3.29/1.01  fd_cond                                 0
% 3.29/1.01  fd_pseudo_cond                          0
% 3.29/1.01  AC symbols                              0
% 3.29/1.01  
% 3.29/1.01  ------ Schedule dynamic 5 is on 
% 3.29/1.01  
% 3.29/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.29/1.01  
% 3.29/1.01  
% 3.29/1.01  ------ 
% 3.29/1.01  Current options:
% 3.29/1.01  ------ 
% 3.29/1.01  
% 3.29/1.01  ------ Input Options
% 3.29/1.01  
% 3.29/1.01  --out_options                           all
% 3.29/1.01  --tptp_safe_out                         true
% 3.29/1.01  --problem_path                          ""
% 3.29/1.01  --include_path                          ""
% 3.29/1.01  --clausifier                            res/vclausify_rel
% 3.29/1.01  --clausifier_options                    --mode clausify
% 3.29/1.01  --stdin                                 false
% 3.29/1.01  --stats_out                             all
% 3.29/1.01  
% 3.29/1.01  ------ General Options
% 3.29/1.01  
% 3.29/1.01  --fof                                   false
% 3.29/1.01  --time_out_real                         305.
% 3.29/1.01  --time_out_virtual                      -1.
% 3.29/1.01  --symbol_type_check                     false
% 3.29/1.01  --clausify_out                          false
% 3.29/1.01  --sig_cnt_out                           false
% 3.29/1.01  --trig_cnt_out                          false
% 3.29/1.01  --trig_cnt_out_tolerance                1.
% 3.29/1.01  --trig_cnt_out_sk_spl                   false
% 3.29/1.01  --abstr_cl_out                          false
% 3.29/1.01  
% 3.29/1.01  ------ Global Options
% 3.29/1.01  
% 3.29/1.01  --schedule                              default
% 3.29/1.01  --add_important_lit                     false
% 3.29/1.01  --prop_solver_per_cl                    1000
% 3.29/1.01  --min_unsat_core                        false
% 3.29/1.01  --soft_assumptions                      false
% 3.29/1.01  --soft_lemma_size                       3
% 3.29/1.01  --prop_impl_unit_size                   0
% 3.29/1.01  --prop_impl_unit                        []
% 3.29/1.01  --share_sel_clauses                     true
% 3.29/1.01  --reset_solvers                         false
% 3.29/1.01  --bc_imp_inh                            [conj_cone]
% 3.29/1.01  --conj_cone_tolerance                   3.
% 3.29/1.01  --extra_neg_conj                        none
% 3.29/1.01  --large_theory_mode                     true
% 3.29/1.01  --prolific_symb_bound                   200
% 3.29/1.01  --lt_threshold                          2000
% 3.29/1.01  --clause_weak_htbl                      true
% 3.29/1.01  --gc_record_bc_elim                     false
% 3.29/1.01  
% 3.29/1.01  ------ Preprocessing Options
% 3.29/1.01  
% 3.29/1.01  --preprocessing_flag                    true
% 3.29/1.01  --time_out_prep_mult                    0.1
% 3.29/1.01  --splitting_mode                        input
% 3.29/1.01  --splitting_grd                         true
% 3.29/1.01  --splitting_cvd                         false
% 3.29/1.01  --splitting_cvd_svl                     false
% 3.29/1.01  --splitting_nvd                         32
% 3.29/1.01  --sub_typing                            true
% 3.29/1.01  --prep_gs_sim                           true
% 3.29/1.01  --prep_unflatten                        true
% 3.29/1.01  --prep_res_sim                          true
% 3.29/1.01  --prep_upred                            true
% 3.29/1.01  --prep_sem_filter                       exhaustive
% 3.29/1.01  --prep_sem_filter_out                   false
% 3.29/1.01  --pred_elim                             true
% 3.29/1.01  --res_sim_input                         true
% 3.29/1.01  --eq_ax_congr_red                       true
% 3.29/1.01  --pure_diseq_elim                       true
% 3.29/1.01  --brand_transform                       false
% 3.29/1.01  --non_eq_to_eq                          false
% 3.29/1.01  --prep_def_merge                        true
% 3.29/1.01  --prep_def_merge_prop_impl              false
% 3.29/1.01  --prep_def_merge_mbd                    true
% 3.29/1.01  --prep_def_merge_tr_red                 false
% 3.29/1.01  --prep_def_merge_tr_cl                  false
% 3.29/1.01  --smt_preprocessing                     true
% 3.29/1.01  --smt_ac_axioms                         fast
% 3.29/1.01  --preprocessed_out                      false
% 3.29/1.01  --preprocessed_stats                    false
% 3.29/1.01  
% 3.29/1.01  ------ Abstraction refinement Options
% 3.29/1.01  
% 3.29/1.01  --abstr_ref                             []
% 3.29/1.01  --abstr_ref_prep                        false
% 3.29/1.01  --abstr_ref_until_sat                   false
% 3.29/1.01  --abstr_ref_sig_restrict                funpre
% 3.29/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.29/1.01  --abstr_ref_under                       []
% 3.29/1.01  
% 3.29/1.01  ------ SAT Options
% 3.29/1.01  
% 3.29/1.01  --sat_mode                              false
% 3.29/1.01  --sat_fm_restart_options                ""
% 3.29/1.01  --sat_gr_def                            false
% 3.29/1.01  --sat_epr_types                         true
% 3.29/1.01  --sat_non_cyclic_types                  false
% 3.29/1.01  --sat_finite_models                     false
% 3.29/1.01  --sat_fm_lemmas                         false
% 3.29/1.01  --sat_fm_prep                           false
% 3.29/1.01  --sat_fm_uc_incr                        true
% 3.29/1.01  --sat_out_model                         small
% 3.29/1.01  --sat_out_clauses                       false
% 3.29/1.01  
% 3.29/1.01  ------ QBF Options
% 3.29/1.01  
% 3.29/1.01  --qbf_mode                              false
% 3.29/1.01  --qbf_elim_univ                         false
% 3.29/1.01  --qbf_dom_inst                          none
% 3.29/1.01  --qbf_dom_pre_inst                      false
% 3.29/1.01  --qbf_sk_in                             false
% 3.29/1.01  --qbf_pred_elim                         true
% 3.29/1.01  --qbf_split                             512
% 3.29/1.01  
% 3.29/1.01  ------ BMC1 Options
% 3.29/1.01  
% 3.29/1.01  --bmc1_incremental                      false
% 3.29/1.01  --bmc1_axioms                           reachable_all
% 3.29/1.01  --bmc1_min_bound                        0
% 3.29/1.01  --bmc1_max_bound                        -1
% 3.29/1.01  --bmc1_max_bound_default                -1
% 3.29/1.01  --bmc1_symbol_reachability              true
% 3.29/1.01  --bmc1_property_lemmas                  false
% 3.29/1.01  --bmc1_k_induction                      false
% 3.29/1.01  --bmc1_non_equiv_states                 false
% 3.29/1.01  --bmc1_deadlock                         false
% 3.29/1.01  --bmc1_ucm                              false
% 3.29/1.01  --bmc1_add_unsat_core                   none
% 3.29/1.01  --bmc1_unsat_core_children              false
% 3.29/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.29/1.01  --bmc1_out_stat                         full
% 3.29/1.01  --bmc1_ground_init                      false
% 3.29/1.01  --bmc1_pre_inst_next_state              false
% 3.29/1.01  --bmc1_pre_inst_state                   false
% 3.29/1.01  --bmc1_pre_inst_reach_state             false
% 3.29/1.01  --bmc1_out_unsat_core                   false
% 3.29/1.01  --bmc1_aig_witness_out                  false
% 3.29/1.01  --bmc1_verbose                          false
% 3.29/1.01  --bmc1_dump_clauses_tptp                false
% 3.29/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.29/1.01  --bmc1_dump_file                        -
% 3.29/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.29/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.29/1.01  --bmc1_ucm_extend_mode                  1
% 3.29/1.01  --bmc1_ucm_init_mode                    2
% 3.29/1.01  --bmc1_ucm_cone_mode                    none
% 3.29/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.29/1.01  --bmc1_ucm_relax_model                  4
% 3.29/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.29/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.29/1.01  --bmc1_ucm_layered_model                none
% 3.29/1.01  --bmc1_ucm_max_lemma_size               10
% 3.29/1.01  
% 3.29/1.01  ------ AIG Options
% 3.29/1.01  
% 3.29/1.01  --aig_mode                              false
% 3.29/1.01  
% 3.29/1.01  ------ Instantiation Options
% 3.29/1.01  
% 3.29/1.01  --instantiation_flag                    true
% 3.29/1.01  --inst_sos_flag                         false
% 3.29/1.01  --inst_sos_phase                        true
% 3.29/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.29/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.29/1.01  --inst_lit_sel_side                     none
% 3.29/1.01  --inst_solver_per_active                1400
% 3.29/1.01  --inst_solver_calls_frac                1.
% 3.29/1.01  --inst_passive_queue_type               priority_queues
% 3.29/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.29/1.01  --inst_passive_queues_freq              [25;2]
% 3.29/1.01  --inst_dismatching                      true
% 3.29/1.01  --inst_eager_unprocessed_to_passive     true
% 3.29/1.01  --inst_prop_sim_given                   true
% 3.29/1.01  --inst_prop_sim_new                     false
% 3.29/1.01  --inst_subs_new                         false
% 3.29/1.01  --inst_eq_res_simp                      false
% 3.29/1.01  --inst_subs_given                       false
% 3.29/1.01  --inst_orphan_elimination               true
% 3.29/1.01  --inst_learning_loop_flag               true
% 3.29/1.01  --inst_learning_start                   3000
% 3.29/1.01  --inst_learning_factor                  2
% 3.29/1.01  --inst_start_prop_sim_after_learn       3
% 3.29/1.01  --inst_sel_renew                        solver
% 3.29/1.01  --inst_lit_activity_flag                true
% 3.29/1.01  --inst_restr_to_given                   false
% 3.29/1.01  --inst_activity_threshold               500
% 3.29/1.01  --inst_out_proof                        true
% 3.29/1.01  
% 3.29/1.01  ------ Resolution Options
% 3.29/1.01  
% 3.29/1.01  --resolution_flag                       false
% 3.29/1.01  --res_lit_sel                           adaptive
% 3.29/1.01  --res_lit_sel_side                      none
% 3.29/1.01  --res_ordering                          kbo
% 3.29/1.01  --res_to_prop_solver                    active
% 3.29/1.01  --res_prop_simpl_new                    false
% 3.29/1.01  --res_prop_simpl_given                  true
% 3.29/1.01  --res_passive_queue_type                priority_queues
% 3.29/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.29/1.01  --res_passive_queues_freq               [15;5]
% 3.29/1.01  --res_forward_subs                      full
% 3.29/1.01  --res_backward_subs                     full
% 3.29/1.01  --res_forward_subs_resolution           true
% 3.29/1.01  --res_backward_subs_resolution          true
% 3.29/1.01  --res_orphan_elimination                true
% 3.29/1.01  --res_time_limit                        2.
% 3.29/1.01  --res_out_proof                         true
% 3.29/1.01  
% 3.29/1.01  ------ Superposition Options
% 3.29/1.01  
% 3.29/1.01  --superposition_flag                    true
% 3.29/1.01  --sup_passive_queue_type                priority_queues
% 3.29/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.29/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.29/1.01  --demod_completeness_check              fast
% 3.29/1.01  --demod_use_ground                      true
% 3.29/1.01  --sup_to_prop_solver                    passive
% 3.29/1.01  --sup_prop_simpl_new                    true
% 3.29/1.01  --sup_prop_simpl_given                  true
% 3.29/1.01  --sup_fun_splitting                     false
% 3.29/1.01  --sup_smt_interval                      50000
% 3.29/1.01  
% 3.29/1.01  ------ Superposition Simplification Setup
% 3.29/1.01  
% 3.29/1.01  --sup_indices_passive                   []
% 3.29/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.29/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.29/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/1.01  --sup_full_bw                           [BwDemod]
% 3.29/1.01  --sup_immed_triv                        [TrivRules]
% 3.29/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.29/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/1.01  --sup_immed_bw_main                     []
% 3.29/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.29/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.29/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.29/1.01  
% 3.29/1.01  ------ Combination Options
% 3.29/1.01  
% 3.29/1.01  --comb_res_mult                         3
% 3.29/1.01  --comb_sup_mult                         2
% 3.29/1.01  --comb_inst_mult                        10
% 3.29/1.01  
% 3.29/1.01  ------ Debug Options
% 3.29/1.01  
% 3.29/1.01  --dbg_backtrace                         false
% 3.29/1.01  --dbg_dump_prop_clauses                 false
% 3.29/1.01  --dbg_dump_prop_clauses_file            -
% 3.29/1.01  --dbg_out_stat                          false
% 3.29/1.01  
% 3.29/1.01  
% 3.29/1.01  
% 3.29/1.01  
% 3.29/1.01  ------ Proving...
% 3.29/1.01  
% 3.29/1.01  
% 3.29/1.01  % SZS status Theorem for theBenchmark.p
% 3.29/1.01  
% 3.29/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.29/1.01  
% 3.29/1.01  fof(f1,axiom,(
% 3.29/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 3.29/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.01  
% 3.29/1.01  fof(f16,plain,(
% 3.29/1.01    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.29/1.01    inference(ennf_transformation,[],[f1])).
% 3.29/1.01  
% 3.29/1.01  fof(f32,plain,(
% 3.29/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.29/1.01    inference(cnf_transformation,[],[f16])).
% 3.29/1.01  
% 3.29/1.01  fof(f6,axiom,(
% 3.29/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.29/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.01  
% 3.29/1.01  fof(f37,plain,(
% 3.29/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.29/1.01    inference(cnf_transformation,[],[f6])).
% 3.29/1.01  
% 3.29/1.01  fof(f5,axiom,(
% 3.29/1.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.29/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.01  
% 3.29/1.01  fof(f36,plain,(
% 3.29/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.29/1.01    inference(cnf_transformation,[],[f5])).
% 3.29/1.01  
% 3.29/1.01  fof(f49,plain,(
% 3.29/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 3.29/1.01    inference(definition_unfolding,[],[f37,f36])).
% 3.29/1.01  
% 3.29/1.01  fof(f50,plain,(
% 3.29/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 3.29/1.01    inference(definition_unfolding,[],[f32,f49])).
% 3.29/1.01  
% 3.29/1.01  fof(f4,axiom,(
% 3.29/1.01    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 3.29/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.01  
% 3.29/1.01  fof(f19,plain,(
% 3.29/1.01    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.29/1.01    inference(ennf_transformation,[],[f4])).
% 3.29/1.01  
% 3.29/1.01  fof(f20,plain,(
% 3.29/1.01    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.29/1.01    inference(flattening,[],[f19])).
% 3.29/1.01  
% 3.29/1.01  fof(f35,plain,(
% 3.29/1.01    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.29/1.01    inference(cnf_transformation,[],[f20])).
% 3.29/1.01  
% 3.29/1.01  fof(f52,plain,(
% 3.29/1.01    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.29/1.01    inference(definition_unfolding,[],[f35,f49])).
% 3.29/1.01  
% 3.29/1.01  fof(f2,axiom,(
% 3.29/1.01    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.29/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.01  
% 3.29/1.01  fof(f17,plain,(
% 3.29/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.29/1.01    inference(ennf_transformation,[],[f2])).
% 3.29/1.01  
% 3.29/1.01  fof(f18,plain,(
% 3.29/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.29/1.01    inference(flattening,[],[f17])).
% 3.29/1.01  
% 3.29/1.01  fof(f33,plain,(
% 3.29/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.29/1.01    inference(cnf_transformation,[],[f18])).
% 3.29/1.01  
% 3.29/1.01  fof(f3,axiom,(
% 3.29/1.01    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.29/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.01  
% 3.29/1.01  fof(f34,plain,(
% 3.29/1.01    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.29/1.01    inference(cnf_transformation,[],[f3])).
% 3.29/1.01  
% 3.29/1.01  fof(f51,plain,(
% 3.29/1.01    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 3.29/1.01    inference(definition_unfolding,[],[f34,f49])).
% 3.29/1.01  
% 3.29/1.01  fof(f10,axiom,(
% 3.29/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.29/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.01  
% 3.29/1.01  fof(f42,plain,(
% 3.29/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.29/1.01    inference(cnf_transformation,[],[f10])).
% 3.29/1.01  
% 3.29/1.01  fof(f7,axiom,(
% 3.29/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.29/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.01  
% 3.29/1.01  fof(f21,plain,(
% 3.29/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.29/1.01    inference(ennf_transformation,[],[f7])).
% 3.29/1.01  
% 3.29/1.01  fof(f38,plain,(
% 3.29/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.29/1.01    inference(cnf_transformation,[],[f21])).
% 3.29/1.01  
% 3.29/1.01  fof(f14,conjecture,(
% 3.29/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 3.29/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.01  
% 3.29/1.01  fof(f15,negated_conjecture,(
% 3.29/1.01    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 3.29/1.01    inference(negated_conjecture,[],[f14])).
% 3.29/1.01  
% 3.29/1.01  fof(f28,plain,(
% 3.29/1.01    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.29/1.01    inference(ennf_transformation,[],[f15])).
% 3.29/1.01  
% 3.29/1.01  fof(f30,plain,(
% 3.29/1.01    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 3.29/1.01    introduced(choice_axiom,[])).
% 3.29/1.01  
% 3.29/1.01  fof(f31,plain,(
% 3.29/1.01    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.29/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f30])).
% 3.29/1.01  
% 3.29/1.01  fof(f47,plain,(
% 3.29/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.29/1.01    inference(cnf_transformation,[],[f31])).
% 3.29/1.01  
% 3.29/1.01  fof(f13,axiom,(
% 3.29/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.29/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.01  
% 3.29/1.01  fof(f27,plain,(
% 3.29/1.01    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.29/1.01    inference(ennf_transformation,[],[f13])).
% 3.29/1.01  
% 3.29/1.01  fof(f45,plain,(
% 3.29/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.29/1.01    inference(cnf_transformation,[],[f27])).
% 3.29/1.01  
% 3.29/1.01  fof(f11,axiom,(
% 3.29/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.29/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.01  
% 3.29/1.01  fof(f24,plain,(
% 3.29/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.29/1.01    inference(ennf_transformation,[],[f11])).
% 3.29/1.01  
% 3.29/1.01  fof(f25,plain,(
% 3.29/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.29/1.01    inference(flattening,[],[f24])).
% 3.29/1.01  
% 3.29/1.01  fof(f43,plain,(
% 3.29/1.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.29/1.01    inference(cnf_transformation,[],[f25])).
% 3.29/1.01  
% 3.29/1.01  fof(f12,axiom,(
% 3.29/1.01    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 3.29/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.01  
% 3.29/1.01  fof(f26,plain,(
% 3.29/1.01    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 3.29/1.01    inference(ennf_transformation,[],[f12])).
% 3.29/1.01  
% 3.29/1.01  fof(f44,plain,(
% 3.29/1.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 3.29/1.01    inference(cnf_transformation,[],[f26])).
% 3.29/1.01  
% 3.29/1.01  fof(f8,axiom,(
% 3.29/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.29/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.01  
% 3.29/1.01  fof(f22,plain,(
% 3.29/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.29/1.01    inference(ennf_transformation,[],[f8])).
% 3.29/1.01  
% 3.29/1.01  fof(f29,plain,(
% 3.29/1.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.29/1.01    inference(nnf_transformation,[],[f22])).
% 3.29/1.01  
% 3.29/1.01  fof(f39,plain,(
% 3.29/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.29/1.01    inference(cnf_transformation,[],[f29])).
% 3.29/1.01  
% 3.29/1.01  fof(f46,plain,(
% 3.29/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.29/1.01    inference(cnf_transformation,[],[f27])).
% 3.29/1.01  
% 3.29/1.01  fof(f9,axiom,(
% 3.29/1.01    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 3.29/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/1.01  
% 3.29/1.01  fof(f23,plain,(
% 3.29/1.01    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 3.29/1.01    inference(ennf_transformation,[],[f9])).
% 3.29/1.01  
% 3.29/1.01  fof(f41,plain,(
% 3.29/1.01    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.29/1.01    inference(cnf_transformation,[],[f23])).
% 3.29/1.01  
% 3.29/1.01  fof(f53,plain,(
% 3.29/1.01    ( ! [X0] : (k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.29/1.01    inference(definition_unfolding,[],[f41,f49])).
% 3.29/1.01  
% 3.29/1.01  fof(f48,plain,(
% 3.29/1.01    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 3.29/1.01    inference(cnf_transformation,[],[f31])).
% 3.29/1.01  
% 3.29/1.01  fof(f54,plain,(
% 3.29/1.01    ~r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))),
% 3.29/1.01    inference(definition_unfolding,[],[f48,f49])).
% 3.29/1.01  
% 3.29/1.01  cnf(c_0,plain,
% 3.29/1.01      ( ~ r1_tarski(X0,X1)
% 3.29/1.01      | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
% 3.29/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_355,plain,
% 3.29/1.01      ( ~ r1_tarski(X0_44,X1_44)
% 3.29/1.01      | r1_tarski(X0_44,k3_tarski(k1_enumset1(X2_44,X2_44,X1_44))) ),
% 3.29/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_2008,plain,
% 3.29/1.01      ( r1_tarski(X0_44,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
% 3.29/1.01      | ~ r1_tarski(X0_44,sK1) ),
% 3.29/1.01      inference(instantiation,[status(thm)],[c_355]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_11394,plain,
% 3.29/1.01      ( r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
% 3.29/1.01      | ~ r1_tarski(k2_relat_1(sK2),sK1) ),
% 3.29/1.01      inference(instantiation,[status(thm)],[c_2008]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_3,plain,
% 3.29/1.01      ( ~ r1_tarski(X0,X1)
% 3.29/1.01      | ~ r1_tarski(X2,X1)
% 3.29/1.01      | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
% 3.29/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_352,plain,
% 3.29/1.01      ( ~ r1_tarski(X0_44,X1_44)
% 3.29/1.01      | ~ r1_tarski(X2_44,X1_44)
% 3.29/1.01      | r1_tarski(k3_tarski(k1_enumset1(X0_44,X0_44,X2_44)),X1_44) ),
% 3.29/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_705,plain,
% 3.29/1.01      ( ~ r1_tarski(X0_44,k3_tarski(k1_enumset1(X1_44,X1_44,X2_44)))
% 3.29/1.01      | ~ r1_tarski(X3_44,k3_tarski(k1_enumset1(X1_44,X1_44,X2_44)))
% 3.29/1.01      | r1_tarski(k3_tarski(k1_enumset1(X0_44,X0_44,X3_44)),k3_tarski(k1_enumset1(X1_44,X1_44,X2_44))) ),
% 3.29/1.01      inference(instantiation,[status(thm)],[c_352]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_2024,plain,
% 3.29/1.01      ( ~ r1_tarski(X0_44,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
% 3.29/1.01      | ~ r1_tarski(X1_44,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
% 3.29/1.01      | r1_tarski(k3_tarski(k1_enumset1(X0_44,X0_44,X1_44)),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
% 3.29/1.01      inference(instantiation,[status(thm)],[c_705]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_5174,plain,
% 3.29/1.01      ( ~ r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
% 3.29/1.01      | ~ r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
% 3.29/1.01      | r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
% 3.29/1.01      inference(instantiation,[status(thm)],[c_2024]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_1,plain,
% 3.29/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.29/1.01      inference(cnf_transformation,[],[f33]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_354,plain,
% 3.29/1.01      ( ~ r1_tarski(X0_44,X1_44)
% 3.29/1.01      | ~ r1_tarski(X1_44,X2_44)
% 3.29/1.01      | r1_tarski(X0_44,X2_44) ),
% 3.29/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_1518,plain,
% 3.29/1.01      ( ~ r1_tarski(X0_44,X1_44)
% 3.29/1.01      | ~ r1_tarski(k1_relat_1(X0_45),X0_44)
% 3.29/1.01      | r1_tarski(k1_relat_1(X0_45),X1_44) ),
% 3.29/1.01      inference(instantiation,[status(thm)],[c_354]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_4947,plain,
% 3.29/1.01      ( ~ r1_tarski(X0_44,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
% 3.29/1.01      | ~ r1_tarski(k1_relat_1(X0_45),X0_44)
% 3.29/1.01      | r1_tarski(k1_relat_1(X0_45),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
% 3.29/1.01      inference(instantiation,[status(thm)],[c_1518]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_4949,plain,
% 3.29/1.01      ( r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
% 3.29/1.01      | ~ r1_tarski(k1_relat_1(sK2),sK0)
% 3.29/1.01      | ~ r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
% 3.29/1.01      inference(instantiation,[status(thm)],[c_4947]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_366,plain,
% 3.29/1.01      ( ~ r1_tarski(X0_44,X1_44)
% 3.29/1.01      | r1_tarski(X2_44,X3_44)
% 3.29/1.01      | X2_44 != X0_44
% 3.29/1.01      | X3_44 != X1_44 ),
% 3.29/1.01      theory(equality) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_713,plain,
% 3.29/1.01      ( r1_tarski(X0_44,X1_44)
% 3.29/1.01      | ~ r1_tarski(X2_44,k3_tarski(k1_enumset1(X3_44,X3_44,X4_44)))
% 3.29/1.01      | X0_44 != X2_44
% 3.29/1.01      | X1_44 != k3_tarski(k1_enumset1(X3_44,X3_44,X4_44)) ),
% 3.29/1.01      inference(instantiation,[status(thm)],[c_366]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_853,plain,
% 3.29/1.01      ( ~ r1_tarski(X0_44,k3_tarski(k1_enumset1(X1_44,X1_44,X2_44)))
% 3.29/1.01      | r1_tarski(X3_44,k3_tarski(k1_enumset1(X1_44,X1_44,X2_44)))
% 3.29/1.01      | X3_44 != X0_44
% 3.29/1.01      | k3_tarski(k1_enumset1(X1_44,X1_44,X2_44)) != k3_tarski(k1_enumset1(X1_44,X1_44,X2_44)) ),
% 3.29/1.01      inference(instantiation,[status(thm)],[c_713]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_1620,plain,
% 3.29/1.01      ( ~ r1_tarski(X0_44,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
% 3.29/1.01      | r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
% 3.29/1.01      | k3_relat_1(sK2) != X0_44
% 3.29/1.01      | k3_tarski(k1_enumset1(sK0,sK0,sK1)) != k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
% 3.29/1.01      inference(instantiation,[status(thm)],[c_853]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_3272,plain,
% 3.29/1.01      ( r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
% 3.29/1.01      | ~ r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))),k3_tarski(k1_enumset1(sK0,sK0,sK1)))
% 3.29/1.01      | k3_relat_1(sK2) != k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2)))
% 3.29/1.01      | k3_tarski(k1_enumset1(sK0,sK0,sK1)) != k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
% 3.29/1.01      inference(instantiation,[status(thm)],[c_1620]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_2,plain,
% 3.29/1.01      ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
% 3.29/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_353,plain,
% 3.29/1.01      ( r1_tarski(X0_44,k3_tarski(k1_enumset1(X0_44,X0_44,X1_44))) ),
% 3.29/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_1950,plain,
% 3.29/1.01      ( r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
% 3.29/1.01      inference(instantiation,[status(thm)],[c_353]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_357,plain,( X0_44 = X0_44 ),theory(equality) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_789,plain,
% 3.29/1.01      ( k3_tarski(k1_enumset1(X0_44,X0_44,X1_44)) = k3_tarski(k1_enumset1(X0_44,X0_44,X1_44)) ),
% 3.29/1.01      inference(instantiation,[status(thm)],[c_357]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_1867,plain,
% 3.29/1.01      ( k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
% 3.29/1.01      inference(instantiation,[status(thm)],[c_789]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_361,plain,
% 3.29/1.01      ( X0_44 != X1_44 | X2_44 != X1_44 | X2_44 = X0_44 ),
% 3.29/1.01      theory(equality) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_793,plain,
% 3.29/1.01      ( X0_44 != X1_44
% 3.29/1.01      | X0_44 = k3_tarski(k1_enumset1(X2_44,X2_44,X3_44))
% 3.29/1.01      | k3_tarski(k1_enumset1(X2_44,X2_44,X3_44)) != X1_44 ),
% 3.29/1.01      inference(instantiation,[status(thm)],[c_361]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_1116,plain,
% 3.29/1.01      ( X0_44 != k3_relat_1(X0_45)
% 3.29/1.01      | X0_44 = k3_tarski(k1_enumset1(k1_relat_1(X0_45),k1_relat_1(X0_45),k2_relat_1(X0_45)))
% 3.29/1.01      | k3_tarski(k1_enumset1(k1_relat_1(X0_45),k1_relat_1(X0_45),k2_relat_1(X0_45))) != k3_relat_1(X0_45) ),
% 3.29/1.01      inference(instantiation,[status(thm)],[c_793]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_1398,plain,
% 3.29/1.01      ( k3_relat_1(X0_45) != k3_relat_1(X0_45)
% 3.29/1.01      | k3_relat_1(X0_45) = k3_tarski(k1_enumset1(k1_relat_1(X0_45),k1_relat_1(X0_45),k2_relat_1(X0_45)))
% 3.29/1.01      | k3_tarski(k1_enumset1(k1_relat_1(X0_45),k1_relat_1(X0_45),k2_relat_1(X0_45))) != k3_relat_1(X0_45) ),
% 3.29/1.01      inference(instantiation,[status(thm)],[c_1116]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_1400,plain,
% 3.29/1.01      ( k3_relat_1(sK2) != k3_relat_1(sK2)
% 3.29/1.01      | k3_relat_1(sK2) = k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2)))
% 3.29/1.01      | k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))) != k3_relat_1(sK2) ),
% 3.29/1.01      inference(instantiation,[status(thm)],[c_1398]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_8,plain,
% 3.29/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.29/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_350,plain,
% 3.29/1.01      ( v1_relat_1(k2_zfmisc_1(X0_44,X1_44)) ),
% 3.29/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_588,plain,
% 3.29/1.01      ( v1_relat_1(k2_zfmisc_1(X0_44,X1_44)) = iProver_top ),
% 3.29/1.01      inference(predicate_to_equality,[status(thm)],[c_350]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_4,plain,
% 3.29/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.29/1.01      | ~ v1_relat_1(X1)
% 3.29/1.01      | v1_relat_1(X0) ),
% 3.29/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_14,negated_conjecture,
% 3.29/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.29/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_190,plain,
% 3.29/1.01      ( ~ v1_relat_1(X0)
% 3.29/1.01      | v1_relat_1(X1)
% 3.29/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0)
% 3.29/1.01      | sK2 != X1 ),
% 3.29/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_14]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_191,plain,
% 3.29/1.01      ( ~ v1_relat_1(X0)
% 3.29/1.01      | v1_relat_1(sK2)
% 3.29/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0) ),
% 3.29/1.01      inference(unflattening,[status(thm)],[c_190]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_347,plain,
% 3.29/1.01      ( ~ v1_relat_1(X0_45)
% 3.29/1.01      | v1_relat_1(sK2)
% 3.29/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0_45) ),
% 3.29/1.01      inference(subtyping,[status(esa)],[c_191]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_591,plain,
% 3.29/1.01      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0_45)
% 3.29/1.01      | v1_relat_1(X0_45) != iProver_top
% 3.29/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.29/1.01      inference(predicate_to_equality,[status(thm)],[c_347]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_682,plain,
% 3.29/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.29/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.29/1.01      inference(equality_resolution,[status(thm)],[c_591]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_837,plain,
% 3.29/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 3.29/1.01      inference(superposition,[status(thm)],[c_588,c_682]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_12,plain,
% 3.29/1.01      ( v4_relat_1(X0,X1)
% 3.29/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.29/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_9,plain,
% 3.29/1.01      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.29/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_172,plain,
% 3.29/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.29/1.01      | ~ v1_relat_1(X0)
% 3.29/1.01      | k7_relat_1(X0,X1) = X0 ),
% 3.29/1.01      inference(resolution,[status(thm)],[c_12,c_9]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_217,plain,
% 3.29/1.01      ( ~ v1_relat_1(X0)
% 3.29/1.01      | k7_relat_1(X0,X1) = X0
% 3.29/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 3.29/1.01      | sK2 != X0 ),
% 3.29/1.01      inference(resolution_lifted,[status(thm)],[c_172,c_14]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_218,plain,
% 3.29/1.01      ( ~ v1_relat_1(sK2)
% 3.29/1.01      | k7_relat_1(sK2,X0) = sK2
% 3.29/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.29/1.01      inference(unflattening,[status(thm)],[c_217]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_346,plain,
% 3.29/1.01      ( ~ v1_relat_1(sK2)
% 3.29/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 3.29/1.01      | k7_relat_1(sK2,X0_44) = sK2 ),
% 3.29/1.01      inference(subtyping,[status(esa)],[c_218]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_592,plain,
% 3.29/1.01      ( k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 3.29/1.01      | k7_relat_1(sK2,X0_44) = sK2
% 3.29/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.29/1.01      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_720,plain,
% 3.29/1.01      ( k7_relat_1(sK2,sK0) = sK2 | v1_relat_1(sK2) != iProver_top ),
% 3.29/1.01      inference(equality_resolution,[status(thm)],[c_592]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_1144,plain,
% 3.29/1.01      ( k7_relat_1(sK2,sK0) = sK2 ),
% 3.29/1.01      inference(superposition,[status(thm)],[c_837,c_720]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_10,plain,
% 3.29/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 3.29/1.01      inference(cnf_transformation,[],[f44]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_349,plain,
% 3.29/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(X0_45,X0_44)),X0_44)
% 3.29/1.01      | ~ v1_relat_1(X0_45) ),
% 3.29/1.01      inference(subtyping,[status(esa)],[c_10]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_589,plain,
% 3.29/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(X0_45,X0_44)),X0_44) = iProver_top
% 3.29/1.01      | v1_relat_1(X0_45) != iProver_top ),
% 3.29/1.01      inference(predicate_to_equality,[status(thm)],[c_349]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_1151,plain,
% 3.29/1.01      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
% 3.29/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.29/1.01      inference(superposition,[status(thm)],[c_1144,c_589]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_1152,plain,
% 3.29/1.01      ( r1_tarski(k1_relat_1(sK2),sK0) | ~ v1_relat_1(sK2) ),
% 3.29/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1151]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_826,plain,
% 3.29/1.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.29/1.01      inference(instantiation,[status(thm)],[c_350]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_6,plain,
% 3.29/1.01      ( ~ v5_relat_1(X0,X1)
% 3.29/1.01      | r1_tarski(k2_relat_1(X0),X1)
% 3.29/1.01      | ~ v1_relat_1(X0) ),
% 3.29/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_11,plain,
% 3.29/1.01      ( v5_relat_1(X0,X1)
% 3.29/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.29/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_205,plain,
% 3.29/1.01      ( v5_relat_1(X0,X1)
% 3.29/1.01      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 3.29/1.01      | sK2 != X0 ),
% 3.29/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_14]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_206,plain,
% 3.29/1.01      ( v5_relat_1(sK2,X0)
% 3.29/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.29/1.01      inference(unflattening,[status(thm)],[c_205]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_244,plain,
% 3.29/1.01      ( r1_tarski(k2_relat_1(X0),X1)
% 3.29/1.01      | ~ v1_relat_1(X0)
% 3.29/1.01      | X2 != X1
% 3.29/1.01      | k1_zfmisc_1(k2_zfmisc_1(X3,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 3.29/1.01      | sK2 != X0 ),
% 3.29/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_206]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_245,plain,
% 3.29/1.01      ( r1_tarski(k2_relat_1(sK2),X0)
% 3.29/1.01      | ~ v1_relat_1(sK2)
% 3.29/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.29/1.01      inference(unflattening,[status(thm)],[c_244]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_345,plain,
% 3.29/1.01      ( r1_tarski(k2_relat_1(sK2),X0_44)
% 3.29/1.01      | ~ v1_relat_1(sK2)
% 3.29/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1_44,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.29/1.01      inference(subtyping,[status(esa)],[c_245]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_593,plain,
% 3.29/1.01      ( k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 3.29/1.01      | r1_tarski(k2_relat_1(sK2),X1_44) = iProver_top
% 3.29/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.29/1.01      inference(predicate_to_equality,[status(thm)],[c_345]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_737,plain,
% 3.29/1.01      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top
% 3.29/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.29/1.01      inference(equality_resolution,[status(thm)],[c_593]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_738,plain,
% 3.29/1.01      ( r1_tarski(k2_relat_1(sK2),sK1) | ~ v1_relat_1(sK2) ),
% 3.29/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_737]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_683,plain,
% 3.29/1.01      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2) ),
% 3.29/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_682]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_7,plain,
% 3.29/1.01      ( ~ v1_relat_1(X0)
% 3.29/1.01      | k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 3.29/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_351,plain,
% 3.29/1.01      ( ~ v1_relat_1(X0_45)
% 3.29/1.01      | k3_tarski(k1_enumset1(k1_relat_1(X0_45),k1_relat_1(X0_45),k2_relat_1(X0_45))) = k3_relat_1(X0_45) ),
% 3.29/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_394,plain,
% 3.29/1.01      ( ~ v1_relat_1(sK2)
% 3.29/1.01      | k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))) = k3_relat_1(sK2) ),
% 3.29/1.01      inference(instantiation,[status(thm)],[c_351]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_358,plain,( X0_45 = X0_45 ),theory(equality) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_386,plain,
% 3.29/1.01      ( sK2 = sK2 ),
% 3.29/1.01      inference(instantiation,[status(thm)],[c_358]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_371,plain,
% 3.29/1.01      ( X0_45 != X1_45 | k3_relat_1(X0_45) = k3_relat_1(X1_45) ),
% 3.29/1.01      theory(equality) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_381,plain,
% 3.29/1.01      ( sK2 != sK2 | k3_relat_1(sK2) = k3_relat_1(sK2) ),
% 3.29/1.01      inference(instantiation,[status(thm)],[c_371]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(c_13,negated_conjecture,
% 3.29/1.01      ( ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
% 3.29/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.29/1.01  
% 3.29/1.01  cnf(contradiction,plain,
% 3.29/1.01      ( $false ),
% 3.29/1.01      inference(minisat,
% 3.29/1.01                [status(thm)],
% 3.29/1.01                [c_11394,c_5174,c_4949,c_3272,c_1950,c_1867,c_1400,
% 3.29/1.01                 c_1152,c_826,c_738,c_683,c_394,c_386,c_381,c_13]) ).
% 3.29/1.01  
% 3.29/1.01  
% 3.29/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.29/1.01  
% 3.29/1.01  ------                               Statistics
% 3.29/1.01  
% 3.29/1.01  ------ General
% 3.29/1.01  
% 3.29/1.01  abstr_ref_over_cycles:                  0
% 3.29/1.01  abstr_ref_under_cycles:                 0
% 3.29/1.01  gc_basic_clause_elim:                   0
% 3.29/1.01  forced_gc_time:                         0
% 3.29/1.01  parsing_time:                           0.011
% 3.29/1.01  unif_index_cands_time:                  0.
% 3.29/1.01  unif_index_add_time:                    0.
% 3.29/1.01  orderings_time:                         0.
% 3.29/1.01  out_proof_time:                         0.009
% 3.29/1.01  total_time:                             0.359
% 3.29/1.01  num_of_symbols:                         48
% 3.29/1.01  num_of_terms:                           13252
% 3.29/1.01  
% 3.29/1.01  ------ Preprocessing
% 3.29/1.01  
% 3.29/1.01  num_of_splits:                          0
% 3.29/1.01  num_of_split_atoms:                     0
% 3.29/1.01  num_of_reused_defs:                     0
% 3.29/1.01  num_eq_ax_congr_red:                    9
% 3.29/1.01  num_of_sem_filtered_clauses:            1
% 3.29/1.01  num_of_subtypes:                        4
% 3.29/1.01  monotx_restored_types:                  0
% 3.29/1.01  sat_num_of_epr_types:                   0
% 3.29/1.01  sat_num_of_non_cyclic_types:            0
% 3.29/1.01  sat_guarded_non_collapsed_types:        0
% 3.29/1.01  num_pure_diseq_elim:                    0
% 3.29/1.01  simp_replaced_by:                       0
% 3.29/1.01  res_preprocessed:                       83
% 3.29/1.01  prep_upred:                             0
% 3.29/1.01  prep_unflattend:                        5
% 3.29/1.01  smt_new_axioms:                         0
% 3.29/1.01  pred_elim_cands:                        2
% 3.29/1.01  pred_elim:                              3
% 3.29/1.01  pred_elim_cl:                           4
% 3.29/1.01  pred_elim_cycles:                       5
% 3.29/1.01  merged_defs:                            0
% 3.29/1.01  merged_defs_ncl:                        0
% 3.29/1.01  bin_hyper_res:                          0
% 3.29/1.01  prep_cycles:                            4
% 3.29/1.01  pred_elim_time:                         0.002
% 3.29/1.01  splitting_time:                         0.
% 3.29/1.01  sem_filter_time:                        0.
% 3.29/1.01  monotx_time:                            0.
% 3.29/1.01  subtype_inf_time:                       0.
% 3.29/1.01  
% 3.29/1.01  ------ Problem properties
% 3.29/1.01  
% 3.29/1.01  clauses:                                11
% 3.29/1.01  conjectures:                            1
% 3.29/1.01  epr:                                    1
% 3.29/1.01  horn:                                   11
% 3.29/1.01  ground:                                 1
% 3.29/1.01  unary:                                  3
% 3.29/1.01  binary:                                 3
% 3.29/1.01  lits:                                   24
% 3.29/1.01  lits_eq:                                5
% 3.29/1.01  fd_pure:                                0
% 3.29/1.01  fd_pseudo:                              0
% 3.29/1.01  fd_cond:                                0
% 3.29/1.01  fd_pseudo_cond:                         0
% 3.29/1.01  ac_symbols:                             0
% 3.29/1.01  
% 3.29/1.01  ------ Propositional Solver
% 3.29/1.01  
% 3.29/1.01  prop_solver_calls:                      29
% 3.29/1.01  prop_fast_solver_calls:                 599
% 3.29/1.01  smt_solver_calls:                       0
% 3.29/1.01  smt_fast_solver_calls:                  0
% 3.29/1.01  prop_num_of_clauses:                    3627
% 3.29/1.01  prop_preprocess_simplified:             9965
% 3.29/1.01  prop_fo_subsumed:                       21
% 3.29/1.01  prop_solver_time:                       0.
% 3.29/1.01  smt_solver_time:                        0.
% 3.29/1.01  smt_fast_solver_time:                   0.
% 3.29/1.01  prop_fast_solver_time:                  0.
% 3.29/1.01  prop_unsat_core_time:                   0.
% 3.29/1.01  
% 3.29/1.01  ------ QBF
% 3.29/1.01  
% 3.29/1.01  qbf_q_res:                              0
% 3.29/1.01  qbf_num_tautologies:                    0
% 3.29/1.01  qbf_prep_cycles:                        0
% 3.29/1.01  
% 3.29/1.01  ------ BMC1
% 3.29/1.01  
% 3.29/1.01  bmc1_current_bound:                     -1
% 3.29/1.01  bmc1_last_solved_bound:                 -1
% 3.29/1.01  bmc1_unsat_core_size:                   -1
% 3.29/1.01  bmc1_unsat_core_parents_size:           -1
% 3.29/1.01  bmc1_merge_next_fun:                    0
% 3.29/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.29/1.01  
% 3.29/1.01  ------ Instantiation
% 3.29/1.01  
% 3.29/1.01  inst_num_of_clauses:                    1038
% 3.29/1.01  inst_num_in_passive:                    612
% 3.29/1.01  inst_num_in_active:                     388
% 3.29/1.01  inst_num_in_unprocessed:                37
% 3.29/1.01  inst_num_of_loops:                      422
% 3.29/1.01  inst_num_of_learning_restarts:          0
% 3.29/1.01  inst_num_moves_active_passive:          30
% 3.29/1.01  inst_lit_activity:                      0
% 3.29/1.01  inst_lit_activity_moves:                0
% 3.29/1.01  inst_num_tautologies:                   0
% 3.29/1.01  inst_num_prop_implied:                  0
% 3.29/1.01  inst_num_existing_simplified:           0
% 3.29/1.01  inst_num_eq_res_simplified:             0
% 3.29/1.01  inst_num_child_elim:                    0
% 3.29/1.01  inst_num_of_dismatching_blockings:      1286
% 3.29/1.01  inst_num_of_non_proper_insts:           1721
% 3.29/1.01  inst_num_of_duplicates:                 0
% 3.29/1.01  inst_inst_num_from_inst_to_res:         0
% 3.29/1.01  inst_dismatching_checking_time:         0.
% 3.29/1.01  
% 3.29/1.01  ------ Resolution
% 3.29/1.01  
% 3.29/1.01  res_num_of_clauses:                     0
% 3.29/1.01  res_num_in_passive:                     0
% 3.29/1.01  res_num_in_active:                      0
% 3.29/1.01  res_num_of_loops:                       87
% 3.29/1.01  res_forward_subset_subsumed:            140
% 3.29/1.01  res_backward_subset_subsumed:           0
% 3.29/1.01  res_forward_subsumed:                   0
% 3.29/1.01  res_backward_subsumed:                  0
% 3.29/1.01  res_forward_subsumption_resolution:     0
% 3.29/1.01  res_backward_subsumption_resolution:    0
% 3.29/1.01  res_clause_to_clause_subsumption:       2270
% 3.29/1.01  res_orphan_elimination:                 0
% 3.29/1.01  res_tautology_del:                      141
% 3.29/1.01  res_num_eq_res_simplified:              0
% 3.29/1.01  res_num_sel_changes:                    0
% 3.29/1.01  res_moves_from_active_to_pass:          0
% 3.29/1.01  
% 3.29/1.01  ------ Superposition
% 3.29/1.01  
% 3.29/1.01  sup_time_total:                         0.
% 3.29/1.01  sup_time_generating:                    0.
% 3.29/1.01  sup_time_sim_full:                      0.
% 3.29/1.01  sup_time_sim_immed:                     0.
% 3.29/1.01  
% 3.29/1.01  sup_num_of_clauses:                     270
% 3.29/1.01  sup_num_in_active:                      82
% 3.29/1.01  sup_num_in_passive:                     188
% 3.29/1.01  sup_num_of_loops:                       84
% 3.29/1.01  sup_fw_superposition:                   292
% 3.29/1.01  sup_bw_superposition:                   147
% 3.29/1.01  sup_immediate_simplified:               123
% 3.29/1.01  sup_given_eliminated:                   1
% 3.29/1.01  comparisons_done:                       0
% 3.29/1.01  comparisons_avoided:                    0
% 3.29/1.01  
% 3.29/1.01  ------ Simplifications
% 3.29/1.01  
% 3.29/1.01  
% 3.29/1.01  sim_fw_subset_subsumed:                 93
% 3.29/1.01  sim_bw_subset_subsumed:                 5
% 3.29/1.01  sim_fw_subsumed:                        32
% 3.29/1.01  sim_bw_subsumed:                        1
% 3.29/1.01  sim_fw_subsumption_res:                 0
% 3.29/1.01  sim_bw_subsumption_res:                 0
% 3.29/1.01  sim_tautology_del:                      3
% 3.29/1.01  sim_eq_tautology_del:                   0
% 3.29/1.01  sim_eq_res_simp:                        0
% 3.29/1.01  sim_fw_demodulated:                     0
% 3.29/1.01  sim_bw_demodulated:                     0
% 3.29/1.01  sim_light_normalised:                   0
% 3.29/1.01  sim_joinable_taut:                      0
% 3.29/1.01  sim_joinable_simp:                      0
% 3.29/1.01  sim_ac_normalised:                      0
% 3.29/1.01  sim_smt_subsumption:                    0
% 3.29/1.01  
%------------------------------------------------------------------------------
