%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0681+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:53 EST 2020

% Result     : Theorem 0.79s
% Output     : CNFRefutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :   49 (  83 expanded)
%              Number of clauses        :   27 (  28 expanded)
%              Number of leaves         :    5 (  16 expanded)
%              Depth                    :   13
%              Number of atoms          :  117 ( 300 expanded)
%              Number of equality atoms :   39 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_xboole_0(X0,X1) )
       => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_xboole_0(X0,X1) )
         => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v2_funct_1(X2)
        & r1_xboole_0(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v2_funct_1(sK2)
      & r1_xboole_0(sK0,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v2_funct_1(sK2)
    & r1_xboole_0(sK0,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f12])).

fof(f21,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f19,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f22,plain,(
    ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f20,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_5,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_121,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k3_xboole_0(X1,X2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_5])).

cnf(c_122,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_121])).

cnf(c_8,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_7,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_126,plain,
    ( k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_122,c_8,c_7])).

cnf(c_169,plain,
    ( k3_xboole_0(k9_relat_1(sK2,X0_38),k9_relat_1(sK2,X1_38)) = k9_relat_1(sK2,k3_xboole_0(X0_38,X1_38)) ),
    inference(subtyping,[status(esa)],[c_126])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_65,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_4,negated_conjecture,
    ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_140,plain,
    ( k9_relat_1(sK2,sK1) != X0
    | k9_relat_1(sK2,sK0) != X1
    | k3_xboole_0(X1,X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_65,c_4])).

cnf(c_141,plain,
    ( k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_140])).

cnf(c_167,plain,
    ( k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_141])).

cnf(c_185,plain,
    ( k9_relat_1(sK2,k3_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_169,c_167])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_67,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_6,negated_conjecture,
    ( r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_145,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_67,c_6])).

cnf(c_146,plain,
    ( k3_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_145])).

cnf(c_166,plain,
    ( k3_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_146])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_133,plain,
    ( k9_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_8])).

cnf(c_134,plain,
    ( k9_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_133])).

cnf(c_168,plain,
    ( k9_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_134])).

cnf(c_187,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_185,c_166,c_168])).

cnf(c_188,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_187])).


%------------------------------------------------------------------------------
