%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0663+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:50 EST 2020

% Result     : Theorem 0.46s
% Output     : CNFRefutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   43 (  69 expanded)
%              Number of clauses        :   26 (  27 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :   15
%              Number of atoms          :  107 ( 221 expanded)
%              Number of equality atoms :   54 (  82 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
        & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
      & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).

fof(f16,plain,(
    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f15,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f14,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f17,plain,(
    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_116,plain,
    ( X0_38 = X0_38 ),
    theory(equality)).

cnf(c_159,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK1)) = k1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_116])).

cnf(c_117,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_141,plain,
    ( k1_funct_1(sK2,sK0) = k1_funct_1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_117])).

cnf(c_119,plain,
    ( X0_41 != X1_41
    | X2_41 != X1_41
    | X2_41 = X0_41 ),
    theory(equality)).

cnf(c_138,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK1),sK0) != X0_41
    | k1_funct_1(sK2,sK0) != X0_41
    | k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_140,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK1),sK0) != k1_funct_1(sK2,sK0)
    | k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    | k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_138])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(k7_relat_1(X1,X2),X0) = k1_funct_1(X1,X0) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_3,negated_conjecture,
    ( r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_61,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_funct_1(k7_relat_1(X0,X1),X2) = k1_funct_1(X0,X2)
    | k1_relat_1(k7_relat_1(X0,X1)) != k3_xboole_0(k1_relat_1(sK2),sK1)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_62,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_funct_1(k7_relat_1(X0,X1),sK0) = k1_funct_1(X0,sK0)
    | k1_relat_1(k7_relat_1(X0,X1)) != k3_xboole_0(k1_relat_1(sK2),sK1) ),
    inference(unflattening,[status(thm)],[c_61])).

cnf(c_4,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_84,plain,
    ( ~ v1_relat_1(X0)
    | k1_funct_1(k7_relat_1(X0,X1),sK0) = k1_funct_1(X0,sK0)
    | k1_relat_1(k7_relat_1(X0,X1)) != k3_xboole_0(k1_relat_1(sK2),sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_62,c_4])).

cnf(c_85,plain,
    ( ~ v1_relat_1(sK2)
    | k1_funct_1(k7_relat_1(sK2,X0),sK0) = k1_funct_1(sK2,sK0)
    | k1_relat_1(k7_relat_1(sK2,X0)) != k3_xboole_0(k1_relat_1(sK2),sK1) ),
    inference(unflattening,[status(thm)],[c_84])).

cnf(c_5,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_89,plain,
    ( k1_funct_1(k7_relat_1(sK2,X0),sK0) = k1_funct_1(sK2,sK0)
    | k1_relat_1(k7_relat_1(sK2,X0)) != k3_xboole_0(k1_relat_1(sK2),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_85,c_5])).

cnf(c_114,plain,
    ( k1_funct_1(k7_relat_1(sK2,X0_39),sK0) = k1_funct_1(sK2,sK0)
    | k1_relat_1(k7_relat_1(sK2,X0_39)) != k3_xboole_0(k1_relat_1(sK2),sK1) ),
    inference(subtyping,[status(esa)],[c_89])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_100,plain,
    ( k3_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(k7_relat_1(X0,X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_5])).

cnf(c_101,plain,
    ( k3_xboole_0(k1_relat_1(sK2),X0) = k1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_100])).

cnf(c_113,plain,
    ( k3_xboole_0(k1_relat_1(sK2),X0_39) = k1_relat_1(k7_relat_1(sK2,X0_39)) ),
    inference(subtyping,[status(esa)],[c_101])).

cnf(c_130,plain,
    ( k1_funct_1(k7_relat_1(sK2,X0_39),sK0) = k1_funct_1(sK2,sK0)
    | k1_relat_1(k7_relat_1(sK2,X0_39)) != k1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(demodulation,[status(thm)],[c_114,c_113])).

cnf(c_135,plain,
    ( k1_funct_1(k7_relat_1(sK2,sK1),sK0) = k1_funct_1(sK2,sK0)
    | k1_relat_1(k7_relat_1(sK2,sK1)) != k1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_130])).

cnf(c_2,negated_conjecture,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_115,negated_conjecture,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_159,c_141,c_140,c_135,c_115])).


%------------------------------------------------------------------------------
