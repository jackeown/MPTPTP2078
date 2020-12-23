%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1105+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:01 EST 2020

% Result     : Theorem 50.87s
% Output     : CNFRefutation 50.87s
% Verified   : 
% Statistics : Number of formulae       :   37 (  51 expanded)
%              Number of clauses        :   12 (  13 expanded)
%              Number of leaves         :    8 (  13 expanded)
%              Depth                    :   10
%              Number of atoms          :   55 (  83 expanded)
%              Number of equality atoms :   37 (  51 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1777,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1778,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) ) ),
    inference(negated_conjecture,[],[f1777])).

fof(f3774,plain,(
    ? [X0] :
      ( k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) != k2_struct_0(X0)
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1778])).

fof(f5339,plain,
    ( ? [X0] :
        ( k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) != k2_struct_0(X0)
        & l1_struct_0(X0) )
   => ( k3_subset_1(u1_struct_0(sK656),k1_struct_0(sK656)) != k2_struct_0(sK656)
      & l1_struct_0(sK656) ) ),
    introduced(choice_axiom,[])).

fof(f5340,plain,
    ( k3_subset_1(u1_struct_0(sK656),k1_struct_0(sK656)) != k2_struct_0(sK656)
    & l1_struct_0(sK656) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK656])],[f3774,f5339])).

fof(f8811,plain,(
    k3_subset_1(u1_struct_0(sK656),k1_struct_0(sK656)) != k2_struct_0(sK656) ),
    inference(cnf_transformation,[],[f5340])).

fof(f1761,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3760,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1761])).

fof(f8795,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3760])).

fof(f8810,plain,(
    l1_struct_0(sK656) ),
    inference(cnf_transformation,[],[f5340])).

fof(f1760,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3759,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1760])).

fof(f8794,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3759])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5348,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f10540,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f8794,f5348])).

fof(f460,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6055,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f460])).

fof(f502,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6143,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f502])).

fof(f458,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6038,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f458])).

fof(f8825,plain,(
    ! [X0] : o_0_0_xboole_0 = k1_subset_1(X0) ),
    inference(definition_unfolding,[],[f6038,f5348])).

fof(f8826,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f6143,f8825])).

fof(f9250,plain,(
    ! [X0] : k3_subset_1(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f6055,f8826])).

cnf(c_3442,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK656),k1_struct_0(sK656)) != k2_struct_0(sK656) ),
    inference(cnf_transformation,[],[f8811])).

cnf(c_3427,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f8795])).

cnf(c_3443,negated_conjecture,
    ( l1_struct_0(sK656) ),
    inference(cnf_transformation,[],[f8810])).

cnf(c_40212,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | sK656 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3427,c_3443])).

cnf(c_40213,plain,
    ( k2_struct_0(sK656) = u1_struct_0(sK656) ),
    inference(unflattening,[status(thm)],[c_40212])).

cnf(c_3426,plain,
    ( ~ l1_struct_0(X0)
    | k1_struct_0(X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f10540])).

cnf(c_40217,plain,
    ( k1_struct_0(X0) = o_0_0_xboole_0
    | sK656 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3426,c_3443])).

cnf(c_40218,plain,
    ( k1_struct_0(sK656) = o_0_0_xboole_0 ),
    inference(unflattening,[status(thm)],[c_40217])).

cnf(c_181123,plain,
    ( k3_subset_1(u1_struct_0(sK656),o_0_0_xboole_0) != u1_struct_0(sK656) ),
    inference(light_normalisation,[status(thm)],[c_3442,c_40213,c_40218])).

cnf(c_701,plain,
    ( k3_subset_1(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9250])).

cnf(c_181124,plain,
    ( u1_struct_0(sK656) != u1_struct_0(sK656) ),
    inference(demodulation,[status(thm)],[c_181123,c_701])).

cnf(c_181125,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_181124])).

%------------------------------------------------------------------------------
