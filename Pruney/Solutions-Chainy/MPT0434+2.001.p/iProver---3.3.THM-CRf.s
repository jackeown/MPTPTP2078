%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:54 EST 2020

% Result     : Theorem 19.21s
% Output     : CNFRefutation 19.21s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 162 expanded)
%              Number of clauses        :   74 (  89 expanded)
%              Number of leaves         :   17 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  235 ( 386 expanded)
%              Number of equality atoms :  127 ( 166 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(X0,sK1)))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(sK0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f18,f17])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0,X1] : k1_xboole_0 = k6_subset_1(X0,k2_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f25,f27])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f21,f27])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f27])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f24,f27])).

fof(f32,plain,(
    ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_248,plain,
    ( X0_38 != X1_38
    | X2_38 != X1_38
    | X2_38 = X0_38 ),
    theory(equality)).

cnf(c_1762,plain,
    ( X0_38 != X1_38
    | X0_38 = k1_relat_1(k2_xboole_0(sK0,sK1))
    | k1_relat_1(k2_xboole_0(sK0,sK1)) != X1_38 ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_3068,plain,
    ( X0_38 != k1_relat_1(X1_38)
    | X0_38 = k1_relat_1(k2_xboole_0(sK0,sK1))
    | k1_relat_1(k2_xboole_0(sK0,sK1)) != k1_relat_1(X1_38) ),
    inference(instantiation,[status(thm)],[c_1762])).

cnf(c_6811,plain,
    ( X0_38 != k1_relat_1(k2_xboole_0(sK1,sK0))
    | X0_38 = k1_relat_1(k2_xboole_0(sK0,sK1))
    | k1_relat_1(k2_xboole_0(sK0,sK1)) != k1_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_3068])).

cnf(c_79487,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))) != k1_relat_1(k2_xboole_0(sK1,sK0))
    | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))) = k1_relat_1(k2_xboole_0(sK0,sK1))
    | k1_relat_1(k2_xboole_0(sK0,sK1)) != k1_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_6811])).

cnf(c_252,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | r1_tarski(X2_38,X3_38)
    | X2_38 != X0_38
    | X3_38 != X1_38 ),
    theory(equality)).

cnf(c_6644,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))))
    | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))) != X1_38
    | k1_relat_1(sK0) != X0_38 ),
    inference(instantiation,[status(thm)],[c_252])).

cnf(c_9547,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),X0_38)
    | r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))))
    | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))) != X0_38
    | k1_relat_1(sK0) != k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_6644])).

cnf(c_79455,plain,
    ( r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))))
    | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1)))
    | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))) != k1_relat_1(k2_xboole_0(sK0,sK1))
    | k1_relat_1(sK0) != k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_9547])).

cnf(c_1422,plain,
    ( X0_38 != X1_38
    | k2_xboole_0(X2_38,X3_38) != X1_38
    | k2_xboole_0(X2_38,X3_38) = X0_38 ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_3601,plain,
    ( X0_38 != k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X1_38)))
    | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,X1_38))) = X0_38
    | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,X1_38))) != k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X1_38))) ),
    inference(instantiation,[status(thm)],[c_1422])).

cnf(c_9949,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,X0_38))) = k1_relat_1(X1_38)
    | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,X0_38))) != k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X0_38)))
    | k1_relat_1(X1_38) != k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X0_38))) ),
    inference(instantiation,[status(thm)],[c_3601])).

cnf(c_48711,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))) != k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))
    | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))) = k1_relat_1(k2_xboole_0(sK1,sK0))
    | k1_relat_1(k2_xboole_0(sK1,sK0)) != k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_9949])).

cnf(c_6,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_133,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k6_subset_1(X2,X3) != X1
    | k1_zfmisc_1(X0) != k1_zfmisc_1(X2) ),
    inference(resolution_lifted,[status(thm)],[c_6,c_7])).

cnf(c_134,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k6_subset_1(X1,X2))
    | k1_zfmisc_1(X0) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_133])).

cnf(c_234,plain,
    ( ~ v1_relat_1(X0_38)
    | v1_relat_1(k6_subset_1(X1_38,X2_38))
    | k1_zfmisc_1(X0_38) != k1_zfmisc_1(X1_38) ),
    inference(subtyping,[status(esa)],[c_134])).

cnf(c_842,plain,
    ( v1_relat_1(k6_subset_1(X0_38,X1_38))
    | ~ v1_relat_1(sK0)
    | k1_zfmisc_1(sK0) != k1_zfmisc_1(X0_38) ),
    inference(instantiation,[status(thm)],[c_234])).

cnf(c_863,plain,
    ( v1_relat_1(k6_subset_1(sK0,X0_38))
    | ~ v1_relat_1(sK0)
    | k1_zfmisc_1(sK0) != k1_zfmisc_1(sK0) ),
    inference(instantiation,[status(thm)],[c_842])).

cnf(c_25918,plain,
    ( v1_relat_1(k6_subset_1(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | k1_zfmisc_1(sK0) != k1_zfmisc_1(sK0) ),
    inference(instantiation,[status(thm)],[c_863])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_238,plain,
    ( ~ v1_relat_1(X0_38)
    | ~ v1_relat_1(X1_38)
    | k2_xboole_0(k1_relat_1(X0_38),k1_relat_1(X1_38)) = k1_relat_1(k2_xboole_0(X0_38,X1_38)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1129,plain,
    ( ~ v1_relat_1(X0_38)
    | ~ v1_relat_1(k6_subset_1(sK0,X1_38))
    | k2_xboole_0(k1_relat_1(X0_38),k1_relat_1(k6_subset_1(sK0,X1_38))) = k1_relat_1(k2_xboole_0(X0_38,k6_subset_1(sK0,X1_38))) ),
    inference(instantiation,[status(thm)],[c_238])).

cnf(c_3144,plain,
    ( ~ v1_relat_1(k6_subset_1(sK0,X0_38))
    | ~ v1_relat_1(sK1)
    | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,X0_38))) = k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X0_38))) ),
    inference(instantiation,[status(thm)],[c_1129])).

cnf(c_24546,plain,
    ( ~ v1_relat_1(k6_subset_1(sK0,sK1))
    | ~ v1_relat_1(sK1)
    | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))) = k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_3144])).

cnf(c_3084,plain,
    ( X0_38 != X1_38
    | k1_relat_1(k2_xboole_0(sK1,sK0)) != X1_38
    | k1_relat_1(k2_xboole_0(sK1,sK0)) = X0_38 ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_6828,plain,
    ( X0_38 != k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))
    | k1_relat_1(k2_xboole_0(sK1,sK0)) = X0_38
    | k1_relat_1(k2_xboole_0(sK1,sK0)) != k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_3084])).

cnf(c_13980,plain,
    ( k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) != k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))
    | k1_relat_1(k2_xboole_0(sK1,sK0)) != k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))
    | k1_relat_1(k2_xboole_0(sK1,sK0)) = k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_6828])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_236,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_514,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_236])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_235,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_515,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_235])).

cnf(c_512,plain,
    ( k2_xboole_0(k1_relat_1(X0_38),k1_relat_1(X1_38)) = k1_relat_1(k2_xboole_0(X0_38,X1_38))
    | v1_relat_1(X0_38) != iProver_top
    | v1_relat_1(X1_38) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_238])).

cnf(c_5086,plain,
    ( k2_xboole_0(k1_relat_1(sK0),k1_relat_1(X0_38)) = k1_relat_1(k2_xboole_0(sK0,X0_38))
    | v1_relat_1(X0_38) != iProver_top ),
    inference(superposition,[status(thm)],[c_515,c_512])).

cnf(c_6233,plain,
    ( k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) = k1_relat_1(k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_514,c_5086])).

cnf(c_5,plain,
    ( k6_subset_1(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_239,plain,
    ( k6_subset_1(X0_38,k2_xboole_0(X0_38,X1_38)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_242,plain,
    ( r1_tarski(X0_38,X1_38)
    | k6_subset_1(X0_38,X1_38) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_510,plain,
    ( k6_subset_1(X0_38,X1_38) != k1_xboole_0
    | r1_tarski(X0_38,X1_38) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_242])).

cnf(c_1965,plain,
    ( r1_tarski(X0_38,k2_xboole_0(X0_38,X1_38)) = iProver_top ),
    inference(superposition,[status(thm)],[c_239,c_510])).

cnf(c_6395,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6233,c_1965])).

cnf(c_6471,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6395])).

cnf(c_825,plain,
    ( X0_38 != X1_38
    | X0_38 = k2_xboole_0(X2_38,X3_38)
    | k2_xboole_0(X2_38,X3_38) != X1_38 ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_1428,plain,
    ( X0_38 = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))
    | X0_38 != k1_relat_1(k2_xboole_0(sK1,sK0))
    | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) != k1_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_825])).

cnf(c_1783,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) != k1_relat_1(k2_xboole_0(sK1,sK0))
    | k1_relat_1(X0_38) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))
    | k1_relat_1(X0_38) != k1_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1428])).

cnf(c_5802,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) != k1_relat_1(k2_xboole_0(sK1,sK0))
    | k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))
    | k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) != k1_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1783])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_244,plain,
    ( k2_xboole_0(X0_38,X1_38) = k2_xboole_0(X1_38,X0_38) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2813,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_244])).

cnf(c_254,plain,
    ( X0_38 != X1_38
    | k1_relat_1(X0_38) = k1_relat_1(X1_38) ),
    theory(equality)).

cnf(c_1784,plain,
    ( X0_38 != k2_xboole_0(sK1,sK0)
    | k1_relat_1(X0_38) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_254])).

cnf(c_2812,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,sK0)
    | k1_relat_1(k2_xboole_0(sK0,sK1)) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1784])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k6_subset_1(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_241,plain,
    ( k2_xboole_0(X0_38,k6_subset_1(X1_38,X0_38)) = k2_xboole_0(X0_38,X1_38) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2811,plain,
    ( k2_xboole_0(sK1,k6_subset_1(sK0,sK1)) = k2_xboole_0(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_241])).

cnf(c_2810,plain,
    ( k2_xboole_0(sK1,k6_subset_1(sK0,sK1)) != k2_xboole_0(sK1,sK0)
    | k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1784])).

cnf(c_246,plain,
    ( X0_38 = X0_38 ),
    theory(equality)).

cnf(c_2104,plain,
    ( k1_relat_1(sK0) = k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_246])).

cnf(c_1780,plain,
    ( k1_relat_1(k2_xboole_0(sK1,sK0)) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_246])).

cnf(c_1779,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) != k1_relat_1(k2_xboole_0(sK1,sK0))
    | k1_relat_1(k2_xboole_0(sK1,sK0)) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))
    | k1_relat_1(k2_xboole_0(sK1,sK0)) != k1_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1428])).

cnf(c_247,plain,
    ( X0_39 = X0_39 ),
    theory(equality)).

cnf(c_626,plain,
    ( k1_zfmisc_1(X0_38) = k1_zfmisc_1(X0_38) ),
    inference(instantiation,[status(thm)],[c_247])).

cnf(c_864,plain,
    ( k1_zfmisc_1(sK0) = k1_zfmisc_1(sK0) ),
    inference(instantiation,[status(thm)],[c_626])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_240,plain,
    ( ~ r1_tarski(X0_38,k2_xboole_0(X1_38,X2_38))
    | r1_tarski(k6_subset_1(X0_38,X1_38),X2_38) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_688,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))
    | ~ r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_240])).

cnf(c_621,plain,
    ( ~ v1_relat_1(X0_38)
    | ~ v1_relat_1(sK0)
    | k2_xboole_0(k1_relat_1(X0_38),k1_relat_1(sK0)) = k1_relat_1(k2_xboole_0(X0_38,sK0)) ),
    inference(instantiation,[status(thm)],[c_238])).

cnf(c_676,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_621])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_79487,c_79455,c_48711,c_25918,c_24546,c_13980,c_6471,c_5802,c_2813,c_2812,c_2811,c_2810,c_2104,c_1780,c_1779,c_864,c_688,c_676,c_9,c_10,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:21:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.21/2.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.21/2.98  
% 19.21/2.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.21/2.98  
% 19.21/2.98  ------  iProver source info
% 19.21/2.98  
% 19.21/2.98  git: date: 2020-06-30 10:37:57 +0100
% 19.21/2.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.21/2.98  git: non_committed_changes: false
% 19.21/2.98  git: last_make_outside_of_git: false
% 19.21/2.98  
% 19.21/2.98  ------ 
% 19.21/2.98  ------ Parsing...
% 19.21/2.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  ------ Proving...
% 19.21/2.98  ------ Problem Properties 
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  clauses                                 11
% 19.21/2.98  conjectures                             3
% 19.21/2.98  EPR                                     2
% 19.21/2.98  Horn                                    11
% 19.21/2.98  unary                                   6
% 19.21/2.98  binary                                  3
% 19.21/2.98  lits                                    18
% 19.21/2.98  lits eq                                 7
% 19.21/2.98  fd_pure                                 0
% 19.21/2.98  fd_pseudo                               0
% 19.21/2.98  fd_cond                                 0
% 19.21/2.98  fd_pseudo_cond                          0
% 19.21/2.98  AC symbols                              0
% 19.21/2.98  
% 19.21/2.98  ------ Input Options Time Limit: Unbounded
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ 
% 19.21/2.98  Current options:
% 19.21/2.98  ------ 
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  % SZS status Theorem for theBenchmark.p
% 19.21/2.98  
% 19.21/2.98  % SZS output start CNFRefutation for theBenchmark.p
% 19.21/2.98  
% 19.21/2.98  fof(f6,axiom,(
% 19.21/2.98    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 19.21/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.21/2.98  
% 19.21/2.98  fof(f26,plain,(
% 19.21/2.98    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 19.21/2.98    inference(cnf_transformation,[],[f6])).
% 19.21/2.98  
% 19.21/2.98  fof(f8,axiom,(
% 19.21/2.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 19.21/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.21/2.98  
% 19.21/2.98  fof(f13,plain,(
% 19.21/2.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 19.21/2.98    inference(ennf_transformation,[],[f8])).
% 19.21/2.98  
% 19.21/2.98  fof(f28,plain,(
% 19.21/2.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 19.21/2.98    inference(cnf_transformation,[],[f13])).
% 19.21/2.98  
% 19.21/2.98  fof(f9,axiom,(
% 19.21/2.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))))),
% 19.21/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.21/2.98  
% 19.21/2.98  fof(f14,plain,(
% 19.21/2.98    ! [X0] : (! [X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 19.21/2.98    inference(ennf_transformation,[],[f9])).
% 19.21/2.98  
% 19.21/2.98  fof(f29,plain,(
% 19.21/2.98    ( ! [X0,X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 19.21/2.98    inference(cnf_transformation,[],[f14])).
% 19.21/2.98  
% 19.21/2.98  fof(f10,conjecture,(
% 19.21/2.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 19.21/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.21/2.98  
% 19.21/2.98  fof(f11,negated_conjecture,(
% 19.21/2.98    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 19.21/2.98    inference(negated_conjecture,[],[f10])).
% 19.21/2.98  
% 19.21/2.98  fof(f15,plain,(
% 19.21/2.98    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 19.21/2.98    inference(ennf_transformation,[],[f11])).
% 19.21/2.98  
% 19.21/2.98  fof(f18,plain,(
% 19.21/2.98    ( ! [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) => (~r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(X0,sK1))) & v1_relat_1(sK1))) )),
% 19.21/2.98    introduced(choice_axiom,[])).
% 19.21/2.98  
% 19.21/2.98  fof(f17,plain,(
% 19.21/2.98    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 19.21/2.98    introduced(choice_axiom,[])).
% 19.21/2.98  
% 19.21/2.98  fof(f19,plain,(
% 19.21/2.98    (~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 19.21/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f18,f17])).
% 19.21/2.98  
% 19.21/2.98  fof(f31,plain,(
% 19.21/2.98    v1_relat_1(sK1)),
% 19.21/2.98    inference(cnf_transformation,[],[f19])).
% 19.21/2.98  
% 19.21/2.98  fof(f30,plain,(
% 19.21/2.98    v1_relat_1(sK0)),
% 19.21/2.98    inference(cnf_transformation,[],[f19])).
% 19.21/2.98  
% 19.21/2.98  fof(f5,axiom,(
% 19.21/2.98    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 19.21/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.21/2.98  
% 19.21/2.98  fof(f25,plain,(
% 19.21/2.98    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 19.21/2.98    inference(cnf_transformation,[],[f5])).
% 19.21/2.98  
% 19.21/2.98  fof(f7,axiom,(
% 19.21/2.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 19.21/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.21/2.98  
% 19.21/2.98  fof(f27,plain,(
% 19.21/2.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 19.21/2.98    inference(cnf_transformation,[],[f7])).
% 19.21/2.98  
% 19.21/2.98  fof(f37,plain,(
% 19.21/2.98    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,k2_xboole_0(X0,X1))) )),
% 19.21/2.98    inference(definition_unfolding,[],[f25,f27])).
% 19.21/2.98  
% 19.21/2.98  fof(f2,axiom,(
% 19.21/2.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 19.21/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.21/2.98  
% 19.21/2.98  fof(f16,plain,(
% 19.21/2.98    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 19.21/2.98    inference(nnf_transformation,[],[f2])).
% 19.21/2.98  
% 19.21/2.98  fof(f21,plain,(
% 19.21/2.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 19.21/2.98    inference(cnf_transformation,[],[f16])).
% 19.21/2.98  
% 19.21/2.98  fof(f34,plain,(
% 19.21/2.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 19.21/2.98    inference(definition_unfolding,[],[f21,f27])).
% 19.21/2.98  
% 19.21/2.98  fof(f1,axiom,(
% 19.21/2.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 19.21/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.21/2.98  
% 19.21/2.98  fof(f20,plain,(
% 19.21/2.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 19.21/2.98    inference(cnf_transformation,[],[f1])).
% 19.21/2.98  
% 19.21/2.98  fof(f3,axiom,(
% 19.21/2.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 19.21/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.21/2.98  
% 19.21/2.98  fof(f23,plain,(
% 19.21/2.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 19.21/2.98    inference(cnf_transformation,[],[f3])).
% 19.21/2.98  
% 19.21/2.98  fof(f35,plain,(
% 19.21/2.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0))) )),
% 19.21/2.98    inference(definition_unfolding,[],[f23,f27])).
% 19.21/2.98  
% 19.21/2.98  fof(f4,axiom,(
% 19.21/2.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 19.21/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.21/2.98  
% 19.21/2.98  fof(f12,plain,(
% 19.21/2.98    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 19.21/2.98    inference(ennf_transformation,[],[f4])).
% 19.21/2.98  
% 19.21/2.98  fof(f24,plain,(
% 19.21/2.98    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 19.21/2.98    inference(cnf_transformation,[],[f12])).
% 19.21/2.98  
% 19.21/2.98  fof(f36,plain,(
% 19.21/2.98    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 19.21/2.98    inference(definition_unfolding,[],[f24,f27])).
% 19.21/2.98  
% 19.21/2.98  fof(f32,plain,(
% 19.21/2.98    ~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))),
% 19.21/2.98    inference(cnf_transformation,[],[f19])).
% 19.21/2.98  
% 19.21/2.98  cnf(c_248,plain,
% 19.21/2.98      ( X0_38 != X1_38 | X2_38 != X1_38 | X2_38 = X0_38 ),
% 19.21/2.98      theory(equality) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_1762,plain,
% 19.21/2.98      ( X0_38 != X1_38
% 19.21/2.98      | X0_38 = k1_relat_1(k2_xboole_0(sK0,sK1))
% 19.21/2.98      | k1_relat_1(k2_xboole_0(sK0,sK1)) != X1_38 ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_248]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_3068,plain,
% 19.21/2.98      ( X0_38 != k1_relat_1(X1_38)
% 19.21/2.98      | X0_38 = k1_relat_1(k2_xboole_0(sK0,sK1))
% 19.21/2.98      | k1_relat_1(k2_xboole_0(sK0,sK1)) != k1_relat_1(X1_38) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_1762]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_6811,plain,
% 19.21/2.98      ( X0_38 != k1_relat_1(k2_xboole_0(sK1,sK0))
% 19.21/2.98      | X0_38 = k1_relat_1(k2_xboole_0(sK0,sK1))
% 19.21/2.98      | k1_relat_1(k2_xboole_0(sK0,sK1)) != k1_relat_1(k2_xboole_0(sK1,sK0)) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_3068]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_79487,plain,
% 19.21/2.98      ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))) != k1_relat_1(k2_xboole_0(sK1,sK0))
% 19.21/2.98      | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))) = k1_relat_1(k2_xboole_0(sK0,sK1))
% 19.21/2.98      | k1_relat_1(k2_xboole_0(sK0,sK1)) != k1_relat_1(k2_xboole_0(sK1,sK0)) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_6811]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_252,plain,
% 19.21/2.98      ( ~ r1_tarski(X0_38,X1_38)
% 19.21/2.98      | r1_tarski(X2_38,X3_38)
% 19.21/2.98      | X2_38 != X0_38
% 19.21/2.98      | X3_38 != X1_38 ),
% 19.21/2.98      theory(equality) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_6644,plain,
% 19.21/2.98      ( ~ r1_tarski(X0_38,X1_38)
% 19.21/2.98      | r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))))
% 19.21/2.98      | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))) != X1_38
% 19.21/2.98      | k1_relat_1(sK0) != X0_38 ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_252]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_9547,plain,
% 19.21/2.98      ( ~ r1_tarski(k1_relat_1(sK0),X0_38)
% 19.21/2.98      | r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))))
% 19.21/2.98      | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))) != X0_38
% 19.21/2.98      | k1_relat_1(sK0) != k1_relat_1(sK0) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_6644]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_79455,plain,
% 19.21/2.98      ( r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))))
% 19.21/2.98      | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1)))
% 19.21/2.98      | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))) != k1_relat_1(k2_xboole_0(sK0,sK1))
% 19.21/2.98      | k1_relat_1(sK0) != k1_relat_1(sK0) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_9547]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_1422,plain,
% 19.21/2.98      ( X0_38 != X1_38
% 19.21/2.98      | k2_xboole_0(X2_38,X3_38) != X1_38
% 19.21/2.98      | k2_xboole_0(X2_38,X3_38) = X0_38 ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_248]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_3601,plain,
% 19.21/2.98      ( X0_38 != k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X1_38)))
% 19.21/2.98      | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,X1_38))) = X0_38
% 19.21/2.98      | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,X1_38))) != k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X1_38))) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_1422]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_9949,plain,
% 19.21/2.98      ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,X0_38))) = k1_relat_1(X1_38)
% 19.21/2.98      | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,X0_38))) != k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X0_38)))
% 19.21/2.98      | k1_relat_1(X1_38) != k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X0_38))) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_3601]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_48711,plain,
% 19.21/2.98      ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))) != k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))
% 19.21/2.98      | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))) = k1_relat_1(k2_xboole_0(sK1,sK0))
% 19.21/2.98      | k1_relat_1(k2_xboole_0(sK1,sK0)) != k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_9949]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_6,plain,
% 19.21/2.98      ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
% 19.21/2.98      inference(cnf_transformation,[],[f26]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_7,plain,
% 19.21/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.21/2.98      | ~ v1_relat_1(X1)
% 19.21/2.98      | v1_relat_1(X0) ),
% 19.21/2.98      inference(cnf_transformation,[],[f28]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_133,plain,
% 19.21/2.98      ( ~ v1_relat_1(X0)
% 19.21/2.98      | v1_relat_1(X1)
% 19.21/2.98      | k6_subset_1(X2,X3) != X1
% 19.21/2.98      | k1_zfmisc_1(X0) != k1_zfmisc_1(X2) ),
% 19.21/2.98      inference(resolution_lifted,[status(thm)],[c_6,c_7]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_134,plain,
% 19.21/2.98      ( ~ v1_relat_1(X0)
% 19.21/2.98      | v1_relat_1(k6_subset_1(X1,X2))
% 19.21/2.98      | k1_zfmisc_1(X0) != k1_zfmisc_1(X1) ),
% 19.21/2.98      inference(unflattening,[status(thm)],[c_133]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_234,plain,
% 19.21/2.98      ( ~ v1_relat_1(X0_38)
% 19.21/2.98      | v1_relat_1(k6_subset_1(X1_38,X2_38))
% 19.21/2.98      | k1_zfmisc_1(X0_38) != k1_zfmisc_1(X1_38) ),
% 19.21/2.98      inference(subtyping,[status(esa)],[c_134]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_842,plain,
% 19.21/2.98      ( v1_relat_1(k6_subset_1(X0_38,X1_38))
% 19.21/2.98      | ~ v1_relat_1(sK0)
% 19.21/2.98      | k1_zfmisc_1(sK0) != k1_zfmisc_1(X0_38) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_234]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_863,plain,
% 19.21/2.98      ( v1_relat_1(k6_subset_1(sK0,X0_38))
% 19.21/2.98      | ~ v1_relat_1(sK0)
% 19.21/2.98      | k1_zfmisc_1(sK0) != k1_zfmisc_1(sK0) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_842]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_25918,plain,
% 19.21/2.98      ( v1_relat_1(k6_subset_1(sK0,sK1))
% 19.21/2.98      | ~ v1_relat_1(sK0)
% 19.21/2.98      | k1_zfmisc_1(sK0) != k1_zfmisc_1(sK0) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_863]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_8,plain,
% 19.21/2.98      ( ~ v1_relat_1(X0)
% 19.21/2.98      | ~ v1_relat_1(X1)
% 19.21/2.98      | k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ),
% 19.21/2.98      inference(cnf_transformation,[],[f29]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_238,plain,
% 19.21/2.98      ( ~ v1_relat_1(X0_38)
% 19.21/2.98      | ~ v1_relat_1(X1_38)
% 19.21/2.98      | k2_xboole_0(k1_relat_1(X0_38),k1_relat_1(X1_38)) = k1_relat_1(k2_xboole_0(X0_38,X1_38)) ),
% 19.21/2.98      inference(subtyping,[status(esa)],[c_8]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_1129,plain,
% 19.21/2.98      ( ~ v1_relat_1(X0_38)
% 19.21/2.98      | ~ v1_relat_1(k6_subset_1(sK0,X1_38))
% 19.21/2.98      | k2_xboole_0(k1_relat_1(X0_38),k1_relat_1(k6_subset_1(sK0,X1_38))) = k1_relat_1(k2_xboole_0(X0_38,k6_subset_1(sK0,X1_38))) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_238]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_3144,plain,
% 19.21/2.98      ( ~ v1_relat_1(k6_subset_1(sK0,X0_38))
% 19.21/2.98      | ~ v1_relat_1(sK1)
% 19.21/2.98      | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,X0_38))) = k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X0_38))) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_1129]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_24546,plain,
% 19.21/2.98      ( ~ v1_relat_1(k6_subset_1(sK0,sK1))
% 19.21/2.98      | ~ v1_relat_1(sK1)
% 19.21/2.98      | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1))) = k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_3144]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_3084,plain,
% 19.21/2.98      ( X0_38 != X1_38
% 19.21/2.98      | k1_relat_1(k2_xboole_0(sK1,sK0)) != X1_38
% 19.21/2.98      | k1_relat_1(k2_xboole_0(sK1,sK0)) = X0_38 ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_248]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_6828,plain,
% 19.21/2.98      ( X0_38 != k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))
% 19.21/2.98      | k1_relat_1(k2_xboole_0(sK1,sK0)) = X0_38
% 19.21/2.98      | k1_relat_1(k2_xboole_0(sK1,sK0)) != k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_3084]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_13980,plain,
% 19.21/2.98      ( k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) != k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))
% 19.21/2.98      | k1_relat_1(k2_xboole_0(sK1,sK0)) != k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))
% 19.21/2.98      | k1_relat_1(k2_xboole_0(sK1,sK0)) = k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_6828]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_10,negated_conjecture,
% 19.21/2.98      ( v1_relat_1(sK1) ),
% 19.21/2.98      inference(cnf_transformation,[],[f31]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_236,negated_conjecture,
% 19.21/2.98      ( v1_relat_1(sK1) ),
% 19.21/2.98      inference(subtyping,[status(esa)],[c_10]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_514,plain,
% 19.21/2.98      ( v1_relat_1(sK1) = iProver_top ),
% 19.21/2.98      inference(predicate_to_equality,[status(thm)],[c_236]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_11,negated_conjecture,
% 19.21/2.98      ( v1_relat_1(sK0) ),
% 19.21/2.98      inference(cnf_transformation,[],[f30]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_235,negated_conjecture,
% 19.21/2.98      ( v1_relat_1(sK0) ),
% 19.21/2.98      inference(subtyping,[status(esa)],[c_11]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_515,plain,
% 19.21/2.98      ( v1_relat_1(sK0) = iProver_top ),
% 19.21/2.98      inference(predicate_to_equality,[status(thm)],[c_235]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_512,plain,
% 19.21/2.98      ( k2_xboole_0(k1_relat_1(X0_38),k1_relat_1(X1_38)) = k1_relat_1(k2_xboole_0(X0_38,X1_38))
% 19.21/2.98      | v1_relat_1(X0_38) != iProver_top
% 19.21/2.98      | v1_relat_1(X1_38) != iProver_top ),
% 19.21/2.98      inference(predicate_to_equality,[status(thm)],[c_238]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_5086,plain,
% 19.21/2.98      ( k2_xboole_0(k1_relat_1(sK0),k1_relat_1(X0_38)) = k1_relat_1(k2_xboole_0(sK0,X0_38))
% 19.21/2.98      | v1_relat_1(X0_38) != iProver_top ),
% 19.21/2.98      inference(superposition,[status(thm)],[c_515,c_512]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_6233,plain,
% 19.21/2.98      ( k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) = k1_relat_1(k2_xboole_0(sK0,sK1)) ),
% 19.21/2.98      inference(superposition,[status(thm)],[c_514,c_5086]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_5,plain,
% 19.21/2.98      ( k6_subset_1(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 19.21/2.98      inference(cnf_transformation,[],[f37]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_239,plain,
% 19.21/2.98      ( k6_subset_1(X0_38,k2_xboole_0(X0_38,X1_38)) = k1_xboole_0 ),
% 19.21/2.98      inference(subtyping,[status(esa)],[c_5]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_2,plain,
% 19.21/2.98      ( r1_tarski(X0,X1) | k6_subset_1(X0,X1) != k1_xboole_0 ),
% 19.21/2.98      inference(cnf_transformation,[],[f34]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_242,plain,
% 19.21/2.98      ( r1_tarski(X0_38,X1_38)
% 19.21/2.98      | k6_subset_1(X0_38,X1_38) != k1_xboole_0 ),
% 19.21/2.98      inference(subtyping,[status(esa)],[c_2]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_510,plain,
% 19.21/2.98      ( k6_subset_1(X0_38,X1_38) != k1_xboole_0
% 19.21/2.98      | r1_tarski(X0_38,X1_38) = iProver_top ),
% 19.21/2.98      inference(predicate_to_equality,[status(thm)],[c_242]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_1965,plain,
% 19.21/2.98      ( r1_tarski(X0_38,k2_xboole_0(X0_38,X1_38)) = iProver_top ),
% 19.21/2.98      inference(superposition,[status(thm)],[c_239,c_510]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_6395,plain,
% 19.21/2.98      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) = iProver_top ),
% 19.21/2.98      inference(superposition,[status(thm)],[c_6233,c_1965]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_6471,plain,
% 19.21/2.98      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) ),
% 19.21/2.98      inference(predicate_to_equality_rev,[status(thm)],[c_6395]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_825,plain,
% 19.21/2.98      ( X0_38 != X1_38
% 19.21/2.98      | X0_38 = k2_xboole_0(X2_38,X3_38)
% 19.21/2.98      | k2_xboole_0(X2_38,X3_38) != X1_38 ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_248]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_1428,plain,
% 19.21/2.98      ( X0_38 = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))
% 19.21/2.98      | X0_38 != k1_relat_1(k2_xboole_0(sK1,sK0))
% 19.21/2.98      | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) != k1_relat_1(k2_xboole_0(sK1,sK0)) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_825]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_1783,plain,
% 19.21/2.98      ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) != k1_relat_1(k2_xboole_0(sK1,sK0))
% 19.21/2.98      | k1_relat_1(X0_38) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))
% 19.21/2.98      | k1_relat_1(X0_38) != k1_relat_1(k2_xboole_0(sK1,sK0)) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_1428]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_5802,plain,
% 19.21/2.98      ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) != k1_relat_1(k2_xboole_0(sK1,sK0))
% 19.21/2.98      | k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))
% 19.21/2.98      | k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) != k1_relat_1(k2_xboole_0(sK1,sK0)) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_1783]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_0,plain,
% 19.21/2.98      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 19.21/2.98      inference(cnf_transformation,[],[f20]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_244,plain,
% 19.21/2.98      ( k2_xboole_0(X0_38,X1_38) = k2_xboole_0(X1_38,X0_38) ),
% 19.21/2.98      inference(subtyping,[status(esa)],[c_0]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_2813,plain,
% 19.21/2.98      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK0) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_244]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_254,plain,
% 19.21/2.98      ( X0_38 != X1_38 | k1_relat_1(X0_38) = k1_relat_1(X1_38) ),
% 19.21/2.98      theory(equality) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_1784,plain,
% 19.21/2.98      ( X0_38 != k2_xboole_0(sK1,sK0)
% 19.21/2.98      | k1_relat_1(X0_38) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_254]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_2812,plain,
% 19.21/2.98      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,sK0)
% 19.21/2.98      | k1_relat_1(k2_xboole_0(sK0,sK1)) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_1784]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_3,plain,
% 19.21/2.98      ( k2_xboole_0(X0,k6_subset_1(X1,X0)) = k2_xboole_0(X0,X1) ),
% 19.21/2.98      inference(cnf_transformation,[],[f35]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_241,plain,
% 19.21/2.98      ( k2_xboole_0(X0_38,k6_subset_1(X1_38,X0_38)) = k2_xboole_0(X0_38,X1_38) ),
% 19.21/2.98      inference(subtyping,[status(esa)],[c_3]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_2811,plain,
% 19.21/2.98      ( k2_xboole_0(sK1,k6_subset_1(sK0,sK1)) = k2_xboole_0(sK1,sK0) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_241]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_2810,plain,
% 19.21/2.98      ( k2_xboole_0(sK1,k6_subset_1(sK0,sK1)) != k2_xboole_0(sK1,sK0)
% 19.21/2.98      | k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_1784]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_246,plain,( X0_38 = X0_38 ),theory(equality) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_2104,plain,
% 19.21/2.98      ( k1_relat_1(sK0) = k1_relat_1(sK0) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_246]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_1780,plain,
% 19.21/2.98      ( k1_relat_1(k2_xboole_0(sK1,sK0)) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_246]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_1779,plain,
% 19.21/2.98      ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) != k1_relat_1(k2_xboole_0(sK1,sK0))
% 19.21/2.98      | k1_relat_1(k2_xboole_0(sK1,sK0)) = k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))
% 19.21/2.98      | k1_relat_1(k2_xboole_0(sK1,sK0)) != k1_relat_1(k2_xboole_0(sK1,sK0)) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_1428]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_247,plain,( X0_39 = X0_39 ),theory(equality) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_626,plain,
% 19.21/2.98      ( k1_zfmisc_1(X0_38) = k1_zfmisc_1(X0_38) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_247]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_864,plain,
% 19.21/2.98      ( k1_zfmisc_1(sK0) = k1_zfmisc_1(sK0) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_626]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_4,plain,
% 19.21/2.98      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 19.21/2.98      | r1_tarski(k6_subset_1(X0,X1),X2) ),
% 19.21/2.98      inference(cnf_transformation,[],[f36]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_240,plain,
% 19.21/2.98      ( ~ r1_tarski(X0_38,k2_xboole_0(X1_38,X2_38))
% 19.21/2.98      | r1_tarski(k6_subset_1(X0_38,X1_38),X2_38) ),
% 19.21/2.98      inference(subtyping,[status(esa)],[c_4]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_688,plain,
% 19.21/2.98      ( r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))
% 19.21/2.98      | ~ r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,sK1)))) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_240]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_621,plain,
% 19.21/2.98      ( ~ v1_relat_1(X0_38)
% 19.21/2.98      | ~ v1_relat_1(sK0)
% 19.21/2.98      | k2_xboole_0(k1_relat_1(X0_38),k1_relat_1(sK0)) = k1_relat_1(k2_xboole_0(X0_38,sK0)) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_238]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_676,plain,
% 19.21/2.98      ( ~ v1_relat_1(sK1)
% 19.21/2.98      | ~ v1_relat_1(sK0)
% 19.21/2.98      | k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_621]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_9,negated_conjecture,
% 19.21/2.98      ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
% 19.21/2.98      inference(cnf_transformation,[],[f32]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(contradiction,plain,
% 19.21/2.98      ( $false ),
% 19.21/2.98      inference(minisat,
% 19.21/2.98                [status(thm)],
% 19.21/2.98                [c_79487,c_79455,c_48711,c_25918,c_24546,c_13980,c_6471,
% 19.21/2.98                 c_5802,c_2813,c_2812,c_2811,c_2810,c_2104,c_1780,c_1779,
% 19.21/2.98                 c_864,c_688,c_676,c_9,c_10,c_11]) ).
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  % SZS output end CNFRefutation for theBenchmark.p
% 19.21/2.98  
% 19.21/2.98  ------                               Statistics
% 19.21/2.98  
% 19.21/2.98  ------ Selected
% 19.21/2.98  
% 19.21/2.98  total_time:                             2.162
% 19.21/2.98  
%------------------------------------------------------------------------------
