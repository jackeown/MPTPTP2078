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
% DateTime   : Thu Dec  3 12:13:27 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 100 expanded)
%              Number of clauses        :   39 (  44 expanded)
%              Number of leaves         :   11 (  21 expanded)
%              Depth                    :   12
%              Number of atoms          :  168 ( 233 expanded)
%              Number of equality atoms :   70 (  97 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k2_struct_0(X0) = X1
                & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                & k2_struct_0(X0) != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_struct_0(X0) != X1
              | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            & ( k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
              | k2_struct_0(X0) = X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
      | k2_struct_0(X0) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f23,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,k2_struct_0(X0))
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,
    ( ? [X0] :
        ( k2_struct_0(X0) != k2_pre_topc(X0,k2_struct_0(X0))
        & l1_pre_topc(X0) )
   => ( k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0))
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_317,plain,
    ( X0_40 != X1_40
    | X2_40 != X1_40
    | X2_40 = X0_40 ),
    theory(equality)).

cnf(c_903,plain,
    ( k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) != X0_40
    | k1_xboole_0 != X0_40
    | k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_317])).

cnf(c_904,plain,
    ( k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0)))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_903])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_313,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
    | k7_subset_1(X1_40,X0_40,X2_40) = k4_xboole_0(X0_40,X2_40) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_525,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0_40) = k4_xboole_0(k2_struct_0(sK0),X0_40) ),
    inference(instantiation,[status(thm)],[c_313])).

cnf(c_761,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_525])).

cnf(c_633,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) != X0_40
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) = k1_xboole_0
    | k1_xboole_0 != X0_40 ),
    inference(instantiation,[status(thm)],[c_317])).

cnf(c_760,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) != k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_633])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0) != k1_xboole_0
    | k2_struct_0(X1) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_5,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_11,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_161,plain,
    ( l1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_11])).

cnf(c_162,plain,
    ( l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_161])).

cnf(c_217,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0) != k1_xboole_0
    | k2_struct_0(X1) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_162])).

cnf(c_218,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0) != k1_xboole_0
    | k2_struct_0(sK0) = X0 ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_306,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0_40) != k1_xboole_0
    | k2_struct_0(sK0) = X0_40 ),
    inference(subtyping,[status(esa)],[c_218])).

cnf(c_541,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) != k1_xboole_0
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_142,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | X0 != X2
    | k2_pre_topc(X1,X0) != X3
    | k4_xboole_0(X2,X3) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_143,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_xboole_0(X0,k2_pre_topc(X1,X0)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_142])).

cnf(c_168,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_xboole_0(X0,k2_pre_topc(X1,X0)) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_143,c_11])).

cnf(c_169,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_xboole_0(X0,k2_pre_topc(sK0,X0)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_168])).

cnf(c_311,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_xboole_0(X0_40,k2_pre_topc(sK0,X0_40)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_169])).

cnf(c_509,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_311])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_180,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_11])).

cnf(c_181,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_180])).

cnf(c_310,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0_40),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_181])).

cnf(c_510,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_310])).

cnf(c_10,negated_conjecture,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_312,negated_conjecture,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_315,plain,
    ( X0_40 = X0_40 ),
    theory(equality)).

cnf(c_329,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_4,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_29,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_26,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_904,c_761,c_760,c_541,c_509,c_510,c_312,c_329,c_29,c_26,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:23:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.71/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.00  
% 1.71/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.71/1.00  
% 1.71/1.00  ------  iProver source info
% 1.71/1.00  
% 1.71/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.71/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.71/1.00  git: non_committed_changes: false
% 1.71/1.00  git: last_make_outside_of_git: false
% 1.71/1.00  
% 1.71/1.00  ------ 
% 1.71/1.00  
% 1.71/1.00  ------ Input Options
% 1.71/1.00  
% 1.71/1.00  --out_options                           all
% 1.71/1.00  --tptp_safe_out                         true
% 1.71/1.00  --problem_path                          ""
% 1.71/1.00  --include_path                          ""
% 1.71/1.00  --clausifier                            res/vclausify_rel
% 1.71/1.00  --clausifier_options                    --mode clausify
% 1.71/1.00  --stdin                                 false
% 1.71/1.00  --stats_out                             all
% 1.71/1.00  
% 1.71/1.00  ------ General Options
% 1.71/1.00  
% 1.71/1.00  --fof                                   false
% 1.71/1.00  --time_out_real                         305.
% 1.71/1.00  --time_out_virtual                      -1.
% 1.71/1.00  --symbol_type_check                     false
% 1.71/1.00  --clausify_out                          false
% 1.71/1.00  --sig_cnt_out                           false
% 1.71/1.00  --trig_cnt_out                          false
% 1.71/1.00  --trig_cnt_out_tolerance                1.
% 1.71/1.00  --trig_cnt_out_sk_spl                   false
% 1.71/1.00  --abstr_cl_out                          false
% 1.71/1.00  
% 1.71/1.00  ------ Global Options
% 1.71/1.00  
% 1.71/1.00  --schedule                              default
% 1.71/1.00  --add_important_lit                     false
% 1.71/1.00  --prop_solver_per_cl                    1000
% 1.71/1.00  --min_unsat_core                        false
% 1.71/1.00  --soft_assumptions                      false
% 1.71/1.00  --soft_lemma_size                       3
% 1.71/1.00  --prop_impl_unit_size                   0
% 1.71/1.00  --prop_impl_unit                        []
% 1.71/1.00  --share_sel_clauses                     true
% 1.71/1.00  --reset_solvers                         false
% 1.71/1.00  --bc_imp_inh                            [conj_cone]
% 1.71/1.00  --conj_cone_tolerance                   3.
% 1.71/1.00  --extra_neg_conj                        none
% 1.71/1.00  --large_theory_mode                     true
% 1.71/1.00  --prolific_symb_bound                   200
% 1.71/1.00  --lt_threshold                          2000
% 1.71/1.00  --clause_weak_htbl                      true
% 1.71/1.00  --gc_record_bc_elim                     false
% 1.71/1.00  
% 1.71/1.00  ------ Preprocessing Options
% 1.71/1.00  
% 1.71/1.00  --preprocessing_flag                    true
% 1.71/1.00  --time_out_prep_mult                    0.1
% 1.71/1.00  --splitting_mode                        input
% 1.71/1.00  --splitting_grd                         true
% 1.71/1.00  --splitting_cvd                         false
% 1.71/1.00  --splitting_cvd_svl                     false
% 1.71/1.00  --splitting_nvd                         32
% 1.71/1.00  --sub_typing                            true
% 1.71/1.00  --prep_gs_sim                           true
% 1.71/1.00  --prep_unflatten                        true
% 1.71/1.00  --prep_res_sim                          true
% 1.71/1.00  --prep_upred                            true
% 1.71/1.00  --prep_sem_filter                       exhaustive
% 1.71/1.00  --prep_sem_filter_out                   false
% 1.71/1.00  --pred_elim                             true
% 1.71/1.00  --res_sim_input                         true
% 1.71/1.00  --eq_ax_congr_red                       true
% 1.71/1.00  --pure_diseq_elim                       true
% 1.71/1.00  --brand_transform                       false
% 1.71/1.00  --non_eq_to_eq                          false
% 1.71/1.00  --prep_def_merge                        true
% 1.71/1.00  --prep_def_merge_prop_impl              false
% 1.71/1.00  --prep_def_merge_mbd                    true
% 1.71/1.00  --prep_def_merge_tr_red                 false
% 1.71/1.00  --prep_def_merge_tr_cl                  false
% 1.71/1.00  --smt_preprocessing                     true
% 1.71/1.00  --smt_ac_axioms                         fast
% 1.71/1.00  --preprocessed_out                      false
% 1.71/1.00  --preprocessed_stats                    false
% 1.71/1.00  
% 1.71/1.00  ------ Abstraction refinement Options
% 1.71/1.00  
% 1.71/1.00  --abstr_ref                             []
% 1.71/1.00  --abstr_ref_prep                        false
% 1.71/1.00  --abstr_ref_until_sat                   false
% 1.71/1.00  --abstr_ref_sig_restrict                funpre
% 1.71/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.71/1.00  --abstr_ref_under                       []
% 1.71/1.00  
% 1.71/1.00  ------ SAT Options
% 1.71/1.00  
% 1.71/1.00  --sat_mode                              false
% 1.71/1.00  --sat_fm_restart_options                ""
% 1.71/1.00  --sat_gr_def                            false
% 1.71/1.00  --sat_epr_types                         true
% 1.71/1.00  --sat_non_cyclic_types                  false
% 1.71/1.00  --sat_finite_models                     false
% 1.71/1.00  --sat_fm_lemmas                         false
% 1.71/1.00  --sat_fm_prep                           false
% 1.71/1.00  --sat_fm_uc_incr                        true
% 1.71/1.00  --sat_out_model                         small
% 1.71/1.00  --sat_out_clauses                       false
% 1.71/1.00  
% 1.71/1.00  ------ QBF Options
% 1.71/1.00  
% 1.71/1.00  --qbf_mode                              false
% 1.71/1.00  --qbf_elim_univ                         false
% 1.71/1.00  --qbf_dom_inst                          none
% 1.71/1.00  --qbf_dom_pre_inst                      false
% 1.71/1.00  --qbf_sk_in                             false
% 1.71/1.00  --qbf_pred_elim                         true
% 1.71/1.00  --qbf_split                             512
% 1.71/1.00  
% 1.71/1.00  ------ BMC1 Options
% 1.71/1.00  
% 1.71/1.00  --bmc1_incremental                      false
% 1.71/1.00  --bmc1_axioms                           reachable_all
% 1.71/1.00  --bmc1_min_bound                        0
% 1.71/1.00  --bmc1_max_bound                        -1
% 1.71/1.00  --bmc1_max_bound_default                -1
% 1.71/1.00  --bmc1_symbol_reachability              true
% 1.71/1.00  --bmc1_property_lemmas                  false
% 1.71/1.00  --bmc1_k_induction                      false
% 1.71/1.00  --bmc1_non_equiv_states                 false
% 1.71/1.00  --bmc1_deadlock                         false
% 1.71/1.00  --bmc1_ucm                              false
% 1.71/1.00  --bmc1_add_unsat_core                   none
% 1.71/1.00  --bmc1_unsat_core_children              false
% 1.71/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.71/1.00  --bmc1_out_stat                         full
% 1.71/1.00  --bmc1_ground_init                      false
% 1.71/1.00  --bmc1_pre_inst_next_state              false
% 1.71/1.00  --bmc1_pre_inst_state                   false
% 1.71/1.00  --bmc1_pre_inst_reach_state             false
% 1.71/1.00  --bmc1_out_unsat_core                   false
% 1.71/1.00  --bmc1_aig_witness_out                  false
% 1.71/1.00  --bmc1_verbose                          false
% 1.71/1.00  --bmc1_dump_clauses_tptp                false
% 1.71/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.71/1.00  --bmc1_dump_file                        -
% 1.71/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.71/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.71/1.00  --bmc1_ucm_extend_mode                  1
% 1.71/1.00  --bmc1_ucm_init_mode                    2
% 1.71/1.00  --bmc1_ucm_cone_mode                    none
% 1.71/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.71/1.00  --bmc1_ucm_relax_model                  4
% 1.71/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.71/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.71/1.00  --bmc1_ucm_layered_model                none
% 1.71/1.00  --bmc1_ucm_max_lemma_size               10
% 1.71/1.00  
% 1.71/1.00  ------ AIG Options
% 1.71/1.00  
% 1.71/1.00  --aig_mode                              false
% 1.71/1.00  
% 1.71/1.00  ------ Instantiation Options
% 1.71/1.00  
% 1.71/1.00  --instantiation_flag                    true
% 1.71/1.00  --inst_sos_flag                         false
% 1.71/1.00  --inst_sos_phase                        true
% 1.71/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.71/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.71/1.00  --inst_lit_sel_side                     num_symb
% 1.71/1.00  --inst_solver_per_active                1400
% 1.71/1.00  --inst_solver_calls_frac                1.
% 1.71/1.00  --inst_passive_queue_type               priority_queues
% 1.71/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.71/1.00  --inst_passive_queues_freq              [25;2]
% 1.71/1.00  --inst_dismatching                      true
% 1.71/1.00  --inst_eager_unprocessed_to_passive     true
% 1.71/1.00  --inst_prop_sim_given                   true
% 1.71/1.00  --inst_prop_sim_new                     false
% 1.71/1.00  --inst_subs_new                         false
% 1.71/1.00  --inst_eq_res_simp                      false
% 1.71/1.00  --inst_subs_given                       false
% 1.71/1.00  --inst_orphan_elimination               true
% 1.71/1.00  --inst_learning_loop_flag               true
% 1.71/1.00  --inst_learning_start                   3000
% 1.71/1.00  --inst_learning_factor                  2
% 1.71/1.00  --inst_start_prop_sim_after_learn       3
% 1.71/1.00  --inst_sel_renew                        solver
% 1.71/1.00  --inst_lit_activity_flag                true
% 1.71/1.00  --inst_restr_to_given                   false
% 1.71/1.00  --inst_activity_threshold               500
% 1.71/1.00  --inst_out_proof                        true
% 1.71/1.00  
% 1.71/1.00  ------ Resolution Options
% 1.71/1.00  
% 1.71/1.00  --resolution_flag                       true
% 1.71/1.00  --res_lit_sel                           adaptive
% 1.71/1.00  --res_lit_sel_side                      none
% 1.71/1.00  --res_ordering                          kbo
% 1.71/1.00  --res_to_prop_solver                    active
% 1.71/1.00  --res_prop_simpl_new                    false
% 1.71/1.00  --res_prop_simpl_given                  true
% 1.71/1.00  --res_passive_queue_type                priority_queues
% 1.71/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.71/1.00  --res_passive_queues_freq               [15;5]
% 1.71/1.00  --res_forward_subs                      full
% 1.71/1.00  --res_backward_subs                     full
% 1.71/1.00  --res_forward_subs_resolution           true
% 1.71/1.00  --res_backward_subs_resolution          true
% 1.71/1.00  --res_orphan_elimination                true
% 1.71/1.00  --res_time_limit                        2.
% 1.71/1.00  --res_out_proof                         true
% 1.71/1.00  
% 1.71/1.00  ------ Superposition Options
% 1.71/1.00  
% 1.71/1.00  --superposition_flag                    true
% 1.71/1.00  --sup_passive_queue_type                priority_queues
% 1.71/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.71/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.71/1.00  --demod_completeness_check              fast
% 1.71/1.00  --demod_use_ground                      true
% 1.71/1.00  --sup_to_prop_solver                    passive
% 1.71/1.00  --sup_prop_simpl_new                    true
% 1.71/1.00  --sup_prop_simpl_given                  true
% 1.71/1.00  --sup_fun_splitting                     false
% 1.71/1.00  --sup_smt_interval                      50000
% 1.71/1.00  
% 1.71/1.00  ------ Superposition Simplification Setup
% 1.71/1.00  
% 1.71/1.00  --sup_indices_passive                   []
% 1.71/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.71/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/1.00  --sup_full_bw                           [BwDemod]
% 1.71/1.00  --sup_immed_triv                        [TrivRules]
% 1.71/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.71/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/1.00  --sup_immed_bw_main                     []
% 1.71/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.71/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/1.00  
% 1.71/1.00  ------ Combination Options
% 1.71/1.00  
% 1.71/1.00  --comb_res_mult                         3
% 1.71/1.00  --comb_sup_mult                         2
% 1.71/1.00  --comb_inst_mult                        10
% 1.71/1.00  
% 1.71/1.00  ------ Debug Options
% 1.71/1.00  
% 1.71/1.00  --dbg_backtrace                         false
% 1.71/1.00  --dbg_dump_prop_clauses                 false
% 1.71/1.00  --dbg_dump_prop_clauses_file            -
% 1.71/1.00  --dbg_out_stat                          false
% 1.71/1.00  ------ Parsing...
% 1.71/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.71/1.00  
% 1.71/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.71/1.00  
% 1.71/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.71/1.00  
% 1.71/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.71/1.00  ------ Proving...
% 1.71/1.00  ------ Problem Properties 
% 1.71/1.00  
% 1.71/1.00  
% 1.71/1.00  clauses                                 9
% 1.71/1.00  conjectures                             1
% 1.71/1.00  EPR                                     0
% 1.71/1.00  Horn                                    9
% 1.71/1.00  unary                                   4
% 1.71/1.00  binary                                  4
% 1.71/1.00  lits                                    15
% 1.71/1.00  lits eq                                 8
% 1.71/1.00  fd_pure                                 0
% 1.71/1.00  fd_pseudo                               0
% 1.71/1.00  fd_cond                                 1
% 1.71/1.00  fd_pseudo_cond                          0
% 1.71/1.00  AC symbols                              0
% 1.71/1.00  
% 1.71/1.00  ------ Schedule dynamic 5 is on 
% 1.71/1.00  
% 1.71/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.71/1.00  
% 1.71/1.00  
% 1.71/1.00  ------ 
% 1.71/1.00  Current options:
% 1.71/1.00  ------ 
% 1.71/1.00  
% 1.71/1.00  ------ Input Options
% 1.71/1.00  
% 1.71/1.00  --out_options                           all
% 1.71/1.00  --tptp_safe_out                         true
% 1.71/1.00  --problem_path                          ""
% 1.71/1.00  --include_path                          ""
% 1.71/1.00  --clausifier                            res/vclausify_rel
% 1.71/1.00  --clausifier_options                    --mode clausify
% 1.71/1.00  --stdin                                 false
% 1.71/1.00  --stats_out                             all
% 1.71/1.00  
% 1.71/1.00  ------ General Options
% 1.71/1.00  
% 1.71/1.00  --fof                                   false
% 1.71/1.00  --time_out_real                         305.
% 1.71/1.00  --time_out_virtual                      -1.
% 1.71/1.00  --symbol_type_check                     false
% 1.71/1.00  --clausify_out                          false
% 1.71/1.00  --sig_cnt_out                           false
% 1.71/1.00  --trig_cnt_out                          false
% 1.71/1.00  --trig_cnt_out_tolerance                1.
% 1.71/1.00  --trig_cnt_out_sk_spl                   false
% 1.71/1.00  --abstr_cl_out                          false
% 1.71/1.00  
% 1.71/1.00  ------ Global Options
% 1.71/1.00  
% 1.71/1.00  --schedule                              default
% 1.71/1.00  --add_important_lit                     false
% 1.71/1.00  --prop_solver_per_cl                    1000
% 1.71/1.00  --min_unsat_core                        false
% 1.71/1.00  --soft_assumptions                      false
% 1.71/1.00  --soft_lemma_size                       3
% 1.71/1.00  --prop_impl_unit_size                   0
% 1.71/1.00  --prop_impl_unit                        []
% 1.71/1.00  --share_sel_clauses                     true
% 1.71/1.00  --reset_solvers                         false
% 1.71/1.00  --bc_imp_inh                            [conj_cone]
% 1.71/1.00  --conj_cone_tolerance                   3.
% 1.71/1.00  --extra_neg_conj                        none
% 1.71/1.00  --large_theory_mode                     true
% 1.71/1.00  --prolific_symb_bound                   200
% 1.71/1.00  --lt_threshold                          2000
% 1.71/1.00  --clause_weak_htbl                      true
% 1.71/1.00  --gc_record_bc_elim                     false
% 1.71/1.00  
% 1.71/1.00  ------ Preprocessing Options
% 1.71/1.00  
% 1.71/1.00  --preprocessing_flag                    true
% 1.71/1.00  --time_out_prep_mult                    0.1
% 1.71/1.00  --splitting_mode                        input
% 1.71/1.00  --splitting_grd                         true
% 1.71/1.00  --splitting_cvd                         false
% 1.71/1.00  --splitting_cvd_svl                     false
% 1.71/1.00  --splitting_nvd                         32
% 1.71/1.00  --sub_typing                            true
% 1.71/1.00  --prep_gs_sim                           true
% 1.71/1.00  --prep_unflatten                        true
% 1.71/1.00  --prep_res_sim                          true
% 1.71/1.00  --prep_upred                            true
% 1.71/1.00  --prep_sem_filter                       exhaustive
% 1.71/1.00  --prep_sem_filter_out                   false
% 1.71/1.00  --pred_elim                             true
% 1.71/1.00  --res_sim_input                         true
% 1.71/1.00  --eq_ax_congr_red                       true
% 1.71/1.00  --pure_diseq_elim                       true
% 1.71/1.00  --brand_transform                       false
% 1.71/1.00  --non_eq_to_eq                          false
% 1.71/1.00  --prep_def_merge                        true
% 1.71/1.00  --prep_def_merge_prop_impl              false
% 1.71/1.00  --prep_def_merge_mbd                    true
% 1.71/1.00  --prep_def_merge_tr_red                 false
% 1.71/1.00  --prep_def_merge_tr_cl                  false
% 1.71/1.00  --smt_preprocessing                     true
% 1.71/1.00  --smt_ac_axioms                         fast
% 1.71/1.00  --preprocessed_out                      false
% 1.71/1.00  --preprocessed_stats                    false
% 1.71/1.00  
% 1.71/1.00  ------ Abstraction refinement Options
% 1.71/1.00  
% 1.71/1.00  --abstr_ref                             []
% 1.71/1.00  --abstr_ref_prep                        false
% 1.71/1.00  --abstr_ref_until_sat                   false
% 1.71/1.00  --abstr_ref_sig_restrict                funpre
% 1.71/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.71/1.00  --abstr_ref_under                       []
% 1.71/1.00  
% 1.71/1.00  ------ SAT Options
% 1.71/1.00  
% 1.71/1.00  --sat_mode                              false
% 1.71/1.00  --sat_fm_restart_options                ""
% 1.71/1.00  --sat_gr_def                            false
% 1.71/1.00  --sat_epr_types                         true
% 1.71/1.00  --sat_non_cyclic_types                  false
% 1.71/1.00  --sat_finite_models                     false
% 1.71/1.00  --sat_fm_lemmas                         false
% 1.71/1.00  --sat_fm_prep                           false
% 1.71/1.00  --sat_fm_uc_incr                        true
% 1.71/1.00  --sat_out_model                         small
% 1.71/1.00  --sat_out_clauses                       false
% 1.71/1.00  
% 1.71/1.00  ------ QBF Options
% 1.71/1.00  
% 1.71/1.00  --qbf_mode                              false
% 1.71/1.00  --qbf_elim_univ                         false
% 1.71/1.00  --qbf_dom_inst                          none
% 1.71/1.00  --qbf_dom_pre_inst                      false
% 1.71/1.00  --qbf_sk_in                             false
% 1.71/1.00  --qbf_pred_elim                         true
% 1.71/1.00  --qbf_split                             512
% 1.71/1.00  
% 1.71/1.00  ------ BMC1 Options
% 1.71/1.00  
% 1.71/1.00  --bmc1_incremental                      false
% 1.71/1.00  --bmc1_axioms                           reachable_all
% 1.71/1.00  --bmc1_min_bound                        0
% 1.71/1.00  --bmc1_max_bound                        -1
% 1.71/1.00  --bmc1_max_bound_default                -1
% 1.71/1.00  --bmc1_symbol_reachability              true
% 1.71/1.00  --bmc1_property_lemmas                  false
% 1.71/1.00  --bmc1_k_induction                      false
% 1.71/1.00  --bmc1_non_equiv_states                 false
% 1.71/1.00  --bmc1_deadlock                         false
% 1.71/1.00  --bmc1_ucm                              false
% 1.71/1.00  --bmc1_add_unsat_core                   none
% 1.71/1.00  --bmc1_unsat_core_children              false
% 1.71/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.71/1.00  --bmc1_out_stat                         full
% 1.71/1.00  --bmc1_ground_init                      false
% 1.71/1.00  --bmc1_pre_inst_next_state              false
% 1.71/1.00  --bmc1_pre_inst_state                   false
% 1.71/1.00  --bmc1_pre_inst_reach_state             false
% 1.71/1.00  --bmc1_out_unsat_core                   false
% 1.71/1.00  --bmc1_aig_witness_out                  false
% 1.71/1.00  --bmc1_verbose                          false
% 1.71/1.00  --bmc1_dump_clauses_tptp                false
% 1.71/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.71/1.00  --bmc1_dump_file                        -
% 1.71/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.71/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.71/1.00  --bmc1_ucm_extend_mode                  1
% 1.71/1.00  --bmc1_ucm_init_mode                    2
% 1.71/1.00  --bmc1_ucm_cone_mode                    none
% 1.71/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.71/1.00  --bmc1_ucm_relax_model                  4
% 1.71/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.71/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.71/1.00  --bmc1_ucm_layered_model                none
% 1.71/1.00  --bmc1_ucm_max_lemma_size               10
% 1.71/1.00  
% 1.71/1.00  ------ AIG Options
% 1.71/1.00  
% 1.71/1.00  --aig_mode                              false
% 1.71/1.00  
% 1.71/1.00  ------ Instantiation Options
% 1.71/1.00  
% 1.71/1.00  --instantiation_flag                    true
% 1.71/1.00  --inst_sos_flag                         false
% 1.71/1.00  --inst_sos_phase                        true
% 1.71/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.71/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.71/1.00  --inst_lit_sel_side                     none
% 1.71/1.00  --inst_solver_per_active                1400
% 1.71/1.00  --inst_solver_calls_frac                1.
% 1.71/1.00  --inst_passive_queue_type               priority_queues
% 1.71/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.71/1.00  --inst_passive_queues_freq              [25;2]
% 1.71/1.00  --inst_dismatching                      true
% 1.71/1.00  --inst_eager_unprocessed_to_passive     true
% 1.71/1.00  --inst_prop_sim_given                   true
% 1.71/1.00  --inst_prop_sim_new                     false
% 1.71/1.00  --inst_subs_new                         false
% 1.71/1.00  --inst_eq_res_simp                      false
% 1.71/1.00  --inst_subs_given                       false
% 1.71/1.00  --inst_orphan_elimination               true
% 1.71/1.00  --inst_learning_loop_flag               true
% 1.71/1.00  --inst_learning_start                   3000
% 1.71/1.00  --inst_learning_factor                  2
% 1.71/1.00  --inst_start_prop_sim_after_learn       3
% 1.71/1.00  --inst_sel_renew                        solver
% 1.71/1.00  --inst_lit_activity_flag                true
% 1.71/1.00  --inst_restr_to_given                   false
% 1.71/1.00  --inst_activity_threshold               500
% 1.71/1.00  --inst_out_proof                        true
% 1.71/1.00  
% 1.71/1.00  ------ Resolution Options
% 1.71/1.00  
% 1.71/1.00  --resolution_flag                       false
% 1.71/1.00  --res_lit_sel                           adaptive
% 1.71/1.00  --res_lit_sel_side                      none
% 1.71/1.00  --res_ordering                          kbo
% 1.71/1.00  --res_to_prop_solver                    active
% 1.71/1.00  --res_prop_simpl_new                    false
% 1.71/1.00  --res_prop_simpl_given                  true
% 1.71/1.00  --res_passive_queue_type                priority_queues
% 1.71/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.71/1.00  --res_passive_queues_freq               [15;5]
% 1.71/1.00  --res_forward_subs                      full
% 1.71/1.00  --res_backward_subs                     full
% 1.71/1.00  --res_forward_subs_resolution           true
% 1.71/1.00  --res_backward_subs_resolution          true
% 1.71/1.00  --res_orphan_elimination                true
% 1.71/1.00  --res_time_limit                        2.
% 1.71/1.00  --res_out_proof                         true
% 1.71/1.00  
% 1.71/1.00  ------ Superposition Options
% 1.71/1.00  
% 1.71/1.00  --superposition_flag                    true
% 1.71/1.00  --sup_passive_queue_type                priority_queues
% 1.71/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.71/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.71/1.00  --demod_completeness_check              fast
% 1.71/1.00  --demod_use_ground                      true
% 1.71/1.00  --sup_to_prop_solver                    passive
% 1.71/1.00  --sup_prop_simpl_new                    true
% 1.71/1.00  --sup_prop_simpl_given                  true
% 1.71/1.00  --sup_fun_splitting                     false
% 1.71/1.00  --sup_smt_interval                      50000
% 1.71/1.00  
% 1.71/1.00  ------ Superposition Simplification Setup
% 1.71/1.00  
% 1.71/1.00  --sup_indices_passive                   []
% 1.71/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.71/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.71/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/1.00  --sup_full_bw                           [BwDemod]
% 1.71/1.00  --sup_immed_triv                        [TrivRules]
% 1.71/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.71/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/1.00  --sup_immed_bw_main                     []
% 1.71/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.71/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.71/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.71/1.00  
% 1.71/1.00  ------ Combination Options
% 1.71/1.00  
% 1.71/1.00  --comb_res_mult                         3
% 1.71/1.00  --comb_sup_mult                         2
% 1.71/1.00  --comb_inst_mult                        10
% 1.71/1.00  
% 1.71/1.00  ------ Debug Options
% 1.71/1.00  
% 1.71/1.00  --dbg_backtrace                         false
% 1.71/1.00  --dbg_dump_prop_clauses                 false
% 1.71/1.00  --dbg_dump_prop_clauses_file            -
% 1.71/1.00  --dbg_out_stat                          false
% 1.71/1.00  
% 1.71/1.00  
% 1.71/1.00  
% 1.71/1.00  
% 1.71/1.00  ------ Proving...
% 1.71/1.00  
% 1.71/1.00  
% 1.71/1.00  % SZS status Theorem for theBenchmark.p
% 1.71/1.00  
% 1.71/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.71/1.00  
% 1.71/1.00  fof(f2,axiom,(
% 1.71/1.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.71/1.00  
% 1.71/1.00  fof(f14,plain,(
% 1.71/1.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.71/1.00    inference(ennf_transformation,[],[f2])).
% 1.71/1.00  
% 1.71/1.00  fof(f27,plain,(
% 1.71/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.71/1.00    inference(cnf_transformation,[],[f14])).
% 1.71/1.00  
% 1.71/1.00  fof(f8,axiom,(
% 1.71/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1))))),
% 1.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.71/1.00  
% 1.71/1.00  fof(f21,plain,(
% 1.71/1.00    ! [X0] : (! [X1] : (((k2_struct_0(X0) != X1 | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & (k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) | k2_struct_0(X0) = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 1.71/1.00    inference(ennf_transformation,[],[f8])).
% 1.71/1.00  
% 1.71/1.00  fof(f33,plain,(
% 1.71/1.00    ( ! [X0,X1] : (k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) | k2_struct_0(X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 1.71/1.00    inference(cnf_transformation,[],[f21])).
% 1.71/1.00  
% 1.71/1.00  fof(f6,axiom,(
% 1.71/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.71/1.00  
% 1.71/1.00  fof(f19,plain,(
% 1.71/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.71/1.00    inference(ennf_transformation,[],[f6])).
% 1.71/1.00  
% 1.71/1.00  fof(f31,plain,(
% 1.71/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.71/1.00    inference(cnf_transformation,[],[f19])).
% 1.71/1.00  
% 1.71/1.00  fof(f10,conjecture,(
% 1.71/1.00    ! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 1.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.71/1.00  
% 1.71/1.00  fof(f11,negated_conjecture,(
% 1.71/1.00    ~! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 1.71/1.00    inference(negated_conjecture,[],[f10])).
% 1.71/1.00  
% 1.71/1.00  fof(f23,plain,(
% 1.71/1.00    ? [X0] : (k2_struct_0(X0) != k2_pre_topc(X0,k2_struct_0(X0)) & l1_pre_topc(X0))),
% 1.71/1.00    inference(ennf_transformation,[],[f11])).
% 1.71/1.00  
% 1.71/1.00  fof(f24,plain,(
% 1.71/1.00    ? [X0] : (k2_struct_0(X0) != k2_pre_topc(X0,k2_struct_0(X0)) & l1_pre_topc(X0)) => (k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0))),
% 1.71/1.00    introduced(choice_axiom,[])).
% 1.71/1.00  
% 1.71/1.00  fof(f25,plain,(
% 1.71/1.00    k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0)),
% 1.71/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 1.71/1.00  
% 1.71/1.00  fof(f36,plain,(
% 1.71/1.00    l1_pre_topc(sK0)),
% 1.71/1.00    inference(cnf_transformation,[],[f25])).
% 1.71/1.00  
% 1.71/1.00  fof(f1,axiom,(
% 1.71/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.71/1.00  
% 1.71/1.00  fof(f12,plain,(
% 1.71/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 1.71/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 1.71/1.00  
% 1.71/1.00  fof(f13,plain,(
% 1.71/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 1.71/1.00    inference(ennf_transformation,[],[f12])).
% 1.71/1.00  
% 1.71/1.00  fof(f26,plain,(
% 1.71/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.71/1.00    inference(cnf_transformation,[],[f13])).
% 1.71/1.00  
% 1.71/1.00  fof(f9,axiom,(
% 1.71/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 1.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.71/1.00  
% 1.71/1.00  fof(f22,plain,(
% 1.71/1.00    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.71/1.00    inference(ennf_transformation,[],[f9])).
% 1.71/1.00  
% 1.71/1.00  fof(f35,plain,(
% 1.71/1.00    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.71/1.00    inference(cnf_transformation,[],[f22])).
% 1.71/1.00  
% 1.71/1.00  fof(f4,axiom,(
% 1.71/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.71/1.00  
% 1.71/1.00  fof(f16,plain,(
% 1.71/1.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.71/1.00    inference(ennf_transformation,[],[f4])).
% 1.71/1.00  
% 1.71/1.00  fof(f17,plain,(
% 1.71/1.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.71/1.00    inference(flattening,[],[f16])).
% 1.71/1.00  
% 1.71/1.00  fof(f29,plain,(
% 1.71/1.00    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.71/1.00    inference(cnf_transformation,[],[f17])).
% 1.71/1.00  
% 1.71/1.00  fof(f37,plain,(
% 1.71/1.00    k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0))),
% 1.71/1.00    inference(cnf_transformation,[],[f25])).
% 1.71/1.00  
% 1.71/1.00  fof(f5,axiom,(
% 1.71/1.00    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.71/1.00  
% 1.71/1.00  fof(f18,plain,(
% 1.71/1.00    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 1.71/1.00    inference(ennf_transformation,[],[f5])).
% 1.71/1.00  
% 1.71/1.00  fof(f30,plain,(
% 1.71/1.00    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 1.71/1.00    inference(cnf_transformation,[],[f18])).
% 1.71/1.00  
% 1.71/1.00  cnf(c_317,plain,
% 1.71/1.00      ( X0_40 != X1_40 | X2_40 != X1_40 | X2_40 = X0_40 ),
% 1.71/1.00      theory(equality) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_903,plain,
% 1.71/1.00      ( k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) != X0_40
% 1.71/1.00      | k1_xboole_0 != X0_40
% 1.71/1.00      | k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) ),
% 1.71/1.00      inference(instantiation,[status(thm)],[c_317]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_904,plain,
% 1.71/1.00      ( k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) != k1_xboole_0
% 1.71/1.00      | k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0)))
% 1.71/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 1.71/1.00      inference(instantiation,[status(thm)],[c_903]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_1,plain,
% 1.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.71/1.00      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 1.71/1.00      inference(cnf_transformation,[],[f27]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_313,plain,
% 1.71/1.00      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
% 1.71/1.00      | k7_subset_1(X1_40,X0_40,X2_40) = k4_xboole_0(X0_40,X2_40) ),
% 1.71/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_525,plain,
% 1.71/1.00      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/1.00      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0_40) = k4_xboole_0(k2_struct_0(sK0),X0_40) ),
% 1.71/1.00      inference(instantiation,[status(thm)],[c_313]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_761,plain,
% 1.71/1.00      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/1.00      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) ),
% 1.71/1.00      inference(instantiation,[status(thm)],[c_525]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_633,plain,
% 1.71/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) != X0_40
% 1.71/1.00      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) = k1_xboole_0
% 1.71/1.00      | k1_xboole_0 != X0_40 ),
% 1.71/1.00      inference(instantiation,[status(thm)],[c_317]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_760,plain,
% 1.71/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) != k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0)))
% 1.71/1.00      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) = k1_xboole_0
% 1.71/1.00      | k1_xboole_0 != k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) ),
% 1.71/1.00      inference(instantiation,[status(thm)],[c_633]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_8,plain,
% 1.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.71/1.00      | ~ l1_struct_0(X1)
% 1.71/1.00      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0) != k1_xboole_0
% 1.71/1.00      | k2_struct_0(X1) = X0 ),
% 1.71/1.00      inference(cnf_transformation,[],[f33]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_5,plain,
% 1.71/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.71/1.00      inference(cnf_transformation,[],[f31]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_11,negated_conjecture,
% 1.71/1.00      ( l1_pre_topc(sK0) ),
% 1.71/1.00      inference(cnf_transformation,[],[f36]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_161,plain,
% 1.71/1.00      ( l1_struct_0(X0) | sK0 != X0 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_11]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_162,plain,
% 1.71/1.00      ( l1_struct_0(sK0) ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_161]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_217,plain,
% 1.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.71/1.00      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0) != k1_xboole_0
% 1.71/1.00      | k2_struct_0(X1) = X0
% 1.71/1.00      | sK0 != X1 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_162]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_218,plain,
% 1.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/1.00      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0) != k1_xboole_0
% 1.71/1.00      | k2_struct_0(sK0) = X0 ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_217]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_306,plain,
% 1.71/1.00      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/1.00      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0_40) != k1_xboole_0
% 1.71/1.00      | k2_struct_0(sK0) = X0_40 ),
% 1.71/1.00      inference(subtyping,[status(esa)],[c_218]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_541,plain,
% 1.71/1.00      ( ~ m1_subset_1(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/1.00      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) != k1_xboole_0
% 1.71/1.00      | k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
% 1.71/1.00      inference(instantiation,[status(thm)],[c_306]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_0,plain,
% 1.71/1.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 1.71/1.00      inference(cnf_transformation,[],[f26]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_9,plain,
% 1.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.71/1.00      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 1.71/1.00      | ~ l1_pre_topc(X1) ),
% 1.71/1.00      inference(cnf_transformation,[],[f35]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_142,plain,
% 1.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.71/1.00      | ~ l1_pre_topc(X1)
% 1.71/1.00      | X0 != X2
% 1.71/1.00      | k2_pre_topc(X1,X0) != X3
% 1.71/1.00      | k4_xboole_0(X2,X3) = k1_xboole_0 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_9]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_143,plain,
% 1.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.71/1.00      | ~ l1_pre_topc(X1)
% 1.71/1.00      | k4_xboole_0(X0,k2_pre_topc(X1,X0)) = k1_xboole_0 ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_142]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_168,plain,
% 1.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.71/1.00      | k4_xboole_0(X0,k2_pre_topc(X1,X0)) = k1_xboole_0
% 1.71/1.00      | sK0 != X1 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_143,c_11]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_169,plain,
% 1.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/1.00      | k4_xboole_0(X0,k2_pre_topc(sK0,X0)) = k1_xboole_0 ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_168]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_311,plain,
% 1.71/1.00      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/1.00      | k4_xboole_0(X0_40,k2_pre_topc(sK0,X0_40)) = k1_xboole_0 ),
% 1.71/1.00      inference(subtyping,[status(esa)],[c_169]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_509,plain,
% 1.71/1.00      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/1.00      | k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) = k1_xboole_0 ),
% 1.71/1.00      inference(instantiation,[status(thm)],[c_311]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_3,plain,
% 1.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.71/1.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.71/1.00      | ~ l1_pre_topc(X1) ),
% 1.71/1.00      inference(cnf_transformation,[],[f29]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_180,plain,
% 1.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.71/1.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.71/1.00      | sK0 != X1 ),
% 1.71/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_11]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_181,plain,
% 1.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/1.00      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.71/1.00      inference(unflattening,[status(thm)],[c_180]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_310,plain,
% 1.71/1.00      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/1.00      | m1_subset_1(k2_pre_topc(sK0,X0_40),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.71/1.00      inference(subtyping,[status(esa)],[c_181]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_510,plain,
% 1.71/1.00      ( m1_subset_1(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/1.00      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.71/1.00      inference(instantiation,[status(thm)],[c_310]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_10,negated_conjecture,
% 1.71/1.00      ( k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0)) ),
% 1.71/1.00      inference(cnf_transformation,[],[f37]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_312,negated_conjecture,
% 1.71/1.00      ( k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0)) ),
% 1.71/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_315,plain,( X0_40 = X0_40 ),theory(equality) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_329,plain,
% 1.71/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 1.71/1.00      inference(instantiation,[status(thm)],[c_315]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_4,plain,
% 1.71/1.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 1.71/1.00      | ~ l1_struct_0(X0) ),
% 1.71/1.00      inference(cnf_transformation,[],[f30]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_29,plain,
% 1.71/1.00      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.71/1.00      | ~ l1_struct_0(sK0) ),
% 1.71/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(c_26,plain,
% 1.71/1.00      ( ~ l1_pre_topc(sK0) | l1_struct_0(sK0) ),
% 1.71/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 1.71/1.00  
% 1.71/1.00  cnf(contradiction,plain,
% 1.71/1.00      ( $false ),
% 1.71/1.00      inference(minisat,
% 1.71/1.00                [status(thm)],
% 1.71/1.00                [c_904,c_761,c_760,c_541,c_509,c_510,c_312,c_329,c_29,
% 1.71/1.00                 c_26,c_11]) ).
% 1.71/1.00  
% 1.71/1.00  
% 1.71/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.71/1.00  
% 1.71/1.00  ------                               Statistics
% 1.71/1.00  
% 1.71/1.00  ------ General
% 1.71/1.00  
% 1.71/1.00  abstr_ref_over_cycles:                  0
% 1.71/1.00  abstr_ref_under_cycles:                 0
% 1.71/1.00  gc_basic_clause_elim:                   0
% 1.71/1.00  forced_gc_time:                         0
% 1.71/1.00  parsing_time:                           0.006
% 1.71/1.00  unif_index_cands_time:                  0.
% 1.71/1.00  unif_index_add_time:                    0.
% 1.71/1.00  orderings_time:                         0.
% 1.71/1.00  out_proof_time:                         0.006
% 1.71/1.00  total_time:                             0.041
% 1.71/1.00  num_of_symbols:                         46
% 1.71/1.00  num_of_terms:                           914
% 1.71/1.00  
% 1.71/1.00  ------ Preprocessing
% 1.71/1.00  
% 1.71/1.00  num_of_splits:                          0
% 1.71/1.00  num_of_split_atoms:                     0
% 1.71/1.00  num_of_reused_defs:                     0
% 1.71/1.00  num_eq_ax_congr_red:                    10
% 1.71/1.00  num_of_sem_filtered_clauses:            1
% 1.71/1.00  num_of_subtypes:                        3
% 1.71/1.00  monotx_restored_types:                  0
% 1.71/1.00  sat_num_of_epr_types:                   0
% 1.71/1.00  sat_num_of_non_cyclic_types:            0
% 1.71/1.00  sat_guarded_non_collapsed_types:        1
% 1.71/1.00  num_pure_diseq_elim:                    0
% 1.71/1.00  simp_replaced_by:                       0
% 1.71/1.00  res_preprocessed:                       56
% 1.71/1.00  prep_upred:                             0
% 1.71/1.00  prep_unflattend:                        10
% 1.71/1.00  smt_new_axioms:                         0
% 1.71/1.00  pred_elim_cands:                        1
% 1.71/1.00  pred_elim:                              3
% 1.71/1.00  pred_elim_cl:                           3
% 1.71/1.00  pred_elim_cycles:                       5
% 1.71/1.00  merged_defs:                            0
% 1.71/1.00  merged_defs_ncl:                        0
% 1.71/1.00  bin_hyper_res:                          0
% 1.71/1.00  prep_cycles:                            4
% 1.71/1.00  pred_elim_time:                         0.001
% 1.71/1.00  splitting_time:                         0.
% 1.71/1.00  sem_filter_time:                        0.
% 1.71/1.00  monotx_time:                            0.
% 1.71/1.00  subtype_inf_time:                       0.
% 1.71/1.00  
% 1.71/1.00  ------ Problem properties
% 1.71/1.00  
% 1.71/1.00  clauses:                                9
% 1.71/1.00  conjectures:                            1
% 1.71/1.00  epr:                                    0
% 1.71/1.00  horn:                                   9
% 1.71/1.00  ground:                                 4
% 1.71/1.00  unary:                                  4
% 1.71/1.00  binary:                                 4
% 1.71/1.00  lits:                                   15
% 1.71/1.00  lits_eq:                                8
% 1.71/1.00  fd_pure:                                0
% 1.71/1.00  fd_pseudo:                              0
% 1.71/1.00  fd_cond:                                1
% 1.71/1.00  fd_pseudo_cond:                         0
% 1.71/1.00  ac_symbols:                             0
% 1.71/1.00  
% 1.71/1.00  ------ Propositional Solver
% 1.71/1.00  
% 1.71/1.00  prop_solver_calls:                      25
% 1.71/1.00  prop_fast_solver_calls:                 260
% 1.71/1.00  smt_solver_calls:                       0
% 1.71/1.00  smt_fast_solver_calls:                  0
% 1.71/1.00  prop_num_of_clauses:                    350
% 1.71/1.00  prop_preprocess_simplified:             1538
% 1.71/1.00  prop_fo_subsumed:                       1
% 1.71/1.00  prop_solver_time:                       0.
% 1.71/1.00  smt_solver_time:                        0.
% 1.71/1.00  smt_fast_solver_time:                   0.
% 1.71/1.00  prop_fast_solver_time:                  0.
% 1.71/1.00  prop_unsat_core_time:                   0.
% 1.71/1.00  
% 1.71/1.00  ------ QBF
% 1.71/1.00  
% 1.71/1.00  qbf_q_res:                              0
% 1.71/1.00  qbf_num_tautologies:                    0
% 1.71/1.00  qbf_prep_cycles:                        0
% 1.71/1.00  
% 1.71/1.00  ------ BMC1
% 1.71/1.00  
% 1.71/1.00  bmc1_current_bound:                     -1
% 1.71/1.00  bmc1_last_solved_bound:                 -1
% 1.71/1.00  bmc1_unsat_core_size:                   -1
% 1.71/1.00  bmc1_unsat_core_parents_size:           -1
% 1.71/1.00  bmc1_merge_next_fun:                    0
% 1.71/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.71/1.00  
% 1.71/1.00  ------ Instantiation
% 1.71/1.00  
% 1.71/1.00  inst_num_of_clauses:                    97
% 1.71/1.00  inst_num_in_passive:                    14
% 1.71/1.00  inst_num_in_active:                     61
% 1.71/1.00  inst_num_in_unprocessed:                21
% 1.71/1.00  inst_num_of_loops:                      65
% 1.71/1.00  inst_num_of_learning_restarts:          0
% 1.71/1.00  inst_num_moves_active_passive:          1
% 1.71/1.00  inst_lit_activity:                      0
% 1.71/1.00  inst_lit_activity_moves:                0
% 1.71/1.00  inst_num_tautologies:                   0
% 1.71/1.00  inst_num_prop_implied:                  0
% 1.71/1.00  inst_num_existing_simplified:           0
% 1.71/1.00  inst_num_eq_res_simplified:             0
% 1.71/1.00  inst_num_child_elim:                    0
% 1.71/1.00  inst_num_of_dismatching_blockings:      3
% 1.71/1.00  inst_num_of_non_proper_insts:           56
% 1.71/1.00  inst_num_of_duplicates:                 0
% 1.71/1.00  inst_inst_num_from_inst_to_res:         0
% 1.71/1.00  inst_dismatching_checking_time:         0.
% 1.71/1.00  
% 1.71/1.00  ------ Resolution
% 1.71/1.00  
% 1.71/1.00  res_num_of_clauses:                     0
% 1.71/1.00  res_num_in_passive:                     0
% 1.71/1.00  res_num_in_active:                      0
% 1.71/1.00  res_num_of_loops:                       60
% 1.71/1.00  res_forward_subset_subsumed:            4
% 1.71/1.00  res_backward_subset_subsumed:           0
% 1.71/1.00  res_forward_subsumed:                   0
% 1.71/1.00  res_backward_subsumed:                  0
% 1.71/1.00  res_forward_subsumption_resolution:     0
% 1.71/1.00  res_backward_subsumption_resolution:    0
% 1.71/1.00  res_clause_to_clause_subsumption:       30
% 1.71/1.00  res_orphan_elimination:                 0
% 1.71/1.00  res_tautology_del:                      2
% 1.71/1.00  res_num_eq_res_simplified:              0
% 1.71/1.00  res_num_sel_changes:                    0
% 1.71/1.00  res_moves_from_active_to_pass:          0
% 1.71/1.00  
% 1.71/1.00  ------ Superposition
% 1.71/1.00  
% 1.71/1.00  sup_time_total:                         0.
% 1.71/1.00  sup_time_generating:                    0.
% 1.71/1.00  sup_time_sim_full:                      0.
% 1.71/1.00  sup_time_sim_immed:                     0.
% 1.71/1.00  
% 1.71/1.00  sup_num_of_clauses:                     19
% 1.71/1.00  sup_num_in_active:                      10
% 1.71/1.00  sup_num_in_passive:                     9
% 1.71/1.00  sup_num_of_loops:                       12
% 1.71/1.00  sup_fw_superposition:                   9
% 1.71/1.00  sup_bw_superposition:                   2
% 1.71/1.00  sup_immediate_simplified:               2
% 1.71/1.00  sup_given_eliminated:                   0
% 1.71/1.00  comparisons_done:                       0
% 1.71/1.00  comparisons_avoided:                    0
% 1.71/1.00  
% 1.71/1.00  ------ Simplifications
% 1.71/1.00  
% 1.71/1.00  
% 1.71/1.00  sim_fw_subset_subsumed:                 0
% 1.71/1.00  sim_bw_subset_subsumed:                 0
% 1.71/1.00  sim_fw_subsumed:                        0
% 1.71/1.00  sim_bw_subsumed:                        0
% 1.71/1.00  sim_fw_subsumption_res:                 0
% 1.71/1.00  sim_bw_subsumption_res:                 0
% 1.71/1.00  sim_tautology_del:                      0
% 1.71/1.00  sim_eq_tautology_del:                   0
% 1.71/1.00  sim_eq_res_simp:                        0
% 1.71/1.00  sim_fw_demodulated:                     1
% 1.71/1.00  sim_bw_demodulated:                     2
% 1.71/1.00  sim_light_normalised:                   7
% 1.71/1.00  sim_joinable_taut:                      0
% 1.71/1.00  sim_joinable_simp:                      0
% 1.71/1.00  sim_ac_normalised:                      0
% 1.71/1.00  sim_smt_subsumption:                    0
% 1.71/1.00  
%------------------------------------------------------------------------------
