%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:11 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 187 expanded)
%              Number of clauses        :   76 (  88 expanded)
%              Number of leaves         :   18 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  297 ( 559 expanded)
%              Number of equality atoms :  104 ( 112 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f26,f30])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_tops_1(X0,sK1),sK1)
        & v4_pre_topc(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,X1),X1)
          & v4_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24,f23])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
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
    inference(nnf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_511,plain,
    ( X0_43 != X1_43
    | X2_43 != X1_43
    | X2_43 = X0_43 ),
    theory(equality)).

cnf(c_8782,plain,
    ( X0_43 != X1_43
    | X0_43 = k2_pre_topc(sK0,X2_43)
    | k2_pre_topc(sK0,X2_43) != X1_43 ),
    inference(instantiation,[status(thm)],[c_511])).

cnf(c_8783,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | sK1 = k2_pre_topc(sK0,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_8782])).

cnf(c_0,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_506,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0_43,X1_43)),X0_43) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_7787,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_506])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_12,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_204,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_12])).

cnf(c_205,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_204])).

cnf(c_496,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0_43),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_205])).

cnf(c_7643,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_496])).

cnf(c_513,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | r1_tarski(X2_43,X3_43)
    | X2_43 != X0_43
    | X3_43 != X1_43 ),
    theory(equality)).

cnf(c_893,plain,
    ( r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(X2_43,X3_43)),X2_43)
    | X1_43 != X2_43
    | X0_43 != k1_setfam_1(k2_tarski(X2_43,X3_43)) ),
    inference(instantiation,[status(thm)],[c_513])).

cnf(c_990,plain,
    ( r1_tarski(k9_subset_1(X0_43,X1_43,X2_43),X3_43)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(X1_43,X2_43)),X1_43)
    | X3_43 != X1_43
    | k9_subset_1(X0_43,X1_43,X2_43) != k1_setfam_1(k2_tarski(X1_43,X2_43)) ),
    inference(instantiation,[status(thm)],[c_893])).

cnf(c_1763,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X0_43,X1_43),X2_43)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(X0_43,X1_43)),X0_43)
    | X2_43 != X0_43
    | k9_subset_1(u1_struct_0(sK0),X0_43,X1_43) != k1_setfam_1(k2_tarski(X0_43,X1_43)) ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(c_6363,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),X0_43)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k2_pre_topc(sK0,sK1))
    | X0_43 != k2_pre_topc(sK0,sK1)
    | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    inference(instantiation,[status(thm)],[c_1763])).

cnf(c_6365,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),sK1)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k2_pre_topc(sK0,sK1))
    | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
    | sK1 != k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_6363])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_503,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | r1_tarski(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1032,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0_43,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_503])).

cnf(c_4335,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1032])).

cnf(c_830,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | k2_tops_1(sK0,sK1) != X0_43
    | sK1 != X1_43 ),
    inference(instantiation,[status(thm)],[c_513])).

cnf(c_2312,plain,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),X0_43,X1_43),X2_43)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | k2_tops_1(sK0,sK1) != k9_subset_1(u1_struct_0(sK0),X0_43,X1_43)
    | sK1 != X2_43 ),
    inference(instantiation,[status(thm)],[c_830])).

cnf(c_3113,plain,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),X0_43)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | k2_tops_1(sK0,sK1) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | sK1 != X0_43 ),
    inference(instantiation,[status(thm)],[c_2312])).

cnf(c_3115,plain,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),sK1)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | k2_tops_1(sK0,sK1) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3113])).

cnf(c_516,plain,
    ( ~ m1_subset_1(X0_43,X0_44)
    | m1_subset_1(X1_43,X1_44)
    | X1_44 != X0_44
    | X1_43 != X0_43 ),
    theory(equality)).

cnf(c_883,plain,
    ( ~ m1_subset_1(X0_43,X0_44)
    | m1_subset_1(X1_43,k1_zfmisc_1(X2_43))
    | k1_zfmisc_1(X2_43) != X0_44
    | X1_43 != X0_43 ),
    inference(instantiation,[status(thm)],[c_516])).

cnf(c_1108,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | ~ m1_subset_1(k4_xboole_0(X2_43,X3_43),k1_zfmisc_1(X2_43))
    | k1_zfmisc_1(X1_43) != k1_zfmisc_1(X2_43)
    | X0_43 != k4_xboole_0(X2_43,X3_43) ),
    inference(instantiation,[status(thm)],[c_883])).

cnf(c_1716,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0_43),k1_zfmisc_1(X1_43))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),X0_43),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_zfmisc_1(X1_43) != k1_zfmisc_1(u1_struct_0(sK0))
    | k3_subset_1(u1_struct_0(sK0),X0_43) != k4_xboole_0(u1_struct_0(sK0),X0_43) ),
    inference(instantiation,[status(thm)],[c_1108])).

cnf(c_2279,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0_43),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),X0_43),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | k3_subset_1(u1_struct_0(sK0),X0_43) != k4_xboole_0(u1_struct_0(sK0),X0_43) ),
    inference(instantiation,[status(thm)],[c_1716])).

cnf(c_2281,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | k3_subset_1(u1_struct_0(sK0),sK1) != k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_2279])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_102,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_103,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_102])).

cnf(c_123,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_103])).

cnf(c_499,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | k9_subset_1(X1_43,X2_43,X0_43) = k1_setfam_1(k2_tarski(X2_43,X0_43)) ),
    inference(subtyping,[status(esa)],[c_123])).

cnf(c_1524,plain,
    ( ~ r1_tarski(X0_43,u1_struct_0(sK0))
    | k9_subset_1(u1_struct_0(sK0),X1_43,X0_43) = k1_setfam_1(k2_tarski(X1_43,X0_43)) ),
    inference(instantiation,[status(thm)],[c_499])).

cnf(c_2192,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    inference(instantiation,[status(thm)],[c_1524])).

cnf(c_504,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | ~ r1_tarski(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1051,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_43,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_504])).

cnf(c_1995,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1051])).

cnf(c_1,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_505,plain,
    ( r1_tarski(k4_xboole_0(X0_43,X1_43),X0_43) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1968,plain,
    ( r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_505])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_122,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_103])).

cnf(c_500,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | k3_subset_1(X1_43,X0_43) = k4_xboole_0(X1_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_122])).

cnf(c_1429,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_500])).

cnf(c_934,plain,
    ( X0_43 != X1_43
    | k2_tops_1(sK0,sK1) != X1_43
    | k2_tops_1(sK0,sK1) = X0_43 ),
    inference(instantiation,[status(thm)],[c_511])).

cnf(c_1085,plain,
    ( X0_43 != k2_tops_1(sK0,sK1)
    | k2_tops_1(sK0,sK1) = X0_43
    | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_934])).

cnf(c_1263,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != k2_tops_1(sK0,sK1)
    | k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1085])).

cnf(c_508,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_1206,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_508])).

cnf(c_515,plain,
    ( k1_zfmisc_1(X0_43) = k1_zfmisc_1(X1_43)
    | X0_43 != X1_43 ),
    theory(equality)).

cnf(c_1025,plain,
    ( k1_zfmisc_1(X0_43) = k1_zfmisc_1(u1_struct_0(sK0))
    | X0_43 != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_515])).

cnf(c_1041,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0))
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1025])).

cnf(c_873,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_503])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_192,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_12])).

cnf(c_193,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_192])).

cnf(c_497,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_43),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_43))) = k2_tops_1(sK0,X0_43) ),
    inference(subtyping,[status(esa)],[c_193])).

cnf(c_553,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_497])).

cnf(c_7,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_10,negated_conjecture,
    ( v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_183,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_10])).

cnf(c_184,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_183])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_186,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_184,c_12,c_11])).

cnf(c_498,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(subtyping,[status(esa)],[c_186])).

cnf(c_529,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_508])).

cnf(c_519,plain,
    ( X0_43 != X1_43
    | k2_tops_1(X0_45,X0_43) = k2_tops_1(X0_45,X1_43) ),
    theory(equality)).

cnf(c_527,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_519])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8783,c_7787,c_7643,c_6365,c_4335,c_3115,c_2281,c_2192,c_1995,c_1968,c_1429,c_1263,c_1206,c_1041,c_873,c_553,c_498,c_529,c_527,c_9,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.20/0.34  % DateTime   : Tue Dec  1 11:32:11 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 3.06/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/0.98  
% 3.06/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.06/0.98  
% 3.06/0.98  ------  iProver source info
% 3.06/0.98  
% 3.06/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.06/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.06/0.98  git: non_committed_changes: false
% 3.06/0.98  git: last_make_outside_of_git: false
% 3.06/0.98  
% 3.06/0.98  ------ 
% 3.06/0.98  
% 3.06/0.98  ------ Input Options
% 3.06/0.98  
% 3.06/0.98  --out_options                           all
% 3.06/0.98  --tptp_safe_out                         true
% 3.06/0.98  --problem_path                          ""
% 3.06/0.98  --include_path                          ""
% 3.06/0.98  --clausifier                            res/vclausify_rel
% 3.06/0.98  --clausifier_options                    ""
% 3.06/0.98  --stdin                                 false
% 3.06/0.98  --stats_out                             all
% 3.06/0.98  
% 3.06/0.98  ------ General Options
% 3.06/0.98  
% 3.06/0.98  --fof                                   false
% 3.06/0.98  --time_out_real                         305.
% 3.06/0.98  --time_out_virtual                      -1.
% 3.06/0.98  --symbol_type_check                     false
% 3.06/0.98  --clausify_out                          false
% 3.06/0.98  --sig_cnt_out                           false
% 3.06/0.98  --trig_cnt_out                          false
% 3.06/0.98  --trig_cnt_out_tolerance                1.
% 3.06/0.98  --trig_cnt_out_sk_spl                   false
% 3.06/0.98  --abstr_cl_out                          false
% 3.06/0.98  
% 3.06/0.98  ------ Global Options
% 3.06/0.98  
% 3.06/0.98  --schedule                              default
% 3.06/0.98  --add_important_lit                     false
% 3.06/0.98  --prop_solver_per_cl                    1000
% 3.06/0.98  --min_unsat_core                        false
% 3.06/0.98  --soft_assumptions                      false
% 3.06/0.98  --soft_lemma_size                       3
% 3.06/0.98  --prop_impl_unit_size                   0
% 3.06/0.98  --prop_impl_unit                        []
% 3.06/0.98  --share_sel_clauses                     true
% 3.06/0.98  --reset_solvers                         false
% 3.06/0.98  --bc_imp_inh                            [conj_cone]
% 3.06/0.98  --conj_cone_tolerance                   3.
% 3.06/0.98  --extra_neg_conj                        none
% 3.06/0.98  --large_theory_mode                     true
% 3.06/0.98  --prolific_symb_bound                   200
% 3.06/0.98  --lt_threshold                          2000
% 3.06/0.98  --clause_weak_htbl                      true
% 3.06/0.98  --gc_record_bc_elim                     false
% 3.06/0.98  
% 3.06/0.98  ------ Preprocessing Options
% 3.06/0.98  
% 3.06/0.98  --preprocessing_flag                    true
% 3.06/0.98  --time_out_prep_mult                    0.1
% 3.06/0.98  --splitting_mode                        input
% 3.06/0.98  --splitting_grd                         true
% 3.06/0.98  --splitting_cvd                         false
% 3.06/0.98  --splitting_cvd_svl                     false
% 3.06/0.98  --splitting_nvd                         32
% 3.06/0.98  --sub_typing                            true
% 3.06/0.98  --prep_gs_sim                           true
% 3.06/0.98  --prep_unflatten                        true
% 3.06/0.98  --prep_res_sim                          true
% 3.06/0.98  --prep_upred                            true
% 3.06/0.98  --prep_sem_filter                       exhaustive
% 3.06/0.98  --prep_sem_filter_out                   false
% 3.06/0.98  --pred_elim                             true
% 3.06/0.98  --res_sim_input                         true
% 3.06/0.98  --eq_ax_congr_red                       true
% 3.06/0.98  --pure_diseq_elim                       true
% 3.06/0.98  --brand_transform                       false
% 3.06/0.98  --non_eq_to_eq                          false
% 3.06/0.98  --prep_def_merge                        true
% 3.06/0.98  --prep_def_merge_prop_impl              false
% 3.06/0.98  --prep_def_merge_mbd                    true
% 3.06/0.98  --prep_def_merge_tr_red                 false
% 3.06/0.98  --prep_def_merge_tr_cl                  false
% 3.06/0.98  --smt_preprocessing                     true
% 3.06/0.98  --smt_ac_axioms                         fast
% 3.06/0.98  --preprocessed_out                      false
% 3.06/0.98  --preprocessed_stats                    false
% 3.06/0.98  
% 3.06/0.98  ------ Abstraction refinement Options
% 3.06/0.98  
% 3.06/0.98  --abstr_ref                             []
% 3.06/0.98  --abstr_ref_prep                        false
% 3.06/0.98  --abstr_ref_until_sat                   false
% 3.06/0.98  --abstr_ref_sig_restrict                funpre
% 3.06/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/0.98  --abstr_ref_under                       []
% 3.06/0.98  
% 3.06/0.98  ------ SAT Options
% 3.06/0.98  
% 3.06/0.98  --sat_mode                              false
% 3.06/0.98  --sat_fm_restart_options                ""
% 3.06/0.98  --sat_gr_def                            false
% 3.06/0.98  --sat_epr_types                         true
% 3.06/0.98  --sat_non_cyclic_types                  false
% 3.06/0.98  --sat_finite_models                     false
% 3.06/0.98  --sat_fm_lemmas                         false
% 3.06/0.98  --sat_fm_prep                           false
% 3.06/0.98  --sat_fm_uc_incr                        true
% 3.06/0.98  --sat_out_model                         small
% 3.06/0.98  --sat_out_clauses                       false
% 3.06/0.98  
% 3.06/0.98  ------ QBF Options
% 3.06/0.98  
% 3.06/0.98  --qbf_mode                              false
% 3.06/0.98  --qbf_elim_univ                         false
% 3.06/0.98  --qbf_dom_inst                          none
% 3.06/0.98  --qbf_dom_pre_inst                      false
% 3.06/0.98  --qbf_sk_in                             false
% 3.06/0.98  --qbf_pred_elim                         true
% 3.06/0.98  --qbf_split                             512
% 3.06/0.98  
% 3.06/0.98  ------ BMC1 Options
% 3.06/0.98  
% 3.06/0.98  --bmc1_incremental                      false
% 3.06/0.98  --bmc1_axioms                           reachable_all
% 3.06/0.98  --bmc1_min_bound                        0
% 3.06/0.98  --bmc1_max_bound                        -1
% 3.06/0.98  --bmc1_max_bound_default                -1
% 3.06/0.98  --bmc1_symbol_reachability              true
% 3.06/0.98  --bmc1_property_lemmas                  false
% 3.06/0.98  --bmc1_k_induction                      false
% 3.06/0.98  --bmc1_non_equiv_states                 false
% 3.06/0.98  --bmc1_deadlock                         false
% 3.06/0.98  --bmc1_ucm                              false
% 3.06/0.98  --bmc1_add_unsat_core                   none
% 3.06/0.98  --bmc1_unsat_core_children              false
% 3.06/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/0.98  --bmc1_out_stat                         full
% 3.06/0.98  --bmc1_ground_init                      false
% 3.06/0.98  --bmc1_pre_inst_next_state              false
% 3.06/0.98  --bmc1_pre_inst_state                   false
% 3.06/0.98  --bmc1_pre_inst_reach_state             false
% 3.06/0.98  --bmc1_out_unsat_core                   false
% 3.06/0.98  --bmc1_aig_witness_out                  false
% 3.06/0.98  --bmc1_verbose                          false
% 3.06/0.98  --bmc1_dump_clauses_tptp                false
% 3.06/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.06/0.98  --bmc1_dump_file                        -
% 3.06/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.06/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.06/0.98  --bmc1_ucm_extend_mode                  1
% 3.06/0.98  --bmc1_ucm_init_mode                    2
% 3.06/0.98  --bmc1_ucm_cone_mode                    none
% 3.06/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.06/0.98  --bmc1_ucm_relax_model                  4
% 3.06/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.06/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/0.98  --bmc1_ucm_layered_model                none
% 3.06/0.98  --bmc1_ucm_max_lemma_size               10
% 3.06/0.98  
% 3.06/0.98  ------ AIG Options
% 3.06/0.98  
% 3.06/0.98  --aig_mode                              false
% 3.06/0.98  
% 3.06/0.98  ------ Instantiation Options
% 3.06/0.98  
% 3.06/0.98  --instantiation_flag                    true
% 3.06/0.98  --inst_sos_flag                         true
% 3.06/0.98  --inst_sos_phase                        true
% 3.06/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/0.98  --inst_lit_sel_side                     num_symb
% 3.06/0.98  --inst_solver_per_active                1400
% 3.06/0.98  --inst_solver_calls_frac                1.
% 3.06/0.98  --inst_passive_queue_type               priority_queues
% 3.06/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/0.98  --inst_passive_queues_freq              [25;2]
% 3.06/0.98  --inst_dismatching                      true
% 3.06/0.98  --inst_eager_unprocessed_to_passive     true
% 3.06/0.98  --inst_prop_sim_given                   true
% 3.06/0.98  --inst_prop_sim_new                     false
% 3.06/0.98  --inst_subs_new                         false
% 3.06/0.98  --inst_eq_res_simp                      false
% 3.06/0.98  --inst_subs_given                       false
% 3.06/0.98  --inst_orphan_elimination               true
% 3.06/0.98  --inst_learning_loop_flag               true
% 3.06/0.98  --inst_learning_start                   3000
% 3.06/0.98  --inst_learning_factor                  2
% 3.06/0.98  --inst_start_prop_sim_after_learn       3
% 3.06/0.98  --inst_sel_renew                        solver
% 3.06/0.98  --inst_lit_activity_flag                true
% 3.06/0.98  --inst_restr_to_given                   false
% 3.06/0.98  --inst_activity_threshold               500
% 3.06/0.98  --inst_out_proof                        true
% 3.06/0.98  
% 3.06/0.98  ------ Resolution Options
% 3.06/0.98  
% 3.06/0.98  --resolution_flag                       true
% 3.06/0.98  --res_lit_sel                           adaptive
% 3.06/0.98  --res_lit_sel_side                      none
% 3.06/0.98  --res_ordering                          kbo
% 3.06/0.98  --res_to_prop_solver                    active
% 3.06/0.98  --res_prop_simpl_new                    false
% 3.06/0.98  --res_prop_simpl_given                  true
% 3.06/0.98  --res_passive_queue_type                priority_queues
% 3.06/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/0.98  --res_passive_queues_freq               [15;5]
% 3.06/0.98  --res_forward_subs                      full
% 3.06/0.98  --res_backward_subs                     full
% 3.06/0.98  --res_forward_subs_resolution           true
% 3.06/0.98  --res_backward_subs_resolution          true
% 3.06/0.98  --res_orphan_elimination                true
% 3.06/0.98  --res_time_limit                        2.
% 3.06/0.98  --res_out_proof                         true
% 3.06/0.98  
% 3.06/0.98  ------ Superposition Options
% 3.06/0.98  
% 3.06/0.98  --superposition_flag                    true
% 3.06/0.98  --sup_passive_queue_type                priority_queues
% 3.06/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.06/0.98  --demod_completeness_check              fast
% 3.06/0.98  --demod_use_ground                      true
% 3.06/0.98  --sup_to_prop_solver                    passive
% 3.06/0.98  --sup_prop_simpl_new                    true
% 3.06/0.98  --sup_prop_simpl_given                  true
% 3.06/0.98  --sup_fun_splitting                     true
% 3.06/0.98  --sup_smt_interval                      50000
% 3.06/0.98  
% 3.06/0.98  ------ Superposition Simplification Setup
% 3.06/0.98  
% 3.06/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.06/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.06/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.06/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.06/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.06/0.98  --sup_immed_triv                        [TrivRules]
% 3.06/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/0.98  --sup_immed_bw_main                     []
% 3.06/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.06/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/0.98  --sup_input_bw                          []
% 3.06/0.98  
% 3.06/0.98  ------ Combination Options
% 3.06/0.98  
% 3.06/0.98  --comb_res_mult                         3
% 3.06/0.98  --comb_sup_mult                         2
% 3.06/0.98  --comb_inst_mult                        10
% 3.06/0.98  
% 3.06/0.98  ------ Debug Options
% 3.06/0.98  
% 3.06/0.98  --dbg_backtrace                         false
% 3.06/0.98  --dbg_dump_prop_clauses                 false
% 3.06/0.98  --dbg_dump_prop_clauses_file            -
% 3.06/0.98  --dbg_out_stat                          false
% 3.06/0.98  ------ Parsing...
% 3.06/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.06/0.98  
% 3.06/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.06/0.98  
% 3.06/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.06/0.98  
% 3.06/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.06/0.98  ------ Proving...
% 3.06/0.98  ------ Problem Properties 
% 3.06/0.98  
% 3.06/0.98  
% 3.06/0.98  clauses                                 11
% 3.06/0.98  conjectures                             2
% 3.06/0.98  EPR                                     0
% 3.06/0.98  Horn                                    11
% 3.06/0.98  unary                                   5
% 3.06/0.98  binary                                  6
% 3.06/0.98  lits                                    17
% 3.06/0.98  lits eq                                 4
% 3.06/0.98  fd_pure                                 0
% 3.06/0.98  fd_pseudo                               0
% 3.06/0.98  fd_cond                                 0
% 3.06/0.98  fd_pseudo_cond                          0
% 3.06/0.98  AC symbols                              0
% 3.06/0.98  
% 3.06/0.98  ------ Schedule dynamic 5 is on 
% 3.06/0.98  
% 3.06/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.06/0.98  
% 3.06/0.98  
% 3.06/0.98  ------ 
% 3.06/0.98  Current options:
% 3.06/0.98  ------ 
% 3.06/0.98  
% 3.06/0.98  ------ Input Options
% 3.06/0.98  
% 3.06/0.98  --out_options                           all
% 3.06/0.98  --tptp_safe_out                         true
% 3.06/0.98  --problem_path                          ""
% 3.06/0.98  --include_path                          ""
% 3.06/0.98  --clausifier                            res/vclausify_rel
% 3.06/0.98  --clausifier_options                    ""
% 3.06/0.98  --stdin                                 false
% 3.06/0.98  --stats_out                             all
% 3.06/0.98  
% 3.06/0.98  ------ General Options
% 3.06/0.98  
% 3.06/0.98  --fof                                   false
% 3.06/0.98  --time_out_real                         305.
% 3.06/0.98  --time_out_virtual                      -1.
% 3.06/0.98  --symbol_type_check                     false
% 3.06/0.98  --clausify_out                          false
% 3.06/0.98  --sig_cnt_out                           false
% 3.06/0.98  --trig_cnt_out                          false
% 3.06/0.98  --trig_cnt_out_tolerance                1.
% 3.06/0.98  --trig_cnt_out_sk_spl                   false
% 3.06/0.98  --abstr_cl_out                          false
% 3.06/0.98  
% 3.06/0.98  ------ Global Options
% 3.06/0.98  
% 3.06/0.98  --schedule                              default
% 3.06/0.98  --add_important_lit                     false
% 3.06/0.98  --prop_solver_per_cl                    1000
% 3.06/0.98  --min_unsat_core                        false
% 3.06/0.98  --soft_assumptions                      false
% 3.06/0.98  --soft_lemma_size                       3
% 3.06/0.98  --prop_impl_unit_size                   0
% 3.06/0.98  --prop_impl_unit                        []
% 3.06/0.98  --share_sel_clauses                     true
% 3.06/0.98  --reset_solvers                         false
% 3.06/0.98  --bc_imp_inh                            [conj_cone]
% 3.06/0.98  --conj_cone_tolerance                   3.
% 3.06/0.98  --extra_neg_conj                        none
% 3.06/0.98  --large_theory_mode                     true
% 3.06/0.98  --prolific_symb_bound                   200
% 3.06/0.98  --lt_threshold                          2000
% 3.06/0.98  --clause_weak_htbl                      true
% 3.06/0.98  --gc_record_bc_elim                     false
% 3.06/0.98  
% 3.06/0.98  ------ Preprocessing Options
% 3.06/0.98  
% 3.06/0.98  --preprocessing_flag                    true
% 3.06/0.98  --time_out_prep_mult                    0.1
% 3.06/0.98  --splitting_mode                        input
% 3.06/0.98  --splitting_grd                         true
% 3.06/0.98  --splitting_cvd                         false
% 3.06/0.98  --splitting_cvd_svl                     false
% 3.06/0.98  --splitting_nvd                         32
% 3.06/0.98  --sub_typing                            true
% 3.06/0.98  --prep_gs_sim                           true
% 3.06/0.98  --prep_unflatten                        true
% 3.06/0.98  --prep_res_sim                          true
% 3.06/0.98  --prep_upred                            true
% 3.06/0.98  --prep_sem_filter                       exhaustive
% 3.06/0.98  --prep_sem_filter_out                   false
% 3.06/0.98  --pred_elim                             true
% 3.06/0.98  --res_sim_input                         true
% 3.06/0.98  --eq_ax_congr_red                       true
% 3.06/0.98  --pure_diseq_elim                       true
% 3.06/0.98  --brand_transform                       false
% 3.06/0.98  --non_eq_to_eq                          false
% 3.06/0.98  --prep_def_merge                        true
% 3.06/0.98  --prep_def_merge_prop_impl              false
% 3.06/0.98  --prep_def_merge_mbd                    true
% 3.06/0.98  --prep_def_merge_tr_red                 false
% 3.06/0.98  --prep_def_merge_tr_cl                  false
% 3.06/0.98  --smt_preprocessing                     true
% 3.06/0.98  --smt_ac_axioms                         fast
% 3.06/0.98  --preprocessed_out                      false
% 3.06/0.98  --preprocessed_stats                    false
% 3.06/0.98  
% 3.06/0.98  ------ Abstraction refinement Options
% 3.06/0.98  
% 3.06/0.98  --abstr_ref                             []
% 3.06/0.98  --abstr_ref_prep                        false
% 3.06/0.98  --abstr_ref_until_sat                   false
% 3.06/0.98  --abstr_ref_sig_restrict                funpre
% 3.06/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/0.98  --abstr_ref_under                       []
% 3.06/0.98  
% 3.06/0.98  ------ SAT Options
% 3.06/0.98  
% 3.06/0.98  --sat_mode                              false
% 3.06/0.98  --sat_fm_restart_options                ""
% 3.06/0.98  --sat_gr_def                            false
% 3.06/0.98  --sat_epr_types                         true
% 3.06/0.98  --sat_non_cyclic_types                  false
% 3.06/0.98  --sat_finite_models                     false
% 3.06/0.98  --sat_fm_lemmas                         false
% 3.06/0.98  --sat_fm_prep                           false
% 3.06/0.98  --sat_fm_uc_incr                        true
% 3.06/0.98  --sat_out_model                         small
% 3.06/0.98  --sat_out_clauses                       false
% 3.06/0.98  
% 3.06/0.98  ------ QBF Options
% 3.06/0.98  
% 3.06/0.98  --qbf_mode                              false
% 3.06/0.98  --qbf_elim_univ                         false
% 3.06/0.98  --qbf_dom_inst                          none
% 3.06/0.98  --qbf_dom_pre_inst                      false
% 3.06/0.98  --qbf_sk_in                             false
% 3.06/0.98  --qbf_pred_elim                         true
% 3.06/0.98  --qbf_split                             512
% 3.06/0.98  
% 3.06/0.98  ------ BMC1 Options
% 3.06/0.98  
% 3.06/0.98  --bmc1_incremental                      false
% 3.06/0.98  --bmc1_axioms                           reachable_all
% 3.06/0.98  --bmc1_min_bound                        0
% 3.06/0.98  --bmc1_max_bound                        -1
% 3.06/0.98  --bmc1_max_bound_default                -1
% 3.06/0.98  --bmc1_symbol_reachability              true
% 3.06/0.98  --bmc1_property_lemmas                  false
% 3.06/0.98  --bmc1_k_induction                      false
% 3.06/0.98  --bmc1_non_equiv_states                 false
% 3.06/0.98  --bmc1_deadlock                         false
% 3.06/0.98  --bmc1_ucm                              false
% 3.06/0.98  --bmc1_add_unsat_core                   none
% 3.06/0.98  --bmc1_unsat_core_children              false
% 3.06/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/0.98  --bmc1_out_stat                         full
% 3.06/0.98  --bmc1_ground_init                      false
% 3.06/0.98  --bmc1_pre_inst_next_state              false
% 3.06/0.98  --bmc1_pre_inst_state                   false
% 3.06/0.98  --bmc1_pre_inst_reach_state             false
% 3.06/0.98  --bmc1_out_unsat_core                   false
% 3.06/0.98  --bmc1_aig_witness_out                  false
% 3.06/0.98  --bmc1_verbose                          false
% 3.06/0.98  --bmc1_dump_clauses_tptp                false
% 3.06/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.06/0.98  --bmc1_dump_file                        -
% 3.06/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.06/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.06/0.98  --bmc1_ucm_extend_mode                  1
% 3.06/0.98  --bmc1_ucm_init_mode                    2
% 3.06/0.98  --bmc1_ucm_cone_mode                    none
% 3.06/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.06/0.98  --bmc1_ucm_relax_model                  4
% 3.06/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.06/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/0.98  --bmc1_ucm_layered_model                none
% 3.06/0.98  --bmc1_ucm_max_lemma_size               10
% 3.06/0.98  
% 3.06/0.98  ------ AIG Options
% 3.06/0.98  
% 3.06/0.98  --aig_mode                              false
% 3.06/0.98  
% 3.06/0.98  ------ Instantiation Options
% 3.06/0.98  
% 3.06/0.98  --instantiation_flag                    true
% 3.06/0.98  --inst_sos_flag                         true
% 3.06/0.98  --inst_sos_phase                        true
% 3.06/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/0.98  --inst_lit_sel_side                     none
% 3.06/0.98  --inst_solver_per_active                1400
% 3.06/0.98  --inst_solver_calls_frac                1.
% 3.06/0.98  --inst_passive_queue_type               priority_queues
% 3.06/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/0.98  --inst_passive_queues_freq              [25;2]
% 3.06/0.98  --inst_dismatching                      true
% 3.06/0.98  --inst_eager_unprocessed_to_passive     true
% 3.06/0.98  --inst_prop_sim_given                   true
% 3.06/0.98  --inst_prop_sim_new                     false
% 3.06/0.98  --inst_subs_new                         false
% 3.06/0.98  --inst_eq_res_simp                      false
% 3.06/0.98  --inst_subs_given                       false
% 3.06/0.98  --inst_orphan_elimination               true
% 3.06/0.98  --inst_learning_loop_flag               true
% 3.06/0.98  --inst_learning_start                   3000
% 3.06/0.98  --inst_learning_factor                  2
% 3.06/0.98  --inst_start_prop_sim_after_learn       3
% 3.06/0.98  --inst_sel_renew                        solver
% 3.06/0.98  --inst_lit_activity_flag                true
% 3.06/0.98  --inst_restr_to_given                   false
% 3.06/0.98  --inst_activity_threshold               500
% 3.06/0.98  --inst_out_proof                        true
% 3.06/0.98  
% 3.06/0.98  ------ Resolution Options
% 3.06/0.98  
% 3.06/0.98  --resolution_flag                       false
% 3.06/0.98  --res_lit_sel                           adaptive
% 3.06/0.98  --res_lit_sel_side                      none
% 3.06/0.98  --res_ordering                          kbo
% 3.06/0.98  --res_to_prop_solver                    active
% 3.06/0.98  --res_prop_simpl_new                    false
% 3.06/0.98  --res_prop_simpl_given                  true
% 3.06/0.98  --res_passive_queue_type                priority_queues
% 3.06/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/0.98  --res_passive_queues_freq               [15;5]
% 3.06/0.98  --res_forward_subs                      full
% 3.06/0.98  --res_backward_subs                     full
% 3.06/0.98  --res_forward_subs_resolution           true
% 3.06/0.98  --res_backward_subs_resolution          true
% 3.06/0.98  --res_orphan_elimination                true
% 3.06/0.98  --res_time_limit                        2.
% 3.06/0.98  --res_out_proof                         true
% 3.06/0.98  
% 3.06/0.98  ------ Superposition Options
% 3.06/0.98  
% 3.06/0.98  --superposition_flag                    true
% 3.06/0.98  --sup_passive_queue_type                priority_queues
% 3.06/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.06/0.98  --demod_completeness_check              fast
% 3.06/0.98  --demod_use_ground                      true
% 3.06/0.98  --sup_to_prop_solver                    passive
% 3.06/0.98  --sup_prop_simpl_new                    true
% 3.06/0.98  --sup_prop_simpl_given                  true
% 3.06/0.98  --sup_fun_splitting                     true
% 3.06/0.98  --sup_smt_interval                      50000
% 3.06/0.98  
% 3.06/0.98  ------ Superposition Simplification Setup
% 3.06/0.98  
% 3.06/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.06/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.06/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.06/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.06/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.06/0.98  --sup_immed_triv                        [TrivRules]
% 3.06/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/0.98  --sup_immed_bw_main                     []
% 3.06/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.06/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/0.98  --sup_input_bw                          []
% 3.06/0.98  
% 3.06/0.98  ------ Combination Options
% 3.06/0.98  
% 3.06/0.98  --comb_res_mult                         3
% 3.06/0.98  --comb_sup_mult                         2
% 3.06/0.98  --comb_inst_mult                        10
% 3.06/0.98  
% 3.06/0.98  ------ Debug Options
% 3.06/0.98  
% 3.06/0.98  --dbg_backtrace                         false
% 3.06/0.98  --dbg_dump_prop_clauses                 false
% 3.06/0.98  --dbg_dump_prop_clauses_file            -
% 3.06/0.98  --dbg_out_stat                          false
% 3.06/0.98  
% 3.06/0.98  
% 3.06/0.98  
% 3.06/0.98  
% 3.06/0.98  ------ Proving...
% 3.06/0.98  
% 3.06/0.98  
% 3.06/0.98  % SZS status Theorem for theBenchmark.p
% 3.06/0.98  
% 3.06/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.06/0.98  
% 3.06/0.98  fof(f1,axiom,(
% 3.06/0.98    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f26,plain,(
% 3.06/0.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.06/0.98    inference(cnf_transformation,[],[f1])).
% 3.06/0.98  
% 3.06/0.98  fof(f5,axiom,(
% 3.06/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f30,plain,(
% 3.06/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.06/0.98    inference(cnf_transformation,[],[f5])).
% 3.06/0.98  
% 3.06/0.98  fof(f40,plain,(
% 3.06/0.98    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 3.06/0.98    inference(definition_unfolding,[],[f26,f30])).
% 3.06/0.98  
% 3.06/0.98  fof(f7,axiom,(
% 3.06/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f15,plain,(
% 3.06/0.98    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.06/0.98    inference(ennf_transformation,[],[f7])).
% 3.06/0.98  
% 3.06/0.98  fof(f16,plain,(
% 3.06/0.98    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.06/0.98    inference(flattening,[],[f15])).
% 3.06/0.98  
% 3.06/0.98  fof(f33,plain,(
% 3.06/0.98    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.06/0.98    inference(cnf_transformation,[],[f16])).
% 3.06/0.98  
% 3.06/0.98  fof(f10,conjecture,(
% 3.06/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f11,negated_conjecture,(
% 3.06/0.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 3.06/0.98    inference(negated_conjecture,[],[f10])).
% 3.06/0.98  
% 3.06/0.98  fof(f20,plain,(
% 3.06/0.98    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.06/0.98    inference(ennf_transformation,[],[f11])).
% 3.06/0.98  
% 3.06/0.98  fof(f21,plain,(
% 3.06/0.98    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.06/0.98    inference(flattening,[],[f20])).
% 3.06/0.98  
% 3.06/0.98  fof(f24,plain,(
% 3.06/0.98    ( ! [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_tops_1(X0,sK1),sK1) & v4_pre_topc(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.06/0.98    introduced(choice_axiom,[])).
% 3.06/0.98  
% 3.06/0.98  fof(f23,plain,(
% 3.06/0.98    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),X1) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.06/0.98    introduced(choice_axiom,[])).
% 3.06/0.98  
% 3.06/0.98  fof(f25,plain,(
% 3.06/0.98    (~r1_tarski(k2_tops_1(sK0,sK1),sK1) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.06/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24,f23])).
% 3.06/0.98  
% 3.06/0.98  fof(f36,plain,(
% 3.06/0.98    l1_pre_topc(sK0)),
% 3.06/0.98    inference(cnf_transformation,[],[f25])).
% 3.06/0.98  
% 3.06/0.98  fof(f6,axiom,(
% 3.06/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f22,plain,(
% 3.06/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.06/0.98    inference(nnf_transformation,[],[f6])).
% 3.06/0.98  
% 3.06/0.98  fof(f31,plain,(
% 3.06/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.06/0.98    inference(cnf_transformation,[],[f22])).
% 3.06/0.98  
% 3.06/0.98  fof(f4,axiom,(
% 3.06/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f14,plain,(
% 3.06/0.98    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.06/0.98    inference(ennf_transformation,[],[f4])).
% 3.06/0.98  
% 3.06/0.98  fof(f29,plain,(
% 3.06/0.98    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.06/0.98    inference(cnf_transformation,[],[f14])).
% 3.06/0.98  
% 3.06/0.98  fof(f41,plain,(
% 3.06/0.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.06/0.98    inference(definition_unfolding,[],[f29,f30])).
% 3.06/0.98  
% 3.06/0.98  fof(f32,plain,(
% 3.06/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.06/0.98    inference(cnf_transformation,[],[f22])).
% 3.06/0.98  
% 3.06/0.98  fof(f2,axiom,(
% 3.06/0.98    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f27,plain,(
% 3.06/0.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.06/0.98    inference(cnf_transformation,[],[f2])).
% 3.06/0.98  
% 3.06/0.98  fof(f3,axiom,(
% 3.06/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f13,plain,(
% 3.06/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.06/0.98    inference(ennf_transformation,[],[f3])).
% 3.06/0.98  
% 3.06/0.98  fof(f28,plain,(
% 3.06/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.06/0.98    inference(cnf_transformation,[],[f13])).
% 3.06/0.98  
% 3.06/0.98  fof(f9,axiom,(
% 3.06/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)))),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f19,plain,(
% 3.06/0.98    ! [X0] : (! [X1] : (k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.06/0.98    inference(ennf_transformation,[],[f9])).
% 3.06/0.98  
% 3.06/0.98  fof(f35,plain,(
% 3.06/0.98    ( ! [X0,X1] : (k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.06/0.98    inference(cnf_transformation,[],[f19])).
% 3.06/0.98  
% 3.06/0.98  fof(f8,axiom,(
% 3.06/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.06/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.98  
% 3.06/0.98  fof(f12,plain,(
% 3.06/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 3.06/0.98    inference(pure_predicate_removal,[],[f8])).
% 3.06/0.98  
% 3.06/0.98  fof(f17,plain,(
% 3.06/0.98    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.06/0.98    inference(ennf_transformation,[],[f12])).
% 3.06/0.98  
% 3.06/0.98  fof(f18,plain,(
% 3.06/0.98    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.06/0.98    inference(flattening,[],[f17])).
% 3.06/0.98  
% 3.06/0.98  fof(f34,plain,(
% 3.06/0.98    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.06/0.98    inference(cnf_transformation,[],[f18])).
% 3.06/0.98  
% 3.06/0.98  fof(f38,plain,(
% 3.06/0.98    v4_pre_topc(sK1,sK0)),
% 3.06/0.98    inference(cnf_transformation,[],[f25])).
% 3.06/0.98  
% 3.06/0.98  fof(f37,plain,(
% 3.06/0.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.06/0.98    inference(cnf_transformation,[],[f25])).
% 3.06/0.98  
% 3.06/0.98  fof(f39,plain,(
% 3.06/0.98    ~r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 3.06/0.98    inference(cnf_transformation,[],[f25])).
% 3.06/0.98  
% 3.06/0.98  cnf(c_511,plain,
% 3.06/0.98      ( X0_43 != X1_43 | X2_43 != X1_43 | X2_43 = X0_43 ),
% 3.06/0.98      theory(equality) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_8782,plain,
% 3.06/0.98      ( X0_43 != X1_43
% 3.06/0.98      | X0_43 = k2_pre_topc(sK0,X2_43)
% 3.06/0.98      | k2_pre_topc(sK0,X2_43) != X1_43 ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_511]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_8783,plain,
% 3.06/0.98      ( k2_pre_topc(sK0,sK1) != sK1
% 3.06/0.98      | sK1 = k2_pre_topc(sK0,sK1)
% 3.06/0.98      | sK1 != sK1 ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_8782]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_0,plain,
% 3.06/0.98      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 3.06/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_506,plain,
% 3.06/0.98      ( r1_tarski(k1_setfam_1(k2_tarski(X0_43,X1_43)),X0_43) ),
% 3.06/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_7787,plain,
% 3.06/0.98      ( r1_tarski(k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k2_pre_topc(sK0,sK1)) ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_506]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_6,plain,
% 3.06/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.06/0.98      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.06/0.98      | ~ l1_pre_topc(X1) ),
% 3.06/0.98      inference(cnf_transformation,[],[f33]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_12,negated_conjecture,
% 3.06/0.98      ( l1_pre_topc(sK0) ),
% 3.06/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_204,plain,
% 3.06/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.06/0.98      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.06/0.98      | sK0 != X1 ),
% 3.06/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_12]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_205,plain,
% 3.06/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.06/0.98      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.06/0.98      inference(unflattening,[status(thm)],[c_204]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_496,plain,
% 3.06/0.98      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.06/0.98      | m1_subset_1(k2_pre_topc(sK0,X0_43),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.06/0.98      inference(subtyping,[status(esa)],[c_205]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_7643,plain,
% 3.06/0.98      ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.06/0.98      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_496]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_513,plain,
% 3.06/0.98      ( ~ r1_tarski(X0_43,X1_43)
% 3.06/0.98      | r1_tarski(X2_43,X3_43)
% 3.06/0.98      | X2_43 != X0_43
% 3.06/0.98      | X3_43 != X1_43 ),
% 3.06/0.98      theory(equality) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_893,plain,
% 3.06/0.98      ( r1_tarski(X0_43,X1_43)
% 3.06/0.98      | ~ r1_tarski(k1_setfam_1(k2_tarski(X2_43,X3_43)),X2_43)
% 3.06/0.98      | X1_43 != X2_43
% 3.06/0.98      | X0_43 != k1_setfam_1(k2_tarski(X2_43,X3_43)) ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_513]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_990,plain,
% 3.06/0.98      ( r1_tarski(k9_subset_1(X0_43,X1_43,X2_43),X3_43)
% 3.06/0.98      | ~ r1_tarski(k1_setfam_1(k2_tarski(X1_43,X2_43)),X1_43)
% 3.06/0.98      | X3_43 != X1_43
% 3.06/0.98      | k9_subset_1(X0_43,X1_43,X2_43) != k1_setfam_1(k2_tarski(X1_43,X2_43)) ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_893]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_1763,plain,
% 3.06/0.98      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X0_43,X1_43),X2_43)
% 3.06/0.98      | ~ r1_tarski(k1_setfam_1(k2_tarski(X0_43,X1_43)),X0_43)
% 3.06/0.98      | X2_43 != X0_43
% 3.06/0.98      | k9_subset_1(u1_struct_0(sK0),X0_43,X1_43) != k1_setfam_1(k2_tarski(X0_43,X1_43)) ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_990]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_6363,plain,
% 3.06/0.98      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),X0_43)
% 3.06/0.98      | ~ r1_tarski(k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k2_pre_topc(sK0,sK1))
% 3.06/0.98      | X0_43 != k2_pre_topc(sK0,sK1)
% 3.06/0.98      | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_1763]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_6365,plain,
% 3.06/0.98      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),sK1)
% 3.06/0.98      | ~ r1_tarski(k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k2_pre_topc(sK0,sK1))
% 3.06/0.98      | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
% 3.06/0.98      | sK1 != k2_pre_topc(sK0,sK1) ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_6363]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_5,plain,
% 3.06/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.06/0.98      inference(cnf_transformation,[],[f31]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_503,plain,
% 3.06/0.98      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 3.06/0.98      | r1_tarski(X0_43,X1_43) ),
% 3.06/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_1032,plain,
% 3.06/0.98      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.06/0.98      | r1_tarski(X0_43,u1_struct_0(sK0)) ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_503]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_4335,plain,
% 3.06/0.98      ( ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.06/0.98      | r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_1032]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_830,plain,
% 3.06/0.98      ( ~ r1_tarski(X0_43,X1_43)
% 3.06/0.98      | r1_tarski(k2_tops_1(sK0,sK1),sK1)
% 3.06/0.98      | k2_tops_1(sK0,sK1) != X0_43
% 3.06/0.98      | sK1 != X1_43 ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_513]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_2312,plain,
% 3.06/0.98      ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),X0_43,X1_43),X2_43)
% 3.06/0.98      | r1_tarski(k2_tops_1(sK0,sK1),sK1)
% 3.06/0.98      | k2_tops_1(sK0,sK1) != k9_subset_1(u1_struct_0(sK0),X0_43,X1_43)
% 3.06/0.98      | sK1 != X2_43 ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_830]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_3113,plain,
% 3.06/0.98      ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),X0_43)
% 3.06/0.98      | r1_tarski(k2_tops_1(sK0,sK1),sK1)
% 3.06/0.98      | k2_tops_1(sK0,sK1) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
% 3.06/0.98      | sK1 != X0_43 ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_2312]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_3115,plain,
% 3.06/0.98      ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),sK1)
% 3.06/0.98      | r1_tarski(k2_tops_1(sK0,sK1),sK1)
% 3.06/0.98      | k2_tops_1(sK0,sK1) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
% 3.06/0.98      | sK1 != sK1 ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_3113]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_516,plain,
% 3.06/0.98      ( ~ m1_subset_1(X0_43,X0_44)
% 3.06/0.98      | m1_subset_1(X1_43,X1_44)
% 3.06/0.98      | X1_44 != X0_44
% 3.06/0.98      | X1_43 != X0_43 ),
% 3.06/0.98      theory(equality) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_883,plain,
% 3.06/0.98      ( ~ m1_subset_1(X0_43,X0_44)
% 3.06/0.98      | m1_subset_1(X1_43,k1_zfmisc_1(X2_43))
% 3.06/0.98      | k1_zfmisc_1(X2_43) != X0_44
% 3.06/0.98      | X1_43 != X0_43 ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_516]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_1108,plain,
% 3.06/0.98      ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 3.06/0.98      | ~ m1_subset_1(k4_xboole_0(X2_43,X3_43),k1_zfmisc_1(X2_43))
% 3.06/0.98      | k1_zfmisc_1(X1_43) != k1_zfmisc_1(X2_43)
% 3.06/0.98      | X0_43 != k4_xboole_0(X2_43,X3_43) ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_883]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_1716,plain,
% 3.06/0.98      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0_43),k1_zfmisc_1(X1_43))
% 3.06/0.98      | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),X0_43),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.06/0.98      | k1_zfmisc_1(X1_43) != k1_zfmisc_1(u1_struct_0(sK0))
% 3.06/0.98      | k3_subset_1(u1_struct_0(sK0),X0_43) != k4_xboole_0(u1_struct_0(sK0),X0_43) ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_1108]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_2279,plain,
% 3.06/0.98      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0_43),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.06/0.98      | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),X0_43),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.06/0.98      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
% 3.06/0.98      | k3_subset_1(u1_struct_0(sK0),X0_43) != k4_xboole_0(u1_struct_0(sK0),X0_43) ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_1716]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_2281,plain,
% 3.06/0.98      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.06/0.98      | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.06/0.98      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
% 3.06/0.98      | k3_subset_1(u1_struct_0(sK0),sK1) != k4_xboole_0(u1_struct_0(sK0),sK1) ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_2279]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_3,plain,
% 3.06/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.06/0.98      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 3.06/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_4,plain,
% 3.06/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.06/0.98      inference(cnf_transformation,[],[f32]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_102,plain,
% 3.06/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.06/0.98      inference(prop_impl,[status(thm)],[c_4]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_103,plain,
% 3.06/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.06/0.98      inference(renaming,[status(thm)],[c_102]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_123,plain,
% 3.06/0.98      ( ~ r1_tarski(X0,X1)
% 3.06/0.98      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 3.06/0.98      inference(bin_hyper_res,[status(thm)],[c_3,c_103]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_499,plain,
% 3.06/0.98      ( ~ r1_tarski(X0_43,X1_43)
% 3.06/0.98      | k9_subset_1(X1_43,X2_43,X0_43) = k1_setfam_1(k2_tarski(X2_43,X0_43)) ),
% 3.06/0.98      inference(subtyping,[status(esa)],[c_123]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_1524,plain,
% 3.06/0.98      ( ~ r1_tarski(X0_43,u1_struct_0(sK0))
% 3.06/0.98      | k9_subset_1(u1_struct_0(sK0),X1_43,X0_43) = k1_setfam_1(k2_tarski(X1_43,X0_43)) ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_499]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_2192,plain,
% 3.06/0.98      ( ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
% 3.06/0.98      | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_1524]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_504,plain,
% 3.06/0.98      ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
% 3.06/0.98      | ~ r1_tarski(X0_43,X1_43) ),
% 3.06/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_1051,plain,
% 3.06/0.98      ( m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.06/0.98      | ~ r1_tarski(X0_43,u1_struct_0(sK0)) ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_504]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_1995,plain,
% 3.06/0.98      ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.06/0.98      | ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_1051]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_1,plain,
% 3.06/0.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.06/0.98      inference(cnf_transformation,[],[f27]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_505,plain,
% 3.06/0.98      ( r1_tarski(k4_xboole_0(X0_43,X1_43),X0_43) ),
% 3.06/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_1968,plain,
% 3.06/0.98      ( r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_505]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_2,plain,
% 3.06/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.06/0.98      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.06/0.98      inference(cnf_transformation,[],[f28]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_122,plain,
% 3.06/0.98      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.06/0.98      inference(bin_hyper_res,[status(thm)],[c_2,c_103]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_500,plain,
% 3.06/0.98      ( ~ r1_tarski(X0_43,X1_43)
% 3.06/0.98      | k3_subset_1(X1_43,X0_43) = k4_xboole_0(X1_43,X0_43) ),
% 3.06/0.98      inference(subtyping,[status(esa)],[c_122]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_1429,plain,
% 3.06/0.98      ( ~ r1_tarski(sK1,u1_struct_0(sK0))
% 3.06/0.98      | k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_500]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_934,plain,
% 3.06/0.98      ( X0_43 != X1_43
% 3.06/0.98      | k2_tops_1(sK0,sK1) != X1_43
% 3.06/0.98      | k2_tops_1(sK0,sK1) = X0_43 ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_511]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_1085,plain,
% 3.06/0.98      ( X0_43 != k2_tops_1(sK0,sK1)
% 3.06/0.98      | k2_tops_1(sK0,sK1) = X0_43
% 3.06/0.98      | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_934]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_1263,plain,
% 3.06/0.98      ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != k2_tops_1(sK0,sK1)
% 3.06/0.98      | k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
% 3.06/0.98      | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_1085]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_508,plain,( X0_43 = X0_43 ),theory(equality) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_1206,plain,
% 3.06/0.98      ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_508]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_515,plain,
% 3.06/0.98      ( k1_zfmisc_1(X0_43) = k1_zfmisc_1(X1_43) | X0_43 != X1_43 ),
% 3.06/0.98      theory(equality) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_1025,plain,
% 3.06/0.98      ( k1_zfmisc_1(X0_43) = k1_zfmisc_1(u1_struct_0(sK0))
% 3.06/0.98      | X0_43 != u1_struct_0(sK0) ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_515]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_1041,plain,
% 3.06/0.98      ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0))
% 3.06/0.98      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_1025]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_873,plain,
% 3.06/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.06/0.98      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 3.06/0.98      inference(instantiation,[status(thm)],[c_503]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_8,plain,
% 3.06/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.06/0.98      | ~ l1_pre_topc(X1)
% 3.06/0.98      | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0) ),
% 3.06/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_192,plain,
% 3.06/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.06/0.98      | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0)
% 3.06/0.98      | sK0 != X1 ),
% 3.06/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_12]) ).
% 3.06/0.98  
% 3.06/0.98  cnf(c_193,plain,
% 3.06/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.06/0.98      | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_tops_1(sK0,X0) ),
% 3.06/0.99      inference(unflattening,[status(thm)],[c_192]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_497,plain,
% 3.06/0.99      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.06/0.99      | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_43),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0_43))) = k2_tops_1(sK0,X0_43) ),
% 3.06/0.99      inference(subtyping,[status(esa)],[c_193]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_553,plain,
% 3.06/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.06/0.99      | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
% 3.06/0.99      inference(instantiation,[status(thm)],[c_497]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_7,plain,
% 3.06/0.99      ( ~ v4_pre_topc(X0,X1)
% 3.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.06/0.99      | ~ l1_pre_topc(X1)
% 3.06/0.99      | k2_pre_topc(X1,X0) = X0 ),
% 3.06/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_10,negated_conjecture,
% 3.06/0.99      ( v4_pre_topc(sK1,sK0) ),
% 3.06/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_183,plain,
% 3.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.06/0.99      | ~ l1_pre_topc(X1)
% 3.06/0.99      | k2_pre_topc(X1,X0) = X0
% 3.06/0.99      | sK1 != X0
% 3.06/0.99      | sK0 != X1 ),
% 3.06/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_10]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_184,plain,
% 3.06/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.06/0.99      | ~ l1_pre_topc(sK0)
% 3.06/0.99      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.06/0.99      inference(unflattening,[status(thm)],[c_183]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_11,negated_conjecture,
% 3.06/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.06/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_186,plain,
% 3.06/0.99      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 3.06/0.99      inference(global_propositional_subsumption,
% 3.06/0.99                [status(thm)],
% 3.06/0.99                [c_184,c_12,c_11]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_498,plain,
% 3.06/0.99      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 3.06/0.99      inference(subtyping,[status(esa)],[c_186]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_529,plain,
% 3.06/0.99      ( sK1 = sK1 ),
% 3.06/0.99      inference(instantiation,[status(thm)],[c_508]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_519,plain,
% 3.06/0.99      ( X0_43 != X1_43
% 3.06/0.99      | k2_tops_1(X0_45,X0_43) = k2_tops_1(X0_45,X1_43) ),
% 3.06/0.99      theory(equality) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_527,plain,
% 3.06/0.99      ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,sK1) | sK1 != sK1 ),
% 3.06/0.99      inference(instantiation,[status(thm)],[c_519]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(c_9,negated_conjecture,
% 3.06/0.99      ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
% 3.06/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.06/0.99  
% 3.06/0.99  cnf(contradiction,plain,
% 3.06/0.99      ( $false ),
% 3.06/0.99      inference(minisat,
% 3.06/0.99                [status(thm)],
% 3.06/0.99                [c_8783,c_7787,c_7643,c_6365,c_4335,c_3115,c_2281,c_2192,
% 3.06/0.99                 c_1995,c_1968,c_1429,c_1263,c_1206,c_1041,c_873,c_553,
% 3.06/0.99                 c_498,c_529,c_527,c_9,c_11]) ).
% 3.06/0.99  
% 3.06/0.99  
% 3.06/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.06/0.99  
% 3.06/0.99  ------                               Statistics
% 3.06/0.99  
% 3.06/0.99  ------ General
% 3.06/0.99  
% 3.06/0.99  abstr_ref_over_cycles:                  0
% 3.06/0.99  abstr_ref_under_cycles:                 0
% 3.06/0.99  gc_basic_clause_elim:                   0
% 3.06/0.99  forced_gc_time:                         0
% 3.06/0.99  parsing_time:                           0.008
% 3.06/0.99  unif_index_cands_time:                  0.
% 3.06/0.99  unif_index_add_time:                    0.
% 3.06/0.99  orderings_time:                         0.
% 3.06/0.99  out_proof_time:                         0.01
% 3.06/0.99  total_time:                             0.381
% 3.06/0.99  num_of_symbols:                         50
% 3.06/0.99  num_of_terms:                           8124
% 3.06/0.99  
% 3.06/0.99  ------ Preprocessing
% 3.06/0.99  
% 3.06/0.99  num_of_splits:                          0
% 3.06/0.99  num_of_split_atoms:                     0
% 3.06/0.99  num_of_reused_defs:                     0
% 3.06/0.99  num_eq_ax_congr_red:                    19
% 3.06/0.99  num_of_sem_filtered_clauses:            1
% 3.06/0.99  num_of_subtypes:                        4
% 3.06/0.99  monotx_restored_types:                  0
% 3.06/0.99  sat_num_of_epr_types:                   0
% 3.06/0.99  sat_num_of_non_cyclic_types:            0
% 3.06/0.99  sat_guarded_non_collapsed_types:        0
% 3.06/0.99  num_pure_diseq_elim:                    0
% 3.06/0.99  simp_replaced_by:                       0
% 3.06/0.99  res_preprocessed:                       71
% 3.06/0.99  prep_upred:                             0
% 3.06/0.99  prep_unflattend:                        36
% 3.06/0.99  smt_new_axioms:                         0
% 3.06/0.99  pred_elim_cands:                        2
% 3.06/0.99  pred_elim:                              2
% 3.06/0.99  pred_elim_cl:                           2
% 3.06/0.99  pred_elim_cycles:                       4
% 3.06/0.99  merged_defs:                            8
% 3.06/0.99  merged_defs_ncl:                        0
% 3.06/0.99  bin_hyper_res:                          10
% 3.06/0.99  prep_cycles:                            4
% 3.06/0.99  pred_elim_time:                         0.006
% 3.06/0.99  splitting_time:                         0.
% 3.06/0.99  sem_filter_time:                        0.
% 3.06/0.99  monotx_time:                            0.
% 3.06/0.99  subtype_inf_time:                       0.
% 3.06/0.99  
% 3.06/0.99  ------ Problem properties
% 3.06/0.99  
% 3.06/0.99  clauses:                                11
% 3.06/0.99  conjectures:                            2
% 3.06/0.99  epr:                                    0
% 3.06/0.99  horn:                                   11
% 3.06/0.99  ground:                                 3
% 3.06/0.99  unary:                                  5
% 3.06/0.99  binary:                                 6
% 3.06/0.99  lits:                                   17
% 3.06/0.99  lits_eq:                                4
% 3.06/0.99  fd_pure:                                0
% 3.06/0.99  fd_pseudo:                              0
% 3.06/0.99  fd_cond:                                0
% 3.06/0.99  fd_pseudo_cond:                         0
% 3.06/0.99  ac_symbols:                             0
% 3.06/0.99  
% 3.06/0.99  ------ Propositional Solver
% 3.06/0.99  
% 3.06/0.99  prop_solver_calls:                      33
% 3.06/0.99  prop_fast_solver_calls:                 522
% 3.06/0.99  smt_solver_calls:                       0
% 3.06/0.99  smt_fast_solver_calls:                  0
% 3.06/0.99  prop_num_of_clauses:                    3240
% 3.06/0.99  prop_preprocess_simplified:             7662
% 3.06/0.99  prop_fo_subsumed:                       2
% 3.06/0.99  prop_solver_time:                       0.
% 3.06/0.99  smt_solver_time:                        0.
% 3.06/0.99  smt_fast_solver_time:                   0.
% 3.06/0.99  prop_fast_solver_time:                  0.
% 3.06/0.99  prop_unsat_core_time:                   0.
% 3.06/0.99  
% 3.06/0.99  ------ QBF
% 3.06/0.99  
% 3.06/0.99  qbf_q_res:                              0
% 3.06/0.99  qbf_num_tautologies:                    0
% 3.06/0.99  qbf_prep_cycles:                        0
% 3.06/0.99  
% 3.06/0.99  ------ BMC1
% 3.06/0.99  
% 3.06/0.99  bmc1_current_bound:                     -1
% 3.06/0.99  bmc1_last_solved_bound:                 -1
% 3.06/0.99  bmc1_unsat_core_size:                   -1
% 3.06/0.99  bmc1_unsat_core_parents_size:           -1
% 3.06/0.99  bmc1_merge_next_fun:                    0
% 3.06/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.06/0.99  
% 3.06/0.99  ------ Instantiation
% 3.06/0.99  
% 3.06/0.99  inst_num_of_clauses:                    1049
% 3.06/0.99  inst_num_in_passive:                    300
% 3.06/0.99  inst_num_in_active:                     599
% 3.06/0.99  inst_num_in_unprocessed:                149
% 3.06/0.99  inst_num_of_loops:                      654
% 3.06/0.99  inst_num_of_learning_restarts:          0
% 3.06/0.99  inst_num_moves_active_passive:          47
% 3.06/0.99  inst_lit_activity:                      0
% 3.06/0.99  inst_lit_activity_moves:                0
% 3.06/0.99  inst_num_tautologies:                   0
% 3.06/0.99  inst_num_prop_implied:                  0
% 3.06/0.99  inst_num_existing_simplified:           0
% 3.06/0.99  inst_num_eq_res_simplified:             0
% 3.06/0.99  inst_num_child_elim:                    0
% 3.06/0.99  inst_num_of_dismatching_blockings:      778
% 3.06/0.99  inst_num_of_non_proper_insts:           1624
% 3.06/0.99  inst_num_of_duplicates:                 0
% 3.06/0.99  inst_inst_num_from_inst_to_res:         0
% 3.06/0.99  inst_dismatching_checking_time:         0.
% 3.06/0.99  
% 3.06/0.99  ------ Resolution
% 3.06/0.99  
% 3.06/0.99  res_num_of_clauses:                     0
% 3.06/0.99  res_num_in_passive:                     0
% 3.06/0.99  res_num_in_active:                      0
% 3.06/0.99  res_num_of_loops:                       75
% 3.06/0.99  res_forward_subset_subsumed:            32
% 3.06/0.99  res_backward_subset_subsumed:           4
% 3.06/0.99  res_forward_subsumed:                   0
% 3.06/0.99  res_backward_subsumed:                  0
% 3.06/0.99  res_forward_subsumption_resolution:     0
% 3.06/0.99  res_backward_subsumption_resolution:    0
% 3.06/0.99  res_clause_to_clause_subsumption:       3804
% 3.06/0.99  res_orphan_elimination:                 0
% 3.06/0.99  res_tautology_del:                      244
% 3.06/0.99  res_num_eq_res_simplified:              0
% 3.06/0.99  res_num_sel_changes:                    0
% 3.06/0.99  res_moves_from_active_to_pass:          0
% 3.06/0.99  
% 3.06/0.99  ------ Superposition
% 3.06/0.99  
% 3.06/0.99  sup_time_total:                         0.
% 3.06/0.99  sup_time_generating:                    0.
% 3.06/0.99  sup_time_sim_full:                      0.
% 3.06/0.99  sup_time_sim_immed:                     0.
% 3.06/0.99  
% 3.06/0.99  sup_num_of_clauses:                     197
% 3.06/0.99  sup_num_in_active:                      125
% 3.06/0.99  sup_num_in_passive:                     72
% 3.06/0.99  sup_num_of_loops:                       130
% 3.06/0.99  sup_fw_superposition:                   285
% 3.06/0.99  sup_bw_superposition:                   6
% 3.06/0.99  sup_immediate_simplified:               74
% 3.06/0.99  sup_given_eliminated:                   0
% 3.06/0.99  comparisons_done:                       0
% 3.06/0.99  comparisons_avoided:                    0
% 3.06/0.99  
% 3.06/0.99  ------ Simplifications
% 3.06/0.99  
% 3.06/0.99  
% 3.06/0.99  sim_fw_subset_subsumed:                 2
% 3.06/0.99  sim_bw_subset_subsumed:                 0
% 3.06/0.99  sim_fw_subsumed:                        0
% 3.06/0.99  sim_bw_subsumed:                        0
% 3.06/0.99  sim_fw_subsumption_res:                 0
% 3.06/0.99  sim_bw_subsumption_res:                 0
% 3.06/0.99  sim_tautology_del:                      1
% 3.06/0.99  sim_eq_tautology_del:                   71
% 3.06/0.99  sim_eq_res_simp:                        0
% 3.06/0.99  sim_fw_demodulated:                     2
% 3.06/0.99  sim_bw_demodulated:                     5
% 3.06/0.99  sim_light_normalised:                   72
% 3.06/0.99  sim_joinable_taut:                      0
% 3.06/0.99  sim_joinable_simp:                      0
% 3.06/0.99  sim_ac_normalised:                      0
% 3.06/0.99  sim_smt_subsumption:                    0
% 3.06/0.99  
%------------------------------------------------------------------------------
