%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:47 EST 2020

% Result     : Theorem 19.57s
% Output     : CNFRefutation 19.57s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 250 expanded)
%              Number of clauses        :   86 ( 114 expanded)
%              Number of leaves         :   17 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  352 ( 789 expanded)
%              Number of equality atoms :  102 ( 140 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f24,f23,f22])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f29])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f29])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f31,f29])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_234,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | r1_tarski(X2_40,X3_40)
    | X2_40 != X0_40
    | X3_40 != X1_40 ),
    theory(equality)).

cnf(c_7157,plain,
    ( r1_tarski(X0_40,X1_40)
    | ~ r1_tarski(k1_tops_1(sK0,X2_40),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X3_40,X4_40)))
    | X0_40 != k1_tops_1(sK0,X2_40)
    | X1_40 != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X3_40,X4_40)) ),
    inference(instantiation,[status(thm)],[c_234])).

cnf(c_20223,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1_40,X2_40)))
    | r1_tarski(k1_tops_1(sK0,sK1),X3_40)
    | X3_40 != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1_40,X2_40))
    | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,X0_40) ),
    inference(instantiation,[status(thm)],[c_7157])).

cnf(c_62888,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))))
    | k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,X0_40) ),
    inference(instantiation,[status(thm)],[c_20223])).

cnf(c_62890,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))))
    | k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_62888])).

cnf(c_2,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_225,plain,
    ( k2_tarski(X0_40,X1_40) = k2_tarski(X1_40,X0_40) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_56550,plain,
    ( k2_tarski(sK1,sK2) = k2_tarski(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_225])).

cnf(c_233,plain,
    ( X0_44 != X1_44
    | k3_tarski(X0_44) = k3_tarski(X1_44) ),
    theory(equality)).

cnf(c_731,plain,
    ( X0_44 != k2_tarski(X0_40,X1_40)
    | k3_tarski(X0_44) = k3_tarski(k2_tarski(X0_40,X1_40)) ),
    inference(instantiation,[status(thm)],[c_233])).

cnf(c_1489,plain,
    ( k2_tarski(X0_40,X1_40) != k2_tarski(X1_40,X0_40)
    | k3_tarski(k2_tarski(X0_40,X1_40)) = k3_tarski(k2_tarski(X1_40,X0_40)) ),
    inference(instantiation,[status(thm)],[c_731])).

cnf(c_36917,plain,
    ( k2_tarski(sK1,sK2) != k2_tarski(sK2,sK1)
    | k3_tarski(k2_tarski(sK1,sK2)) = k3_tarski(k2_tarski(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_1489])).

cnf(c_528,plain,
    ( r1_tarski(X0_40,X1_40)
    | ~ r1_tarski(X2_40,k3_tarski(k2_tarski(X2_40,X3_40)))
    | X0_40 != X2_40
    | X1_40 != k3_tarski(k2_tarski(X2_40,X3_40)) ),
    inference(instantiation,[status(thm)],[c_234])).

cnf(c_602,plain,
    ( r1_tarski(X0_40,k3_tarski(X0_44))
    | ~ r1_tarski(X1_40,k3_tarski(k2_tarski(X1_40,X2_40)))
    | X0_40 != X1_40
    | k3_tarski(X0_44) != k3_tarski(k2_tarski(X1_40,X2_40)) ),
    inference(instantiation,[status(thm)],[c_528])).

cnf(c_4886,plain,
    ( r1_tarski(X0_40,k3_tarski(k2_tarski(X1_40,X2_40)))
    | ~ r1_tarski(X3_40,k3_tarski(k2_tarski(X3_40,sK1)))
    | X0_40 != X3_40
    | k3_tarski(k2_tarski(X1_40,X2_40)) != k3_tarski(k2_tarski(X3_40,sK1)) ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(c_15601,plain,
    ( ~ r1_tarski(X0_40,k3_tarski(k2_tarski(X0_40,sK1)))
    | r1_tarski(sK2,k3_tarski(k2_tarski(X1_40,sK2)))
    | k3_tarski(k2_tarski(X1_40,sK2)) != k3_tarski(k2_tarski(X0_40,sK1))
    | sK2 != X0_40 ),
    inference(instantiation,[status(thm)],[c_4886])).

cnf(c_27396,plain,
    ( r1_tarski(sK2,k3_tarski(k2_tarski(X0_40,sK2)))
    | ~ r1_tarski(sK2,k3_tarski(k2_tarski(sK2,sK1)))
    | k3_tarski(k2_tarski(X0_40,sK2)) != k3_tarski(k2_tarski(sK2,sK1))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_15601])).

cnf(c_27398,plain,
    ( ~ r1_tarski(sK2,k3_tarski(k2_tarski(sK2,sK1)))
    | r1_tarski(sK2,k3_tarski(k2_tarski(sK1,sK2)))
    | k3_tarski(k2_tarski(sK1,sK2)) != k3_tarski(k2_tarski(sK2,sK1))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_27396])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_10,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_115,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_10])).

cnf(c_116,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_115])).

cnf(c_219,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1_40,X0_40)
    | r1_tarski(k1_tops_1(sK0,X1_40),k1_tops_1(sK0,X0_40)) ),
    inference(subtyping,[status(esa)],[c_116])).

cnf(c_805,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_tarski(k2_tarski(X1_40,X2_40)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_40,k3_tarski(k2_tarski(X1_40,X2_40)))
    | r1_tarski(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,k3_tarski(k2_tarski(X1_40,X2_40)))) ),
    inference(instantiation,[status(thm)],[c_219])).

cnf(c_14118,plain,
    ( ~ m1_subset_1(k3_tarski(k2_tarski(X0_40,X1_40)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k3_tarski(k2_tarski(X0_40,X1_40))))
    | ~ r1_tarski(sK2,k3_tarski(k2_tarski(X0_40,X1_40))) ),
    inference(instantiation,[status(thm)],[c_805])).

cnf(c_19501,plain,
    ( ~ m1_subset_1(k3_tarski(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))))
    | ~ r1_tarski(sK2,k3_tarski(k2_tarski(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_14118])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k2_tarski(X2,X0)),X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_226,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | ~ r1_tarski(X2_40,X1_40)
    | r1_tarski(k3_tarski(k2_tarski(X2_40,X0_40)),X1_40) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2030,plain,
    ( ~ r1_tarski(X0_40,k1_tops_1(sK0,k3_tarski(k2_tarski(X1_40,X2_40))))
    | ~ r1_tarski(k1_tops_1(sK0,X3_40),k1_tops_1(sK0,k3_tarski(k2_tarski(X1_40,X2_40))))
    | r1_tarski(k3_tarski(k2_tarski(X0_40,k1_tops_1(sK0,X3_40))),k1_tops_1(sK0,k3_tarski(k2_tarski(X1_40,X2_40)))) ),
    inference(instantiation,[status(thm)],[c_226])).

cnf(c_5350,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,k3_tarski(k2_tarski(X0_40,X1_40))))
    | ~ r1_tarski(k1_tops_1(sK0,X2_40),k1_tops_1(sK0,k3_tarski(k2_tarski(X0_40,X1_40))))
    | r1_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,X2_40))),k1_tops_1(sK0,k3_tarski(k2_tarski(X0_40,X1_40)))) ),
    inference(instantiation,[status(thm)],[c_2030])).

cnf(c_10423,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))))
    | r1_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_5350])).

cnf(c_0,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_227,plain,
    ( r1_tarski(X0_40,k3_tarski(k2_tarski(X0_40,X1_40))) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_7934,plain,
    ( r1_tarski(sK2,k3_tarski(k2_tarski(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_227])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_224,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X0_42))
    | ~ m1_subset_1(X1_40,k1_zfmisc_1(X0_42))
    | m1_subset_1(k4_subset_1(X0_42,X1_40,X0_40),k1_zfmisc_1(X0_42)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1581,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k4_subset_1(u1_struct_0(sK0),X1_40,X0_40),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_224])).

cnf(c_3660,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k4_subset_1(u1_struct_0(sK0),X0_40,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1581])).

cnf(c_3662,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_3660])).

cnf(c_1823,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),X1_40,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_40,k4_subset_1(u1_struct_0(sK0),X1_40,sK2))
    | r1_tarski(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1_40,sK2))) ),
    inference(instantiation,[status(thm)],[c_219])).

cnf(c_1825,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1823])).

cnf(c_229,plain,
    ( X0_40 = X0_40 ),
    theory(equality)).

cnf(c_1518,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_229])).

cnf(c_1212,plain,
    ( r1_tarski(sK1,k3_tarski(k2_tarski(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_227])).

cnf(c_1153,plain,
    ( k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))) = k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_229])).

cnf(c_231,plain,
    ( X0_40 != X1_40
    | X2_40 != X1_40
    | X2_40 = X0_40 ),
    theory(equality)).

cnf(c_653,plain,
    ( X0_40 != X1_40
    | X0_40 = k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1_40 ),
    inference(instantiation,[status(thm)],[c_231])).

cnf(c_799,plain,
    ( X0_40 = k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | X0_40 != k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_653])).

cnf(c_917,plain,
    ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))
    | k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))) = k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))) != k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_799])).

cnf(c_430,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0_40
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1_40 ),
    inference(instantiation,[status(thm)],[c_234])).

cnf(c_447,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k3_tarski(k2_tarski(X0_40,X1_40)),X2_40)
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k3_tarski(k2_tarski(X0_40,X1_40))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X2_40 ),
    inference(instantiation,[status(thm)],[c_430])).

cnf(c_477,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k3_tarski(k2_tarski(X0_40,X1_40)),k1_tops_1(sK0,X2_40))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k3_tarski(k2_tarski(X0_40,X1_40))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,X2_40) ),
    inference(instantiation,[status(thm)],[c_447])).

cnf(c_743,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k3_tarski(k2_tarski(X0_40,X1_40)),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k3_tarski(k2_tarski(X0_40,X1_40))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_477])).

cnf(c_895,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_220,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_413,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_220])).

cnf(c_8,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_221,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_412,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_221])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_223,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X0_42))
    | ~ m1_subset_1(X1_40,k1_zfmisc_1(X0_42))
    | k4_subset_1(X0_42,X1_40,X0_40) = k3_tarski(k2_tarski(X1_40,X0_40)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_410,plain,
    ( k4_subset_1(X0_42,X0_40,X1_40) = k3_tarski(k2_tarski(X0_40,X1_40))
    | m1_subset_1(X0_40,k1_zfmisc_1(X0_42)) != iProver_top
    | m1_subset_1(X1_40,k1_zfmisc_1(X0_42)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_223])).

cnf(c_756,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0_40,sK2) = k3_tarski(k2_tarski(X0_40,sK2))
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_412,c_410])).

cnf(c_774,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_tarski(k2_tarski(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_413,c_756])).

cnf(c_409,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(X0_42)) != iProver_top
    | m1_subset_1(X1_40,k1_zfmisc_1(X0_42)) != iProver_top
    | m1_subset_1(k4_subset_1(X0_42,X0_40,X1_40),k1_zfmisc_1(X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_224])).

cnf(c_874,plain,
    ( m1_subset_1(k3_tarski(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_774,c_409])).

cnf(c_875,plain,
    ( m1_subset_1(k3_tarski(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_874])).

cnf(c_592,plain,
    ( r1_tarski(X0_40,k4_subset_1(X0_42,X1_40,X2_40))
    | ~ r1_tarski(X1_40,k3_tarski(k2_tarski(X1_40,X2_40)))
    | X0_40 != X1_40
    | k4_subset_1(X0_42,X1_40,X2_40) != k3_tarski(k2_tarski(X1_40,X2_40)) ),
    inference(instantiation,[status(thm)],[c_528])).

cnf(c_858,plain,
    ( r1_tarski(X0_40,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r1_tarski(sK1,k3_tarski(k2_tarski(sK1,sK2)))
    | X0_40 != sK1
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k3_tarski(k2_tarski(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_592])).

cnf(c_860,plain,
    ( r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r1_tarski(sK1,k3_tarski(k2_tarski(sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k3_tarski(k2_tarski(sK1,sK2))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_858])).

cnf(c_632,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_tarski(k2_tarski(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_223])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_133,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_10])).

cnf(c_134,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_133])).

cnf(c_218,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0_40),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_134])).

cnf(c_612,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_218])).

cnf(c_237,plain,
    ( X0_40 != X1_40
    | k1_tops_1(X0_43,X0_40) = k1_tops_1(X0_43,X1_40) ),
    theory(equality)).

cnf(c_506,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0_40
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,X0_40) ),
    inference(instantiation,[status(thm)],[c_237])).

cnf(c_543,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k3_tarski(k2_tarski(sK1,sK2))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_506])).

cnf(c_535,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_223])).

cnf(c_266,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_218])).

cnf(c_244,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_229])).

cnf(c_242,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_237])).

cnf(c_7,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f37])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_62890,c_56550,c_36917,c_27398,c_19501,c_10423,c_7934,c_3662,c_1825,c_1518,c_1212,c_1153,c_917,c_895,c_875,c_860,c_632,c_612,c_543,c_535,c_266,c_244,c_242,c_7,c_8,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:47:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 19.57/3.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.57/3.02  
% 19.57/3.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.57/3.02  
% 19.57/3.02  ------  iProver source info
% 19.57/3.02  
% 19.57/3.02  git: date: 2020-06-30 10:37:57 +0100
% 19.57/3.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.57/3.02  git: non_committed_changes: false
% 19.57/3.02  git: last_make_outside_of_git: false
% 19.57/3.02  
% 19.57/3.02  ------ 
% 19.57/3.02  
% 19.57/3.02  ------ Input Options
% 19.57/3.02  
% 19.57/3.02  --out_options                           all
% 19.57/3.02  --tptp_safe_out                         true
% 19.57/3.02  --problem_path                          ""
% 19.57/3.02  --include_path                          ""
% 19.57/3.02  --clausifier                            res/vclausify_rel
% 19.57/3.02  --clausifier_options                    ""
% 19.57/3.02  --stdin                                 false
% 19.57/3.02  --stats_out                             all
% 19.57/3.02  
% 19.57/3.02  ------ General Options
% 19.57/3.02  
% 19.57/3.02  --fof                                   false
% 19.57/3.02  --time_out_real                         305.
% 19.57/3.02  --time_out_virtual                      -1.
% 19.57/3.02  --symbol_type_check                     false
% 19.57/3.02  --clausify_out                          false
% 19.57/3.02  --sig_cnt_out                           false
% 19.57/3.02  --trig_cnt_out                          false
% 19.57/3.02  --trig_cnt_out_tolerance                1.
% 19.57/3.02  --trig_cnt_out_sk_spl                   false
% 19.57/3.02  --abstr_cl_out                          false
% 19.57/3.02  
% 19.57/3.02  ------ Global Options
% 19.57/3.02  
% 19.57/3.02  --schedule                              default
% 19.57/3.02  --add_important_lit                     false
% 19.57/3.02  --prop_solver_per_cl                    1000
% 19.57/3.02  --min_unsat_core                        false
% 19.57/3.02  --soft_assumptions                      false
% 19.57/3.02  --soft_lemma_size                       3
% 19.57/3.02  --prop_impl_unit_size                   0
% 19.57/3.02  --prop_impl_unit                        []
% 19.57/3.02  --share_sel_clauses                     true
% 19.57/3.02  --reset_solvers                         false
% 19.57/3.02  --bc_imp_inh                            [conj_cone]
% 19.57/3.02  --conj_cone_tolerance                   3.
% 19.57/3.02  --extra_neg_conj                        none
% 19.57/3.02  --large_theory_mode                     true
% 19.57/3.02  --prolific_symb_bound                   200
% 19.57/3.02  --lt_threshold                          2000
% 19.57/3.02  --clause_weak_htbl                      true
% 19.57/3.02  --gc_record_bc_elim                     false
% 19.57/3.02  
% 19.57/3.02  ------ Preprocessing Options
% 19.57/3.02  
% 19.57/3.02  --preprocessing_flag                    true
% 19.57/3.02  --time_out_prep_mult                    0.1
% 19.57/3.02  --splitting_mode                        input
% 19.57/3.02  --splitting_grd                         true
% 19.57/3.02  --splitting_cvd                         false
% 19.57/3.02  --splitting_cvd_svl                     false
% 19.57/3.02  --splitting_nvd                         32
% 19.57/3.02  --sub_typing                            true
% 19.57/3.02  --prep_gs_sim                           true
% 19.57/3.02  --prep_unflatten                        true
% 19.57/3.02  --prep_res_sim                          true
% 19.57/3.02  --prep_upred                            true
% 19.57/3.02  --prep_sem_filter                       exhaustive
% 19.57/3.02  --prep_sem_filter_out                   false
% 19.57/3.02  --pred_elim                             true
% 19.57/3.02  --res_sim_input                         true
% 19.57/3.02  --eq_ax_congr_red                       true
% 19.57/3.02  --pure_diseq_elim                       true
% 19.57/3.02  --brand_transform                       false
% 19.57/3.02  --non_eq_to_eq                          false
% 19.57/3.02  --prep_def_merge                        true
% 19.57/3.02  --prep_def_merge_prop_impl              false
% 19.57/3.02  --prep_def_merge_mbd                    true
% 19.57/3.02  --prep_def_merge_tr_red                 false
% 19.57/3.02  --prep_def_merge_tr_cl                  false
% 19.57/3.02  --smt_preprocessing                     true
% 19.57/3.02  --smt_ac_axioms                         fast
% 19.57/3.02  --preprocessed_out                      false
% 19.57/3.02  --preprocessed_stats                    false
% 19.57/3.02  
% 19.57/3.02  ------ Abstraction refinement Options
% 19.57/3.02  
% 19.57/3.02  --abstr_ref                             []
% 19.57/3.02  --abstr_ref_prep                        false
% 19.57/3.02  --abstr_ref_until_sat                   false
% 19.57/3.02  --abstr_ref_sig_restrict                funpre
% 19.57/3.02  --abstr_ref_af_restrict_to_split_sk     false
% 19.57/3.02  --abstr_ref_under                       []
% 19.57/3.02  
% 19.57/3.02  ------ SAT Options
% 19.57/3.02  
% 19.57/3.02  --sat_mode                              false
% 19.57/3.02  --sat_fm_restart_options                ""
% 19.57/3.02  --sat_gr_def                            false
% 19.57/3.02  --sat_epr_types                         true
% 19.57/3.02  --sat_non_cyclic_types                  false
% 19.57/3.02  --sat_finite_models                     false
% 19.57/3.02  --sat_fm_lemmas                         false
% 19.57/3.02  --sat_fm_prep                           false
% 19.57/3.02  --sat_fm_uc_incr                        true
% 19.57/3.02  --sat_out_model                         small
% 19.57/3.02  --sat_out_clauses                       false
% 19.57/3.02  
% 19.57/3.02  ------ QBF Options
% 19.57/3.02  
% 19.57/3.02  --qbf_mode                              false
% 19.57/3.02  --qbf_elim_univ                         false
% 19.57/3.02  --qbf_dom_inst                          none
% 19.57/3.02  --qbf_dom_pre_inst                      false
% 19.57/3.02  --qbf_sk_in                             false
% 19.57/3.02  --qbf_pred_elim                         true
% 19.57/3.02  --qbf_split                             512
% 19.57/3.02  
% 19.57/3.02  ------ BMC1 Options
% 19.57/3.02  
% 19.57/3.02  --bmc1_incremental                      false
% 19.57/3.02  --bmc1_axioms                           reachable_all
% 19.57/3.02  --bmc1_min_bound                        0
% 19.57/3.02  --bmc1_max_bound                        -1
% 19.57/3.02  --bmc1_max_bound_default                -1
% 19.57/3.02  --bmc1_symbol_reachability              true
% 19.57/3.02  --bmc1_property_lemmas                  false
% 19.57/3.02  --bmc1_k_induction                      false
% 19.57/3.02  --bmc1_non_equiv_states                 false
% 19.57/3.02  --bmc1_deadlock                         false
% 19.57/3.02  --bmc1_ucm                              false
% 19.57/3.02  --bmc1_add_unsat_core                   none
% 19.57/3.02  --bmc1_unsat_core_children              false
% 19.57/3.02  --bmc1_unsat_core_extrapolate_axioms    false
% 19.57/3.02  --bmc1_out_stat                         full
% 19.57/3.02  --bmc1_ground_init                      false
% 19.57/3.02  --bmc1_pre_inst_next_state              false
% 19.57/3.02  --bmc1_pre_inst_state                   false
% 19.57/3.02  --bmc1_pre_inst_reach_state             false
% 19.57/3.02  --bmc1_out_unsat_core                   false
% 19.57/3.02  --bmc1_aig_witness_out                  false
% 19.57/3.02  --bmc1_verbose                          false
% 19.57/3.02  --bmc1_dump_clauses_tptp                false
% 19.57/3.02  --bmc1_dump_unsat_core_tptp             false
% 19.57/3.02  --bmc1_dump_file                        -
% 19.57/3.02  --bmc1_ucm_expand_uc_limit              128
% 19.57/3.02  --bmc1_ucm_n_expand_iterations          6
% 19.57/3.02  --bmc1_ucm_extend_mode                  1
% 19.57/3.02  --bmc1_ucm_init_mode                    2
% 19.57/3.02  --bmc1_ucm_cone_mode                    none
% 19.57/3.02  --bmc1_ucm_reduced_relation_type        0
% 19.57/3.02  --bmc1_ucm_relax_model                  4
% 19.57/3.02  --bmc1_ucm_full_tr_after_sat            true
% 19.57/3.02  --bmc1_ucm_expand_neg_assumptions       false
% 19.57/3.02  --bmc1_ucm_layered_model                none
% 19.57/3.02  --bmc1_ucm_max_lemma_size               10
% 19.57/3.02  
% 19.57/3.02  ------ AIG Options
% 19.57/3.02  
% 19.57/3.02  --aig_mode                              false
% 19.57/3.02  
% 19.57/3.02  ------ Instantiation Options
% 19.57/3.02  
% 19.57/3.02  --instantiation_flag                    true
% 19.57/3.02  --inst_sos_flag                         true
% 19.57/3.02  --inst_sos_phase                        true
% 19.57/3.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.57/3.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.57/3.02  --inst_lit_sel_side                     num_symb
% 19.57/3.02  --inst_solver_per_active                1400
% 19.57/3.02  --inst_solver_calls_frac                1.
% 19.57/3.02  --inst_passive_queue_type               priority_queues
% 19.57/3.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.57/3.02  --inst_passive_queues_freq              [25;2]
% 19.57/3.02  --inst_dismatching                      true
% 19.57/3.02  --inst_eager_unprocessed_to_passive     true
% 19.57/3.02  --inst_prop_sim_given                   true
% 19.57/3.02  --inst_prop_sim_new                     false
% 19.57/3.02  --inst_subs_new                         false
% 19.57/3.02  --inst_eq_res_simp                      false
% 19.57/3.02  --inst_subs_given                       false
% 19.57/3.02  --inst_orphan_elimination               true
% 19.57/3.02  --inst_learning_loop_flag               true
% 19.57/3.02  --inst_learning_start                   3000
% 19.57/3.02  --inst_learning_factor                  2
% 19.57/3.02  --inst_start_prop_sim_after_learn       3
% 19.57/3.02  --inst_sel_renew                        solver
% 19.57/3.02  --inst_lit_activity_flag                true
% 19.57/3.02  --inst_restr_to_given                   false
% 19.57/3.02  --inst_activity_threshold               500
% 19.57/3.02  --inst_out_proof                        true
% 19.57/3.02  
% 19.57/3.02  ------ Resolution Options
% 19.57/3.02  
% 19.57/3.02  --resolution_flag                       true
% 19.57/3.02  --res_lit_sel                           adaptive
% 19.57/3.02  --res_lit_sel_side                      none
% 19.57/3.02  --res_ordering                          kbo
% 19.57/3.02  --res_to_prop_solver                    active
% 19.57/3.02  --res_prop_simpl_new                    false
% 19.57/3.02  --res_prop_simpl_given                  true
% 19.57/3.02  --res_passive_queue_type                priority_queues
% 19.57/3.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.57/3.02  --res_passive_queues_freq               [15;5]
% 19.57/3.02  --res_forward_subs                      full
% 19.57/3.02  --res_backward_subs                     full
% 19.57/3.02  --res_forward_subs_resolution           true
% 19.57/3.02  --res_backward_subs_resolution          true
% 19.57/3.02  --res_orphan_elimination                true
% 19.57/3.02  --res_time_limit                        2.
% 19.57/3.02  --res_out_proof                         true
% 19.57/3.02  
% 19.57/3.02  ------ Superposition Options
% 19.57/3.02  
% 19.57/3.02  --superposition_flag                    true
% 19.57/3.02  --sup_passive_queue_type                priority_queues
% 19.57/3.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.57/3.02  --sup_passive_queues_freq               [8;1;4]
% 19.57/3.02  --demod_completeness_check              fast
% 19.57/3.02  --demod_use_ground                      true
% 19.57/3.02  --sup_to_prop_solver                    passive
% 19.57/3.02  --sup_prop_simpl_new                    true
% 19.57/3.02  --sup_prop_simpl_given                  true
% 19.57/3.02  --sup_fun_splitting                     true
% 19.57/3.02  --sup_smt_interval                      50000
% 19.57/3.02  
% 19.57/3.02  ------ Superposition Simplification Setup
% 19.57/3.02  
% 19.57/3.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.57/3.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.57/3.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.57/3.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.57/3.02  --sup_full_triv                         [TrivRules;PropSubs]
% 19.57/3.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.57/3.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.57/3.02  --sup_immed_triv                        [TrivRules]
% 19.57/3.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.57/3.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.57/3.02  --sup_immed_bw_main                     []
% 19.57/3.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.57/3.02  --sup_input_triv                        [Unflattening;TrivRules]
% 19.57/3.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.57/3.02  --sup_input_bw                          []
% 19.57/3.02  
% 19.57/3.02  ------ Combination Options
% 19.57/3.02  
% 19.57/3.02  --comb_res_mult                         3
% 19.57/3.02  --comb_sup_mult                         2
% 19.57/3.02  --comb_inst_mult                        10
% 19.57/3.02  
% 19.57/3.02  ------ Debug Options
% 19.57/3.02  
% 19.57/3.02  --dbg_backtrace                         false
% 19.57/3.02  --dbg_dump_prop_clauses                 false
% 19.57/3.02  --dbg_dump_prop_clauses_file            -
% 19.57/3.02  --dbg_out_stat                          false
% 19.57/3.02  ------ Parsing...
% 19.57/3.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.57/3.02  
% 19.57/3.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.57/3.02  
% 19.57/3.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.57/3.02  
% 19.57/3.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.57/3.02  ------ Proving...
% 19.57/3.02  ------ Problem Properties 
% 19.57/3.02  
% 19.57/3.02  
% 19.57/3.02  clauses                                 10
% 19.57/3.02  conjectures                             3
% 19.57/3.02  EPR                                     0
% 19.57/3.02  Horn                                    10
% 19.57/3.02  unary                                   5
% 19.57/3.02  binary                                  1
% 19.57/3.02  lits                                    20
% 19.57/3.02  lits eq                                 2
% 19.57/3.02  fd_pure                                 0
% 19.57/3.02  fd_pseudo                               0
% 19.57/3.02  fd_cond                                 0
% 19.57/3.02  fd_pseudo_cond                          0
% 19.57/3.02  AC symbols                              0
% 19.57/3.02  
% 19.57/3.02  ------ Schedule dynamic 5 is on 
% 19.57/3.02  
% 19.57/3.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.57/3.02  
% 19.57/3.02  
% 19.57/3.02  ------ 
% 19.57/3.02  Current options:
% 19.57/3.02  ------ 
% 19.57/3.02  
% 19.57/3.02  ------ Input Options
% 19.57/3.02  
% 19.57/3.02  --out_options                           all
% 19.57/3.02  --tptp_safe_out                         true
% 19.57/3.02  --problem_path                          ""
% 19.57/3.02  --include_path                          ""
% 19.57/3.02  --clausifier                            res/vclausify_rel
% 19.57/3.02  --clausifier_options                    ""
% 19.57/3.02  --stdin                                 false
% 19.57/3.02  --stats_out                             all
% 19.57/3.02  
% 19.57/3.02  ------ General Options
% 19.57/3.02  
% 19.57/3.02  --fof                                   false
% 19.57/3.02  --time_out_real                         305.
% 19.57/3.02  --time_out_virtual                      -1.
% 19.57/3.02  --symbol_type_check                     false
% 19.57/3.02  --clausify_out                          false
% 19.57/3.02  --sig_cnt_out                           false
% 19.57/3.02  --trig_cnt_out                          false
% 19.57/3.02  --trig_cnt_out_tolerance                1.
% 19.57/3.02  --trig_cnt_out_sk_spl                   false
% 19.57/3.02  --abstr_cl_out                          false
% 19.57/3.02  
% 19.57/3.02  ------ Global Options
% 19.57/3.02  
% 19.57/3.02  --schedule                              default
% 19.57/3.02  --add_important_lit                     false
% 19.57/3.02  --prop_solver_per_cl                    1000
% 19.57/3.02  --min_unsat_core                        false
% 19.57/3.02  --soft_assumptions                      false
% 19.57/3.02  --soft_lemma_size                       3
% 19.57/3.02  --prop_impl_unit_size                   0
% 19.57/3.02  --prop_impl_unit                        []
% 19.57/3.02  --share_sel_clauses                     true
% 19.57/3.02  --reset_solvers                         false
% 19.57/3.02  --bc_imp_inh                            [conj_cone]
% 19.57/3.02  --conj_cone_tolerance                   3.
% 19.57/3.02  --extra_neg_conj                        none
% 19.57/3.02  --large_theory_mode                     true
% 19.57/3.02  --prolific_symb_bound                   200
% 19.57/3.02  --lt_threshold                          2000
% 19.57/3.02  --clause_weak_htbl                      true
% 19.57/3.02  --gc_record_bc_elim                     false
% 19.57/3.02  
% 19.57/3.02  ------ Preprocessing Options
% 19.57/3.02  
% 19.57/3.02  --preprocessing_flag                    true
% 19.57/3.02  --time_out_prep_mult                    0.1
% 19.57/3.02  --splitting_mode                        input
% 19.57/3.02  --splitting_grd                         true
% 19.57/3.02  --splitting_cvd                         false
% 19.57/3.02  --splitting_cvd_svl                     false
% 19.57/3.02  --splitting_nvd                         32
% 19.57/3.02  --sub_typing                            true
% 19.57/3.02  --prep_gs_sim                           true
% 19.57/3.02  --prep_unflatten                        true
% 19.57/3.02  --prep_res_sim                          true
% 19.57/3.02  --prep_upred                            true
% 19.57/3.02  --prep_sem_filter                       exhaustive
% 19.57/3.02  --prep_sem_filter_out                   false
% 19.57/3.02  --pred_elim                             true
% 19.57/3.02  --res_sim_input                         true
% 19.57/3.02  --eq_ax_congr_red                       true
% 19.57/3.02  --pure_diseq_elim                       true
% 19.57/3.02  --brand_transform                       false
% 19.57/3.02  --non_eq_to_eq                          false
% 19.57/3.02  --prep_def_merge                        true
% 19.57/3.02  --prep_def_merge_prop_impl              false
% 19.57/3.02  --prep_def_merge_mbd                    true
% 19.57/3.02  --prep_def_merge_tr_red                 false
% 19.57/3.02  --prep_def_merge_tr_cl                  false
% 19.57/3.02  --smt_preprocessing                     true
% 19.57/3.02  --smt_ac_axioms                         fast
% 19.57/3.02  --preprocessed_out                      false
% 19.57/3.02  --preprocessed_stats                    false
% 19.57/3.02  
% 19.57/3.02  ------ Abstraction refinement Options
% 19.57/3.02  
% 19.57/3.02  --abstr_ref                             []
% 19.57/3.02  --abstr_ref_prep                        false
% 19.57/3.02  --abstr_ref_until_sat                   false
% 19.57/3.02  --abstr_ref_sig_restrict                funpre
% 19.57/3.02  --abstr_ref_af_restrict_to_split_sk     false
% 19.57/3.02  --abstr_ref_under                       []
% 19.57/3.02  
% 19.57/3.02  ------ SAT Options
% 19.57/3.02  
% 19.57/3.02  --sat_mode                              false
% 19.57/3.02  --sat_fm_restart_options                ""
% 19.57/3.02  --sat_gr_def                            false
% 19.57/3.02  --sat_epr_types                         true
% 19.57/3.02  --sat_non_cyclic_types                  false
% 19.57/3.02  --sat_finite_models                     false
% 19.57/3.02  --sat_fm_lemmas                         false
% 19.57/3.02  --sat_fm_prep                           false
% 19.57/3.02  --sat_fm_uc_incr                        true
% 19.57/3.02  --sat_out_model                         small
% 19.57/3.02  --sat_out_clauses                       false
% 19.57/3.02  
% 19.57/3.02  ------ QBF Options
% 19.57/3.02  
% 19.57/3.02  --qbf_mode                              false
% 19.57/3.02  --qbf_elim_univ                         false
% 19.57/3.02  --qbf_dom_inst                          none
% 19.57/3.02  --qbf_dom_pre_inst                      false
% 19.57/3.02  --qbf_sk_in                             false
% 19.57/3.02  --qbf_pred_elim                         true
% 19.57/3.02  --qbf_split                             512
% 19.57/3.02  
% 19.57/3.02  ------ BMC1 Options
% 19.57/3.02  
% 19.57/3.02  --bmc1_incremental                      false
% 19.57/3.02  --bmc1_axioms                           reachable_all
% 19.57/3.02  --bmc1_min_bound                        0
% 19.57/3.02  --bmc1_max_bound                        -1
% 19.57/3.02  --bmc1_max_bound_default                -1
% 19.57/3.02  --bmc1_symbol_reachability              true
% 19.57/3.02  --bmc1_property_lemmas                  false
% 19.57/3.02  --bmc1_k_induction                      false
% 19.57/3.02  --bmc1_non_equiv_states                 false
% 19.57/3.02  --bmc1_deadlock                         false
% 19.57/3.02  --bmc1_ucm                              false
% 19.57/3.02  --bmc1_add_unsat_core                   none
% 19.57/3.02  --bmc1_unsat_core_children              false
% 19.57/3.02  --bmc1_unsat_core_extrapolate_axioms    false
% 19.57/3.02  --bmc1_out_stat                         full
% 19.57/3.02  --bmc1_ground_init                      false
% 19.57/3.02  --bmc1_pre_inst_next_state              false
% 19.57/3.02  --bmc1_pre_inst_state                   false
% 19.57/3.02  --bmc1_pre_inst_reach_state             false
% 19.57/3.02  --bmc1_out_unsat_core                   false
% 19.57/3.02  --bmc1_aig_witness_out                  false
% 19.57/3.02  --bmc1_verbose                          false
% 19.57/3.02  --bmc1_dump_clauses_tptp                false
% 19.57/3.02  --bmc1_dump_unsat_core_tptp             false
% 19.57/3.02  --bmc1_dump_file                        -
% 19.57/3.02  --bmc1_ucm_expand_uc_limit              128
% 19.57/3.02  --bmc1_ucm_n_expand_iterations          6
% 19.57/3.02  --bmc1_ucm_extend_mode                  1
% 19.57/3.02  --bmc1_ucm_init_mode                    2
% 19.57/3.02  --bmc1_ucm_cone_mode                    none
% 19.57/3.02  --bmc1_ucm_reduced_relation_type        0
% 19.57/3.02  --bmc1_ucm_relax_model                  4
% 19.57/3.02  --bmc1_ucm_full_tr_after_sat            true
% 19.57/3.02  --bmc1_ucm_expand_neg_assumptions       false
% 19.57/3.02  --bmc1_ucm_layered_model                none
% 19.57/3.02  --bmc1_ucm_max_lemma_size               10
% 19.57/3.02  
% 19.57/3.02  ------ AIG Options
% 19.57/3.02  
% 19.57/3.02  --aig_mode                              false
% 19.57/3.02  
% 19.57/3.02  ------ Instantiation Options
% 19.57/3.02  
% 19.57/3.02  --instantiation_flag                    true
% 19.57/3.02  --inst_sos_flag                         true
% 19.57/3.02  --inst_sos_phase                        true
% 19.57/3.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.57/3.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.57/3.02  --inst_lit_sel_side                     none
% 19.57/3.02  --inst_solver_per_active                1400
% 19.57/3.02  --inst_solver_calls_frac                1.
% 19.57/3.02  --inst_passive_queue_type               priority_queues
% 19.57/3.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.57/3.02  --inst_passive_queues_freq              [25;2]
% 19.57/3.02  --inst_dismatching                      true
% 19.57/3.02  --inst_eager_unprocessed_to_passive     true
% 19.57/3.02  --inst_prop_sim_given                   true
% 19.57/3.02  --inst_prop_sim_new                     false
% 19.57/3.02  --inst_subs_new                         false
% 19.57/3.02  --inst_eq_res_simp                      false
% 19.57/3.02  --inst_subs_given                       false
% 19.57/3.02  --inst_orphan_elimination               true
% 19.57/3.02  --inst_learning_loop_flag               true
% 19.57/3.02  --inst_learning_start                   3000
% 19.57/3.02  --inst_learning_factor                  2
% 19.57/3.02  --inst_start_prop_sim_after_learn       3
% 19.57/3.02  --inst_sel_renew                        solver
% 19.57/3.02  --inst_lit_activity_flag                true
% 19.57/3.02  --inst_restr_to_given                   false
% 19.57/3.02  --inst_activity_threshold               500
% 19.57/3.02  --inst_out_proof                        true
% 19.57/3.02  
% 19.57/3.02  ------ Resolution Options
% 19.57/3.02  
% 19.57/3.02  --resolution_flag                       false
% 19.57/3.02  --res_lit_sel                           adaptive
% 19.57/3.02  --res_lit_sel_side                      none
% 19.57/3.02  --res_ordering                          kbo
% 19.57/3.02  --res_to_prop_solver                    active
% 19.57/3.02  --res_prop_simpl_new                    false
% 19.57/3.02  --res_prop_simpl_given                  true
% 19.57/3.02  --res_passive_queue_type                priority_queues
% 19.57/3.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.57/3.02  --res_passive_queues_freq               [15;5]
% 19.57/3.02  --res_forward_subs                      full
% 19.57/3.02  --res_backward_subs                     full
% 19.57/3.02  --res_forward_subs_resolution           true
% 19.57/3.02  --res_backward_subs_resolution          true
% 19.57/3.02  --res_orphan_elimination                true
% 19.57/3.02  --res_time_limit                        2.
% 19.57/3.02  --res_out_proof                         true
% 19.57/3.02  
% 19.57/3.02  ------ Superposition Options
% 19.57/3.02  
% 19.57/3.02  --superposition_flag                    true
% 19.57/3.02  --sup_passive_queue_type                priority_queues
% 19.57/3.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.57/3.02  --sup_passive_queues_freq               [8;1;4]
% 19.57/3.02  --demod_completeness_check              fast
% 19.57/3.02  --demod_use_ground                      true
% 19.57/3.02  --sup_to_prop_solver                    passive
% 19.57/3.02  --sup_prop_simpl_new                    true
% 19.57/3.02  --sup_prop_simpl_given                  true
% 19.57/3.02  --sup_fun_splitting                     true
% 19.57/3.02  --sup_smt_interval                      50000
% 19.57/3.02  
% 19.57/3.02  ------ Superposition Simplification Setup
% 19.57/3.02  
% 19.57/3.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.57/3.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.57/3.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.57/3.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.57/3.02  --sup_full_triv                         [TrivRules;PropSubs]
% 19.57/3.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.57/3.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.57/3.02  --sup_immed_triv                        [TrivRules]
% 19.57/3.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.57/3.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.57/3.02  --sup_immed_bw_main                     []
% 19.57/3.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.57/3.02  --sup_input_triv                        [Unflattening;TrivRules]
% 19.57/3.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.57/3.02  --sup_input_bw                          []
% 19.57/3.02  
% 19.57/3.02  ------ Combination Options
% 19.57/3.02  
% 19.57/3.02  --comb_res_mult                         3
% 19.57/3.02  --comb_sup_mult                         2
% 19.57/3.02  --comb_inst_mult                        10
% 19.57/3.02  
% 19.57/3.02  ------ Debug Options
% 19.57/3.02  
% 19.57/3.02  --dbg_backtrace                         false
% 19.57/3.02  --dbg_dump_prop_clauses                 false
% 19.57/3.02  --dbg_dump_prop_clauses_file            -
% 19.57/3.02  --dbg_out_stat                          false
% 19.57/3.02  
% 19.57/3.02  
% 19.57/3.02  
% 19.57/3.02  
% 19.57/3.02  ------ Proving...
% 19.57/3.02  
% 19.57/3.02  
% 19.57/3.02  % SZS status Theorem for theBenchmark.p
% 19.57/3.02  
% 19.57/3.02  % SZS output start CNFRefutation for theBenchmark.p
% 19.57/3.02  
% 19.57/3.02  fof(f3,axiom,(
% 19.57/3.02    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 19.57/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.57/3.02  
% 19.57/3.02  fof(f28,plain,(
% 19.57/3.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 19.57/3.02    inference(cnf_transformation,[],[f3])).
% 19.57/3.02  
% 19.57/3.02  fof(f8,axiom,(
% 19.57/3.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 19.57/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.57/3.02  
% 19.57/3.02  fof(f19,plain,(
% 19.57/3.02    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.57/3.02    inference(ennf_transformation,[],[f8])).
% 19.57/3.02  
% 19.57/3.02  fof(f20,plain,(
% 19.57/3.02    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.57/3.02    inference(flattening,[],[f19])).
% 19.57/3.02  
% 19.57/3.02  fof(f33,plain,(
% 19.57/3.02    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.57/3.02    inference(cnf_transformation,[],[f20])).
% 19.57/3.02  
% 19.57/3.02  fof(f9,conjecture,(
% 19.57/3.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 19.57/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.57/3.02  
% 19.57/3.02  fof(f10,negated_conjecture,(
% 19.57/3.02    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 19.57/3.02    inference(negated_conjecture,[],[f9])).
% 19.57/3.02  
% 19.57/3.02  fof(f21,plain,(
% 19.57/3.02    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 19.57/3.02    inference(ennf_transformation,[],[f10])).
% 19.57/3.02  
% 19.57/3.02  fof(f24,plain,(
% 19.57/3.02    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 19.57/3.02    introduced(choice_axiom,[])).
% 19.57/3.02  
% 19.57/3.02  fof(f23,plain,(
% 19.57/3.02    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 19.57/3.02    introduced(choice_axiom,[])).
% 19.57/3.02  
% 19.57/3.02  fof(f22,plain,(
% 19.57/3.02    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 19.57/3.02    introduced(choice_axiom,[])).
% 19.57/3.02  
% 19.57/3.02  fof(f25,plain,(
% 19.57/3.02    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 19.57/3.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f24,f23,f22])).
% 19.57/3.02  
% 19.57/3.02  fof(f34,plain,(
% 19.57/3.02    l1_pre_topc(sK0)),
% 19.57/3.02    inference(cnf_transformation,[],[f25])).
% 19.57/3.02  
% 19.57/3.02  fof(f2,axiom,(
% 19.57/3.02    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 19.57/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.57/3.02  
% 19.57/3.02  fof(f11,plain,(
% 19.57/3.02    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 19.57/3.02    inference(ennf_transformation,[],[f2])).
% 19.57/3.02  
% 19.57/3.02  fof(f12,plain,(
% 19.57/3.02    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 19.57/3.02    inference(flattening,[],[f11])).
% 19.57/3.02  
% 19.57/3.02  fof(f27,plain,(
% 19.57/3.02    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 19.57/3.02    inference(cnf_transformation,[],[f12])).
% 19.57/3.02  
% 19.57/3.02  fof(f4,axiom,(
% 19.57/3.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 19.57/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.57/3.02  
% 19.57/3.02  fof(f29,plain,(
% 19.57/3.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 19.57/3.02    inference(cnf_transformation,[],[f4])).
% 19.57/3.02  
% 19.57/3.02  fof(f39,plain,(
% 19.57/3.02    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 19.57/3.02    inference(definition_unfolding,[],[f27,f29])).
% 19.57/3.02  
% 19.57/3.02  fof(f1,axiom,(
% 19.57/3.02    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 19.57/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.57/3.02  
% 19.57/3.02  fof(f26,plain,(
% 19.57/3.02    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 19.57/3.02    inference(cnf_transformation,[],[f1])).
% 19.57/3.02  
% 19.57/3.02  fof(f38,plain,(
% 19.57/3.02    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 19.57/3.02    inference(definition_unfolding,[],[f26,f29])).
% 19.57/3.02  
% 19.57/3.02  fof(f5,axiom,(
% 19.57/3.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 19.57/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.57/3.02  
% 19.57/3.02  fof(f13,plain,(
% 19.57/3.02    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 19.57/3.02    inference(ennf_transformation,[],[f5])).
% 19.57/3.02  
% 19.57/3.02  fof(f14,plain,(
% 19.57/3.02    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.57/3.02    inference(flattening,[],[f13])).
% 19.57/3.02  
% 19.57/3.02  fof(f30,plain,(
% 19.57/3.02    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.57/3.02    inference(cnf_transformation,[],[f14])).
% 19.57/3.02  
% 19.57/3.02  fof(f35,plain,(
% 19.57/3.02    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 19.57/3.02    inference(cnf_transformation,[],[f25])).
% 19.57/3.02  
% 19.57/3.02  fof(f36,plain,(
% 19.57/3.02    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 19.57/3.02    inference(cnf_transformation,[],[f25])).
% 19.57/3.02  
% 19.57/3.02  fof(f6,axiom,(
% 19.57/3.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 19.57/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.57/3.02  
% 19.57/3.02  fof(f15,plain,(
% 19.57/3.02    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 19.57/3.02    inference(ennf_transformation,[],[f6])).
% 19.57/3.02  
% 19.57/3.02  fof(f16,plain,(
% 19.57/3.02    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.57/3.02    inference(flattening,[],[f15])).
% 19.57/3.02  
% 19.57/3.02  fof(f31,plain,(
% 19.57/3.02    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.57/3.02    inference(cnf_transformation,[],[f16])).
% 19.57/3.02  
% 19.57/3.02  fof(f40,plain,(
% 19.57/3.02    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.57/3.02    inference(definition_unfolding,[],[f31,f29])).
% 19.57/3.02  
% 19.57/3.02  fof(f7,axiom,(
% 19.57/3.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 19.57/3.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.57/3.02  
% 19.57/3.02  fof(f17,plain,(
% 19.57/3.02    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 19.57/3.02    inference(ennf_transformation,[],[f7])).
% 19.57/3.02  
% 19.57/3.02  fof(f18,plain,(
% 19.57/3.02    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 19.57/3.02    inference(flattening,[],[f17])).
% 19.57/3.02  
% 19.57/3.02  fof(f32,plain,(
% 19.57/3.02    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.57/3.02    inference(cnf_transformation,[],[f18])).
% 19.57/3.02  
% 19.57/3.02  fof(f37,plain,(
% 19.57/3.02    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 19.57/3.02    inference(cnf_transformation,[],[f25])).
% 19.57/3.02  
% 19.57/3.02  cnf(c_234,plain,
% 19.57/3.02      ( ~ r1_tarski(X0_40,X1_40)
% 19.57/3.02      | r1_tarski(X2_40,X3_40)
% 19.57/3.02      | X2_40 != X0_40
% 19.57/3.02      | X3_40 != X1_40 ),
% 19.57/3.02      theory(equality) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_7157,plain,
% 19.57/3.02      ( r1_tarski(X0_40,X1_40)
% 19.57/3.02      | ~ r1_tarski(k1_tops_1(sK0,X2_40),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X3_40,X4_40)))
% 19.57/3.02      | X0_40 != k1_tops_1(sK0,X2_40)
% 19.57/3.02      | X1_40 != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X3_40,X4_40)) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_234]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_20223,plain,
% 19.57/3.02      ( ~ r1_tarski(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1_40,X2_40)))
% 19.57/3.02      | r1_tarski(k1_tops_1(sK0,sK1),X3_40)
% 19.57/3.02      | X3_40 != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1_40,X2_40))
% 19.57/3.02      | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,X0_40) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_7157]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_62888,plain,
% 19.57/3.02      ( ~ r1_tarski(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 19.57/3.02      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))))
% 19.57/3.02      | k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 19.57/3.02      | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,X0_40) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_20223]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_62890,plain,
% 19.57/3.02      ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 19.57/3.02      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))))
% 19.57/3.02      | k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 19.57/3.02      | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_62888]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_2,plain,
% 19.57/3.02      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 19.57/3.02      inference(cnf_transformation,[],[f28]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_225,plain,
% 19.57/3.02      ( k2_tarski(X0_40,X1_40) = k2_tarski(X1_40,X0_40) ),
% 19.57/3.02      inference(subtyping,[status(esa)],[c_2]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_56550,plain,
% 19.57/3.02      ( k2_tarski(sK1,sK2) = k2_tarski(sK2,sK1) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_225]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_233,plain,
% 19.57/3.02      ( X0_44 != X1_44 | k3_tarski(X0_44) = k3_tarski(X1_44) ),
% 19.57/3.02      theory(equality) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_731,plain,
% 19.57/3.02      ( X0_44 != k2_tarski(X0_40,X1_40)
% 19.57/3.02      | k3_tarski(X0_44) = k3_tarski(k2_tarski(X0_40,X1_40)) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_233]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_1489,plain,
% 19.57/3.02      ( k2_tarski(X0_40,X1_40) != k2_tarski(X1_40,X0_40)
% 19.57/3.02      | k3_tarski(k2_tarski(X0_40,X1_40)) = k3_tarski(k2_tarski(X1_40,X0_40)) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_731]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_36917,plain,
% 19.57/3.02      ( k2_tarski(sK1,sK2) != k2_tarski(sK2,sK1)
% 19.57/3.02      | k3_tarski(k2_tarski(sK1,sK2)) = k3_tarski(k2_tarski(sK2,sK1)) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_1489]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_528,plain,
% 19.57/3.02      ( r1_tarski(X0_40,X1_40)
% 19.57/3.02      | ~ r1_tarski(X2_40,k3_tarski(k2_tarski(X2_40,X3_40)))
% 19.57/3.02      | X0_40 != X2_40
% 19.57/3.02      | X1_40 != k3_tarski(k2_tarski(X2_40,X3_40)) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_234]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_602,plain,
% 19.57/3.02      ( r1_tarski(X0_40,k3_tarski(X0_44))
% 19.57/3.02      | ~ r1_tarski(X1_40,k3_tarski(k2_tarski(X1_40,X2_40)))
% 19.57/3.02      | X0_40 != X1_40
% 19.57/3.02      | k3_tarski(X0_44) != k3_tarski(k2_tarski(X1_40,X2_40)) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_528]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_4886,plain,
% 19.57/3.02      ( r1_tarski(X0_40,k3_tarski(k2_tarski(X1_40,X2_40)))
% 19.57/3.02      | ~ r1_tarski(X3_40,k3_tarski(k2_tarski(X3_40,sK1)))
% 19.57/3.02      | X0_40 != X3_40
% 19.57/3.02      | k3_tarski(k2_tarski(X1_40,X2_40)) != k3_tarski(k2_tarski(X3_40,sK1)) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_602]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_15601,plain,
% 19.57/3.02      ( ~ r1_tarski(X0_40,k3_tarski(k2_tarski(X0_40,sK1)))
% 19.57/3.02      | r1_tarski(sK2,k3_tarski(k2_tarski(X1_40,sK2)))
% 19.57/3.02      | k3_tarski(k2_tarski(X1_40,sK2)) != k3_tarski(k2_tarski(X0_40,sK1))
% 19.57/3.02      | sK2 != X0_40 ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_4886]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_27396,plain,
% 19.57/3.02      ( r1_tarski(sK2,k3_tarski(k2_tarski(X0_40,sK2)))
% 19.57/3.02      | ~ r1_tarski(sK2,k3_tarski(k2_tarski(sK2,sK1)))
% 19.57/3.02      | k3_tarski(k2_tarski(X0_40,sK2)) != k3_tarski(k2_tarski(sK2,sK1))
% 19.57/3.02      | sK2 != sK2 ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_15601]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_27398,plain,
% 19.57/3.02      ( ~ r1_tarski(sK2,k3_tarski(k2_tarski(sK2,sK1)))
% 19.57/3.02      | r1_tarski(sK2,k3_tarski(k2_tarski(sK1,sK2)))
% 19.57/3.02      | k3_tarski(k2_tarski(sK1,sK2)) != k3_tarski(k2_tarski(sK2,sK1))
% 19.57/3.02      | sK2 != sK2 ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_27396]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_6,plain,
% 19.57/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.57/3.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.57/3.02      | ~ r1_tarski(X0,X2)
% 19.57/3.02      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 19.57/3.02      | ~ l1_pre_topc(X1) ),
% 19.57/3.02      inference(cnf_transformation,[],[f33]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_10,negated_conjecture,
% 19.57/3.02      ( l1_pre_topc(sK0) ),
% 19.57/3.02      inference(cnf_transformation,[],[f34]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_115,plain,
% 19.57/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.57/3.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.57/3.02      | ~ r1_tarski(X0,X2)
% 19.57/3.02      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 19.57/3.02      | sK0 != X1 ),
% 19.57/3.02      inference(resolution_lifted,[status(thm)],[c_6,c_10]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_116,plain,
% 19.57/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | ~ r1_tarski(X1,X0)
% 19.57/3.02      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
% 19.57/3.02      inference(unflattening,[status(thm)],[c_115]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_219,plain,
% 19.57/3.02      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | ~ m1_subset_1(X1_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | ~ r1_tarski(X1_40,X0_40)
% 19.57/3.02      | r1_tarski(k1_tops_1(sK0,X1_40),k1_tops_1(sK0,X0_40)) ),
% 19.57/3.02      inference(subtyping,[status(esa)],[c_116]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_805,plain,
% 19.57/3.02      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | ~ m1_subset_1(k3_tarski(k2_tarski(X1_40,X2_40)),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | ~ r1_tarski(X0_40,k3_tarski(k2_tarski(X1_40,X2_40)))
% 19.57/3.02      | r1_tarski(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,k3_tarski(k2_tarski(X1_40,X2_40)))) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_219]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_14118,plain,
% 19.57/3.02      ( ~ m1_subset_1(k3_tarski(k2_tarski(X0_40,X1_40)),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k3_tarski(k2_tarski(X0_40,X1_40))))
% 19.57/3.02      | ~ r1_tarski(sK2,k3_tarski(k2_tarski(X0_40,X1_40))) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_805]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_19501,plain,
% 19.57/3.02      ( ~ m1_subset_1(k3_tarski(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))))
% 19.57/3.02      | ~ r1_tarski(sK2,k3_tarski(k2_tarski(sK1,sK2))) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_14118]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_1,plain,
% 19.57/3.02      ( ~ r1_tarski(X0,X1)
% 19.57/3.02      | ~ r1_tarski(X2,X1)
% 19.57/3.02      | r1_tarski(k3_tarski(k2_tarski(X2,X0)),X1) ),
% 19.57/3.02      inference(cnf_transformation,[],[f39]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_226,plain,
% 19.57/3.02      ( ~ r1_tarski(X0_40,X1_40)
% 19.57/3.02      | ~ r1_tarski(X2_40,X1_40)
% 19.57/3.02      | r1_tarski(k3_tarski(k2_tarski(X2_40,X0_40)),X1_40) ),
% 19.57/3.02      inference(subtyping,[status(esa)],[c_1]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_2030,plain,
% 19.57/3.02      ( ~ r1_tarski(X0_40,k1_tops_1(sK0,k3_tarski(k2_tarski(X1_40,X2_40))))
% 19.57/3.02      | ~ r1_tarski(k1_tops_1(sK0,X3_40),k1_tops_1(sK0,k3_tarski(k2_tarski(X1_40,X2_40))))
% 19.57/3.02      | r1_tarski(k3_tarski(k2_tarski(X0_40,k1_tops_1(sK0,X3_40))),k1_tops_1(sK0,k3_tarski(k2_tarski(X1_40,X2_40)))) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_226]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_5350,plain,
% 19.57/3.02      ( ~ r1_tarski(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,k3_tarski(k2_tarski(X0_40,X1_40))))
% 19.57/3.02      | ~ r1_tarski(k1_tops_1(sK0,X2_40),k1_tops_1(sK0,k3_tarski(k2_tarski(X0_40,X1_40))))
% 19.57/3.02      | r1_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,X2_40))),k1_tops_1(sK0,k3_tarski(k2_tarski(X0_40,X1_40)))) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_2030]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_10423,plain,
% 19.57/3.02      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))))
% 19.57/3.02      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))))
% 19.57/3.02      | r1_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_5350]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_0,plain,
% 19.57/3.02      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
% 19.57/3.02      inference(cnf_transformation,[],[f38]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_227,plain,
% 19.57/3.02      ( r1_tarski(X0_40,k3_tarski(k2_tarski(X0_40,X1_40))) ),
% 19.57/3.02      inference(subtyping,[status(esa)],[c_0]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_7934,plain,
% 19.57/3.02      ( r1_tarski(sK2,k3_tarski(k2_tarski(sK2,sK1))) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_227]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_3,plain,
% 19.57/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.57/3.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 19.57/3.02      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 19.57/3.02      inference(cnf_transformation,[],[f30]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_224,plain,
% 19.57/3.02      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X0_42))
% 19.57/3.02      | ~ m1_subset_1(X1_40,k1_zfmisc_1(X0_42))
% 19.57/3.02      | m1_subset_1(k4_subset_1(X0_42,X1_40,X0_40),k1_zfmisc_1(X0_42)) ),
% 19.57/3.02      inference(subtyping,[status(esa)],[c_3]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_1581,plain,
% 19.57/3.02      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | ~ m1_subset_1(X1_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | m1_subset_1(k4_subset_1(u1_struct_0(sK0),X1_40,X0_40),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_224]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_3660,plain,
% 19.57/3.02      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | m1_subset_1(k4_subset_1(u1_struct_0(sK0),X0_40,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_1581]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_3662,plain,
% 19.57/3.02      ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_3660]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_1823,plain,
% 19.57/3.02      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),X1_40,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | ~ r1_tarski(X0_40,k4_subset_1(u1_struct_0(sK0),X1_40,sK2))
% 19.57/3.02      | r1_tarski(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1_40,sK2))) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_219]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_1825,plain,
% 19.57/3.02      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 19.57/3.02      | ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_1823]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_229,plain,( X0_40 = X0_40 ),theory(equality) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_1518,plain,
% 19.57/3.02      ( sK2 = sK2 ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_229]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_1212,plain,
% 19.57/3.02      ( r1_tarski(sK1,k3_tarski(k2_tarski(sK1,sK2))) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_227]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_1153,plain,
% 19.57/3.02      ( k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))) = k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_229]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_231,plain,
% 19.57/3.02      ( X0_40 != X1_40 | X2_40 != X1_40 | X2_40 = X0_40 ),
% 19.57/3.02      theory(equality) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_653,plain,
% 19.57/3.02      ( X0_40 != X1_40
% 19.57/3.02      | X0_40 = k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 19.57/3.02      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1_40 ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_231]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_799,plain,
% 19.57/3.02      ( X0_40 = k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 19.57/3.02      | X0_40 != k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))
% 19.57/3.02      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_653]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_917,plain,
% 19.57/3.02      ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2)))
% 19.57/3.02      | k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))) = k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 19.57/3.02      | k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))) != k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_799]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_430,plain,
% 19.57/3.02      ( ~ r1_tarski(X0_40,X1_40)
% 19.57/3.02      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 19.57/3.02      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0_40
% 19.57/3.02      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1_40 ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_234]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_447,plain,
% 19.57/3.02      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 19.57/3.02      | ~ r1_tarski(k3_tarski(k2_tarski(X0_40,X1_40)),X2_40)
% 19.57/3.02      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k3_tarski(k2_tarski(X0_40,X1_40))
% 19.57/3.02      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X2_40 ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_430]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_477,plain,
% 19.57/3.02      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 19.57/3.02      | ~ r1_tarski(k3_tarski(k2_tarski(X0_40,X1_40)),k1_tops_1(sK0,X2_40))
% 19.57/3.02      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k3_tarski(k2_tarski(X0_40,X1_40))
% 19.57/3.02      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,X2_40) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_447]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_743,plain,
% 19.57/3.02      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 19.57/3.02      | ~ r1_tarski(k3_tarski(k2_tarski(X0_40,X1_40)),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))))
% 19.57/3.02      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k3_tarski(k2_tarski(X0_40,X1_40))
% 19.57/3.02      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_477]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_895,plain,
% 19.57/3.02      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 19.57/3.02      | ~ r1_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))),k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))))
% 19.57/3.02      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
% 19.57/3.02      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_743]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_9,negated_conjecture,
% 19.57/3.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.57/3.02      inference(cnf_transformation,[],[f35]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_220,negated_conjecture,
% 19.57/3.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.57/3.02      inference(subtyping,[status(esa)],[c_9]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_413,plain,
% 19.57/3.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.57/3.02      inference(predicate_to_equality,[status(thm)],[c_220]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_8,negated_conjecture,
% 19.57/3.02      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.57/3.02      inference(cnf_transformation,[],[f36]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_221,negated_conjecture,
% 19.57/3.02      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.57/3.02      inference(subtyping,[status(esa)],[c_8]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_412,plain,
% 19.57/3.02      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.57/3.02      inference(predicate_to_equality,[status(thm)],[c_221]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_4,plain,
% 19.57/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.57/3.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 19.57/3.02      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 19.57/3.02      inference(cnf_transformation,[],[f40]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_223,plain,
% 19.57/3.02      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X0_42))
% 19.57/3.02      | ~ m1_subset_1(X1_40,k1_zfmisc_1(X0_42))
% 19.57/3.02      | k4_subset_1(X0_42,X1_40,X0_40) = k3_tarski(k2_tarski(X1_40,X0_40)) ),
% 19.57/3.02      inference(subtyping,[status(esa)],[c_4]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_410,plain,
% 19.57/3.02      ( k4_subset_1(X0_42,X0_40,X1_40) = k3_tarski(k2_tarski(X0_40,X1_40))
% 19.57/3.02      | m1_subset_1(X0_40,k1_zfmisc_1(X0_42)) != iProver_top
% 19.57/3.02      | m1_subset_1(X1_40,k1_zfmisc_1(X0_42)) != iProver_top ),
% 19.57/3.02      inference(predicate_to_equality,[status(thm)],[c_223]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_756,plain,
% 19.57/3.02      ( k4_subset_1(u1_struct_0(sK0),X0_40,sK2) = k3_tarski(k2_tarski(X0_40,sK2))
% 19.57/3.02      | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.57/3.02      inference(superposition,[status(thm)],[c_412,c_410]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_774,plain,
% 19.57/3.02      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_tarski(k2_tarski(sK1,sK2)) ),
% 19.57/3.02      inference(superposition,[status(thm)],[c_413,c_756]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_409,plain,
% 19.57/3.02      ( m1_subset_1(X0_40,k1_zfmisc_1(X0_42)) != iProver_top
% 19.57/3.02      | m1_subset_1(X1_40,k1_zfmisc_1(X0_42)) != iProver_top
% 19.57/3.02      | m1_subset_1(k4_subset_1(X0_42,X0_40,X1_40),k1_zfmisc_1(X0_42)) = iProver_top ),
% 19.57/3.02      inference(predicate_to_equality,[status(thm)],[c_224]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_874,plain,
% 19.57/3.02      ( m1_subset_1(k3_tarski(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 19.57/3.02      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.57/3.02      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.57/3.02      inference(superposition,[status(thm)],[c_774,c_409]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_875,plain,
% 19.57/3.02      ( m1_subset_1(k3_tarski(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.57/3.02      inference(predicate_to_equality_rev,[status(thm)],[c_874]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_592,plain,
% 19.57/3.02      ( r1_tarski(X0_40,k4_subset_1(X0_42,X1_40,X2_40))
% 19.57/3.02      | ~ r1_tarski(X1_40,k3_tarski(k2_tarski(X1_40,X2_40)))
% 19.57/3.02      | X0_40 != X1_40
% 19.57/3.02      | k4_subset_1(X0_42,X1_40,X2_40) != k3_tarski(k2_tarski(X1_40,X2_40)) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_528]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_858,plain,
% 19.57/3.02      ( r1_tarski(X0_40,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 19.57/3.02      | ~ r1_tarski(sK1,k3_tarski(k2_tarski(sK1,sK2)))
% 19.57/3.02      | X0_40 != sK1
% 19.57/3.02      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k3_tarski(k2_tarski(sK1,sK2)) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_592]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_860,plain,
% 19.57/3.02      ( r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 19.57/3.02      | ~ r1_tarski(sK1,k3_tarski(k2_tarski(sK1,sK2)))
% 19.57/3.02      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k3_tarski(k2_tarski(sK1,sK2))
% 19.57/3.02      | sK1 != sK1 ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_858]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_632,plain,
% 19.57/3.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_tarski(k2_tarski(sK1,sK2)) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_223]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_5,plain,
% 19.57/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.57/3.02      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.57/3.02      | ~ l1_pre_topc(X1) ),
% 19.57/3.02      inference(cnf_transformation,[],[f32]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_133,plain,
% 19.57/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.57/3.02      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.57/3.02      | sK0 != X1 ),
% 19.57/3.02      inference(resolution_lifted,[status(thm)],[c_5,c_10]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_134,plain,
% 19.57/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.57/3.02      inference(unflattening,[status(thm)],[c_133]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_218,plain,
% 19.57/3.02      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | m1_subset_1(k1_tops_1(sK0,X0_40),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.57/3.02      inference(subtyping,[status(esa)],[c_134]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_612,plain,
% 19.57/3.02      ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_218]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_237,plain,
% 19.57/3.02      ( X0_40 != X1_40
% 19.57/3.02      | k1_tops_1(X0_43,X0_40) = k1_tops_1(X0_43,X1_40) ),
% 19.57/3.02      theory(equality) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_506,plain,
% 19.57/3.02      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0_40
% 19.57/3.02      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,X0_40) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_237]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_543,plain,
% 19.57/3.02      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k3_tarski(k2_tarski(sK1,sK2))
% 19.57/3.02      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k3_tarski(k2_tarski(sK1,sK2))) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_506]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_535,plain,
% 19.57/3.02      ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_223]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_266,plain,
% 19.57/3.02      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.57/3.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_218]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_244,plain,
% 19.57/3.02      ( sK1 = sK1 ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_229]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_242,plain,
% 19.57/3.02      ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1) | sK1 != sK1 ),
% 19.57/3.02      inference(instantiation,[status(thm)],[c_237]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(c_7,negated_conjecture,
% 19.57/3.02      ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 19.57/3.02      inference(cnf_transformation,[],[f37]) ).
% 19.57/3.02  
% 19.57/3.02  cnf(contradiction,plain,
% 19.57/3.02      ( $false ),
% 19.57/3.02      inference(minisat,
% 19.57/3.02                [status(thm)],
% 19.57/3.02                [c_62890,c_56550,c_36917,c_27398,c_19501,c_10423,c_7934,
% 19.57/3.02                 c_3662,c_1825,c_1518,c_1212,c_1153,c_917,c_895,c_875,
% 19.57/3.03                 c_860,c_632,c_612,c_543,c_535,c_266,c_244,c_242,c_7,c_8,
% 19.57/3.03                 c_9]) ).
% 19.57/3.03  
% 19.57/3.03  
% 19.57/3.03  % SZS output end CNFRefutation for theBenchmark.p
% 19.57/3.03  
% 19.57/3.03  ------                               Statistics
% 19.57/3.03  
% 19.57/3.03  ------ General
% 19.57/3.03  
% 19.57/3.03  abstr_ref_over_cycles:                  0
% 19.57/3.03  abstr_ref_under_cycles:                 0
% 19.57/3.03  gc_basic_clause_elim:                   0
% 19.57/3.03  forced_gc_time:                         0
% 19.57/3.03  parsing_time:                           0.008
% 19.57/3.03  unif_index_cands_time:                  0.
% 19.57/3.03  unif_index_add_time:                    0.
% 19.57/3.03  orderings_time:                         0.
% 19.57/3.03  out_proof_time:                         0.012
% 19.57/3.03  total_time:                             2.017
% 19.57/3.03  num_of_symbols:                         45
% 19.57/3.03  num_of_terms:                           59674
% 19.57/3.03  
% 19.57/3.03  ------ Preprocessing
% 19.57/3.03  
% 19.57/3.03  num_of_splits:                          0
% 19.57/3.03  num_of_split_atoms:                     0
% 19.57/3.03  num_of_reused_defs:                     0
% 19.57/3.03  num_eq_ax_congr_red:                    11
% 19.57/3.03  num_of_sem_filtered_clauses:            1
% 19.57/3.03  num_of_subtypes:                        5
% 19.57/3.03  monotx_restored_types:                  0
% 19.57/3.03  sat_num_of_epr_types:                   0
% 19.57/3.03  sat_num_of_non_cyclic_types:            0
% 19.57/3.03  sat_guarded_non_collapsed_types:        0
% 19.57/3.03  num_pure_diseq_elim:                    0
% 19.57/3.03  simp_replaced_by:                       0
% 19.57/3.03  res_preprocessed:                       60
% 19.57/3.03  prep_upred:                             0
% 19.57/3.03  prep_unflattend:                        2
% 19.57/3.03  smt_new_axioms:                         0
% 19.57/3.03  pred_elim_cands:                        2
% 19.57/3.03  pred_elim:                              1
% 19.57/3.03  pred_elim_cl:                           1
% 19.57/3.03  pred_elim_cycles:                       3
% 19.57/3.03  merged_defs:                            0
% 19.57/3.03  merged_defs_ncl:                        0
% 19.57/3.03  bin_hyper_res:                          0
% 19.57/3.03  prep_cycles:                            4
% 19.57/3.03  pred_elim_time:                         0.001
% 19.57/3.03  splitting_time:                         0.
% 19.57/3.03  sem_filter_time:                        0.
% 19.57/3.03  monotx_time:                            0.
% 19.57/3.03  subtype_inf_time:                       0.
% 19.57/3.03  
% 19.57/3.03  ------ Problem properties
% 19.57/3.03  
% 19.57/3.03  clauses:                                10
% 19.57/3.03  conjectures:                            3
% 19.57/3.03  epr:                                    0
% 19.57/3.03  horn:                                   10
% 19.57/3.03  ground:                                 3
% 19.57/3.03  unary:                                  5
% 19.57/3.03  binary:                                 1
% 19.57/3.03  lits:                                   20
% 19.57/3.03  lits_eq:                                2
% 19.57/3.03  fd_pure:                                0
% 19.57/3.03  fd_pseudo:                              0
% 19.57/3.03  fd_cond:                                0
% 19.57/3.03  fd_pseudo_cond:                         0
% 19.57/3.03  ac_symbols:                             0
% 19.57/3.03  
% 19.57/3.03  ------ Propositional Solver
% 19.57/3.03  
% 19.57/3.03  prop_solver_calls:                      36
% 19.57/3.03  prop_fast_solver_calls:                 890
% 19.57/3.03  smt_solver_calls:                       0
% 19.57/3.03  smt_fast_solver_calls:                  0
% 19.57/3.03  prop_num_of_clauses:                    18494
% 19.57/3.03  prop_preprocess_simplified:             39601
% 19.57/3.03  prop_fo_subsumed:                       31
% 19.57/3.03  prop_solver_time:                       0.
% 19.57/3.03  smt_solver_time:                        0.
% 19.57/3.03  smt_fast_solver_time:                   0.
% 19.57/3.03  prop_fast_solver_time:                  0.
% 19.57/3.03  prop_unsat_core_time:                   0.002
% 19.57/3.03  
% 19.57/3.03  ------ QBF
% 19.57/3.03  
% 19.57/3.03  qbf_q_res:                              0
% 19.57/3.03  qbf_num_tautologies:                    0
% 19.57/3.03  qbf_prep_cycles:                        0
% 19.57/3.03  
% 19.57/3.03  ------ BMC1
% 19.57/3.03  
% 19.57/3.03  bmc1_current_bound:                     -1
% 19.57/3.03  bmc1_last_solved_bound:                 -1
% 19.57/3.03  bmc1_unsat_core_size:                   -1
% 19.57/3.03  bmc1_unsat_core_parents_size:           -1
% 19.57/3.03  bmc1_merge_next_fun:                    0
% 19.57/3.03  bmc1_unsat_core_clauses_time:           0.
% 19.57/3.03  
% 19.57/3.03  ------ Instantiation
% 19.57/3.03  
% 19.57/3.03  inst_num_of_clauses:                    5567
% 19.57/3.03  inst_num_in_passive:                    2041
% 19.57/3.03  inst_num_in_active:                     2022
% 19.57/3.03  inst_num_in_unprocessed:                1510
% 19.57/3.03  inst_num_of_loops:                      2174
% 19.57/3.03  inst_num_of_learning_restarts:          0
% 19.57/3.03  inst_num_moves_active_passive:          146
% 19.57/3.03  inst_lit_activity:                      0
% 19.57/3.03  inst_lit_activity_moves:                0
% 19.57/3.03  inst_num_tautologies:                   0
% 19.57/3.03  inst_num_prop_implied:                  0
% 19.57/3.03  inst_num_existing_simplified:           0
% 19.57/3.03  inst_num_eq_res_simplified:             0
% 19.57/3.03  inst_num_child_elim:                    0
% 19.57/3.03  inst_num_of_dismatching_blockings:      15207
% 19.57/3.03  inst_num_of_non_proper_insts:           13684
% 19.57/3.03  inst_num_of_duplicates:                 0
% 19.57/3.03  inst_inst_num_from_inst_to_res:         0
% 19.57/3.03  inst_dismatching_checking_time:         0.
% 19.57/3.03  
% 19.57/3.03  ------ Resolution
% 19.57/3.03  
% 19.57/3.03  res_num_of_clauses:                     0
% 19.57/3.03  res_num_in_passive:                     0
% 19.57/3.03  res_num_in_active:                      0
% 19.57/3.03  res_num_of_loops:                       64
% 19.57/3.03  res_forward_subset_subsumed:            828
% 19.57/3.03  res_backward_subset_subsumed:           18
% 19.57/3.03  res_forward_subsumed:                   0
% 19.57/3.03  res_backward_subsumed:                  0
% 19.57/3.03  res_forward_subsumption_resolution:     0
% 19.57/3.03  res_backward_subsumption_resolution:    0
% 19.57/3.03  res_clause_to_clause_subsumption:       6079
% 19.57/3.03  res_orphan_elimination:                 0
% 19.57/3.03  res_tautology_del:                      1027
% 19.57/3.03  res_num_eq_res_simplified:              0
% 19.57/3.03  res_num_sel_changes:                    0
% 19.57/3.03  res_moves_from_active_to_pass:          0
% 19.57/3.03  
% 19.57/3.03  ------ Superposition
% 19.57/3.03  
% 19.57/3.03  sup_time_total:                         0.
% 19.57/3.03  sup_time_generating:                    0.
% 19.57/3.03  sup_time_sim_full:                      0.
% 19.57/3.03  sup_time_sim_immed:                     0.
% 19.57/3.03  
% 19.57/3.03  sup_num_of_clauses:                     2156
% 19.57/3.03  sup_num_in_active:                      344
% 19.57/3.03  sup_num_in_passive:                     1812
% 19.57/3.03  sup_num_of_loops:                       434
% 19.57/3.03  sup_fw_superposition:                   1420
% 19.57/3.03  sup_bw_superposition:                   1154
% 19.57/3.03  sup_immediate_simplified:               758
% 19.57/3.03  sup_given_eliminated:                   52
% 19.57/3.03  comparisons_done:                       0
% 19.57/3.03  comparisons_avoided:                    0
% 19.57/3.03  
% 19.57/3.03  ------ Simplifications
% 19.57/3.03  
% 19.57/3.03  
% 19.57/3.03  sim_fw_subset_subsumed:                 0
% 19.57/3.03  sim_bw_subset_subsumed:                 3
% 19.57/3.03  sim_fw_subsumed:                        111
% 19.57/3.03  sim_bw_subsumed:                        0
% 19.57/3.03  sim_fw_subsumption_res:                 0
% 19.57/3.03  sim_bw_subsumption_res:                 0
% 19.57/3.03  sim_tautology_del:                      0
% 19.57/3.03  sim_eq_tautology_del:                   77
% 19.57/3.03  sim_eq_res_simp:                        0
% 19.57/3.03  sim_fw_demodulated:                     131
% 19.57/3.03  sim_bw_demodulated:                     169
% 19.57/3.03  sim_light_normalised:                   673
% 19.57/3.03  sim_joinable_taut:                      0
% 19.57/3.03  sim_joinable_simp:                      0
% 19.57/3.03  sim_ac_normalised:                      0
% 19.57/3.03  sim_smt_subsumption:                    0
% 19.57/3.03  
%------------------------------------------------------------------------------
