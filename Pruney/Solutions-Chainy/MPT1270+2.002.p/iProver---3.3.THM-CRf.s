%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:14 EST 2020

% Result     : Theorem 51.25s
% Output     : CNFRefutation 51.25s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 636 expanded)
%              Number of clauses        :  104 ( 226 expanded)
%              Number of leaves         :   22 ( 156 expanded)
%              Depth                    :   22
%              Number of atoms          :  367 (1748 expanded)
%              Number of equality atoms :  157 ( 436 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> r1_tarski(X1,k2_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ r1_tarski(sK1,k2_tops_1(X0,sK1))
          | ~ v2_tops_1(sK1,X0) )
        & ( r1_tarski(sK1,k2_tops_1(X0,sK1))
          | v2_tops_1(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(sK0,X1))
            | ~ v2_tops_1(X1,sK0) )
          & ( r1_tarski(X1,k2_tops_1(sK0,X1))
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | ~ v2_tops_1(sK1,sK0) )
    & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).

fof(f71,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f77,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f51,f44])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f52,f44,f44])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f75,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f48,f44])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f58,f44])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f55,f44])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f50,f44])).

fof(f73,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_889,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_166582,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k2_tops_1(sK0,sK1))
    | X2 != X0
    | k2_tops_1(sK0,sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_889])).

cnf(c_176603,plain,
    ( ~ r1_tarski(X0,k2_tops_1(sK0,sK1))
    | r1_tarski(X1,k2_tops_1(sK0,sK1))
    | X1 != X0
    | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_166582])).

cnf(c_192942,plain,
    ( ~ r1_tarski(X0,k2_tops_1(sK0,sK1))
    | r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)),k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)) != X0 ),
    inference(instantiation,[status(thm)],[c_176603])).

cnf(c_219750,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,k1_xboole_0),k2_tops_1(sK0,sK1))
    | r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)),k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)) != k3_subset_1(sK1,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_192942])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_26,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_210,plain,
    ( v2_tops_1(sK1,sK0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(prop_impl,[status(thm)],[c_26])).

cnf(c_24,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_354,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_28])).

cnf(c_355,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_424,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,X0) = k1_xboole_0
    | sK0 != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_210,c_355])).

cnf(c_425,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_662,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_27,c_425])).

cnf(c_1399,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_662])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1417,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3108,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1399,c_1417])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1865,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1870,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1865,c_4])).

cnf(c_9107,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_3108,c_1870])).

cnf(c_1406,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_384,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_28])).

cnf(c_385,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_1401,plain,
    ( k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_385])).

cnf(c_1632,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1406,c_1401])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1411,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4274,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1406,c_1411])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_15,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_206,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_15])).

cnf(c_207,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_206])).

cnf(c_254,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_13,c_207])).

cnf(c_1402,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_254])).

cnf(c_123881,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_4274,c_1402])).

cnf(c_125984,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1632,c_123881])).

cnf(c_126050,plain,
    ( k1_tops_1(sK0,sK1) = k5_xboole_0(sK1,sK1)
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9107,c_125984])).

cnf(c_2006,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1870,c_7])).

cnf(c_126192,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_126050,c_2006])).

cnf(c_126220,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_126192,c_125984])).

cnf(c_3,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1416,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3106,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_1416,c_1417])).

cnf(c_4047,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_3106,c_1870])).

cnf(c_9,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_14,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1830,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_9,c_14])).

cnf(c_2508,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1830,c_14])).

cnf(c_12208,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4047,c_2508])).

cnf(c_2516,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2508,c_0])).

cnf(c_4429,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_2516,c_0])).

cnf(c_14691,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_12208,c_4429])).

cnf(c_24541,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_14691,c_1416])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_251,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_207])).

cnf(c_1405,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_251])).

cnf(c_26658,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_24541,c_1405])).

cnf(c_26727,plain,
    ( k3_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_26658,c_0])).

cnf(c_126241,plain,
    ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_126220,c_26727])).

cnf(c_2515,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_1416])).

cnf(c_127378,plain,
    ( r1_tarski(k3_subset_1(sK1,k1_xboole_0),k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_126241,c_2515])).

cnf(c_127869,plain,
    ( r1_tarski(k3_subset_1(sK1,k1_xboole_0),k2_tops_1(sK0,sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_127378])).

cnf(c_3033,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_889])).

cnf(c_15131,plain,
    ( ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)),X0)
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) != X0
    | sK1 != k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_3033])).

cnf(c_46408,plain,
    ( ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)),k2_tops_1(sK0,sK1))
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | sK1 != k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_15131])).

cnf(c_33552,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)) = k3_subset_1(sK1,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_251])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_11913,plain,
    ( ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_xboole_0)
    | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_11917,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_11913])).

cnf(c_885,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_9865,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_885])).

cnf(c_1696,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X3)),X4)
    | X1 != X4
    | X0 != k5_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(instantiation,[status(thm)],[c_889])).

cnf(c_3839,plain,
    ( r1_tarski(X0,sK1)
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)
    | X0 != k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | sK1 != X3 ),
    inference(instantiation,[status(thm)],[c_1696])).

cnf(c_8292,plain,
    ( r1_tarski(X0,sK1)
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),sK1)
    | X0 != k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3839])).

cnf(c_8294,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),sK1)
    | r1_tarski(k1_xboole_0,sK1)
    | sK1 != sK1
    | k1_xboole_0 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_8292])).

cnf(c_886,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2562,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_886])).

cnf(c_4773,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2562])).

cnf(c_7084,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)) != sK1
    | sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_4773])).

cnf(c_8,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_5014,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,sK1)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5016,plain,
    ( r1_tarski(k1_xboole_0,k2_xboole_0(k1_xboole_0,sK1)) ),
    inference(instantiation,[status(thm)],[c_5014])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2637,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,sK1))
    | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2639,plain,
    ( r1_tarski(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),sK1)
    | ~ r1_tarski(k1_xboole_0,k2_xboole_0(k1_xboole_0,sK1)) ),
    inference(instantiation,[status(thm)],[c_2637])).

cnf(c_1784,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_885])).

cnf(c_1752,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)) = sK1 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_25,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_208,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(prop_impl,[status(thm)],[c_25])).

cnf(c_23,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_369,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_28])).

cnf(c_370,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_438,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,X0) != k1_xboole_0
    | sK0 != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_208,c_370])).

cnf(c_439,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_441,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_439,c_27])).

cnf(c_76,plain,
    ( r1_tarski(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_72,plain,
    ( r1_tarski(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_219750,c_127869,c_126192,c_46408,c_33552,c_11917,c_9865,c_8294,c_7084,c_5016,c_2639,c_1784,c_1752,c_441,c_76,c_72])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:14:25 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 51.25/6.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 51.25/6.99  
% 51.25/6.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.25/6.99  
% 51.25/6.99  ------  iProver source info
% 51.25/6.99  
% 51.25/6.99  git: date: 2020-06-30 10:37:57 +0100
% 51.25/6.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.25/6.99  git: non_committed_changes: false
% 51.25/6.99  git: last_make_outside_of_git: false
% 51.25/6.99  
% 51.25/6.99  ------ 
% 51.25/6.99  
% 51.25/6.99  ------ Input Options
% 51.25/6.99  
% 51.25/6.99  --out_options                           all
% 51.25/6.99  --tptp_safe_out                         true
% 51.25/6.99  --problem_path                          ""
% 51.25/6.99  --include_path                          ""
% 51.25/6.99  --clausifier                            res/vclausify_rel
% 51.25/6.99  --clausifier_options                    --mode clausify
% 51.25/6.99  --stdin                                 false
% 51.25/6.99  --stats_out                             all
% 51.25/6.99  
% 51.25/6.99  ------ General Options
% 51.25/6.99  
% 51.25/6.99  --fof                                   false
% 51.25/6.99  --time_out_real                         305.
% 51.25/6.99  --time_out_virtual                      -1.
% 51.25/6.99  --symbol_type_check                     false
% 51.25/6.99  --clausify_out                          false
% 51.25/6.99  --sig_cnt_out                           false
% 51.25/6.99  --trig_cnt_out                          false
% 51.25/6.99  --trig_cnt_out_tolerance                1.
% 51.25/6.99  --trig_cnt_out_sk_spl                   false
% 51.25/6.99  --abstr_cl_out                          false
% 51.25/6.99  
% 51.25/6.99  ------ Global Options
% 51.25/6.99  
% 51.25/6.99  --schedule                              default
% 51.25/6.99  --add_important_lit                     false
% 51.25/6.99  --prop_solver_per_cl                    1000
% 51.25/6.99  --min_unsat_core                        false
% 51.25/6.99  --soft_assumptions                      false
% 51.25/6.99  --soft_lemma_size                       3
% 51.25/6.99  --prop_impl_unit_size                   0
% 51.25/6.99  --prop_impl_unit                        []
% 51.25/6.99  --share_sel_clauses                     true
% 51.25/6.99  --reset_solvers                         false
% 51.25/6.99  --bc_imp_inh                            [conj_cone]
% 51.25/6.99  --conj_cone_tolerance                   3.
% 51.25/6.99  --extra_neg_conj                        none
% 51.25/6.99  --large_theory_mode                     true
% 51.25/6.99  --prolific_symb_bound                   200
% 51.25/6.99  --lt_threshold                          2000
% 51.25/6.99  --clause_weak_htbl                      true
% 51.25/6.99  --gc_record_bc_elim                     false
% 51.25/6.99  
% 51.25/6.99  ------ Preprocessing Options
% 51.25/6.99  
% 51.25/6.99  --preprocessing_flag                    true
% 51.25/6.99  --time_out_prep_mult                    0.1
% 51.25/6.99  --splitting_mode                        input
% 51.25/6.99  --splitting_grd                         true
% 51.25/6.99  --splitting_cvd                         false
% 51.25/6.99  --splitting_cvd_svl                     false
% 51.25/6.99  --splitting_nvd                         32
% 51.25/6.99  --sub_typing                            true
% 51.25/6.99  --prep_gs_sim                           true
% 51.25/6.99  --prep_unflatten                        true
% 51.25/6.99  --prep_res_sim                          true
% 51.25/6.99  --prep_upred                            true
% 51.25/6.99  --prep_sem_filter                       exhaustive
% 51.25/6.99  --prep_sem_filter_out                   false
% 51.25/6.99  --pred_elim                             true
% 51.25/6.99  --res_sim_input                         true
% 51.25/6.99  --eq_ax_congr_red                       true
% 51.25/6.99  --pure_diseq_elim                       true
% 51.25/6.99  --brand_transform                       false
% 51.25/6.99  --non_eq_to_eq                          false
% 51.25/6.99  --prep_def_merge                        true
% 51.25/6.99  --prep_def_merge_prop_impl              false
% 51.25/6.99  --prep_def_merge_mbd                    true
% 51.25/6.99  --prep_def_merge_tr_red                 false
% 51.25/6.99  --prep_def_merge_tr_cl                  false
% 51.25/6.99  --smt_preprocessing                     true
% 51.25/6.99  --smt_ac_axioms                         fast
% 51.25/6.99  --preprocessed_out                      false
% 51.25/6.99  --preprocessed_stats                    false
% 51.25/6.99  
% 51.25/6.99  ------ Abstraction refinement Options
% 51.25/6.99  
% 51.25/6.99  --abstr_ref                             []
% 51.25/6.99  --abstr_ref_prep                        false
% 51.25/6.99  --abstr_ref_until_sat                   false
% 51.25/6.99  --abstr_ref_sig_restrict                funpre
% 51.25/6.99  --abstr_ref_af_restrict_to_split_sk     false
% 51.25/6.99  --abstr_ref_under                       []
% 51.25/6.99  
% 51.25/6.99  ------ SAT Options
% 51.25/6.99  
% 51.25/6.99  --sat_mode                              false
% 51.25/6.99  --sat_fm_restart_options                ""
% 51.25/6.99  --sat_gr_def                            false
% 51.25/6.99  --sat_epr_types                         true
% 51.25/6.99  --sat_non_cyclic_types                  false
% 51.25/6.99  --sat_finite_models                     false
% 51.25/6.99  --sat_fm_lemmas                         false
% 51.25/6.99  --sat_fm_prep                           false
% 51.25/6.99  --sat_fm_uc_incr                        true
% 51.25/6.99  --sat_out_model                         small
% 51.25/6.99  --sat_out_clauses                       false
% 51.25/6.99  
% 51.25/6.99  ------ QBF Options
% 51.25/6.99  
% 51.25/6.99  --qbf_mode                              false
% 51.25/6.99  --qbf_elim_univ                         false
% 51.25/6.99  --qbf_dom_inst                          none
% 51.25/6.99  --qbf_dom_pre_inst                      false
% 51.25/6.99  --qbf_sk_in                             false
% 51.25/6.99  --qbf_pred_elim                         true
% 51.25/6.99  --qbf_split                             512
% 51.25/6.99  
% 51.25/6.99  ------ BMC1 Options
% 51.25/6.99  
% 51.25/6.99  --bmc1_incremental                      false
% 51.25/6.99  --bmc1_axioms                           reachable_all
% 51.25/6.99  --bmc1_min_bound                        0
% 51.25/6.99  --bmc1_max_bound                        -1
% 51.25/6.99  --bmc1_max_bound_default                -1
% 51.25/6.99  --bmc1_symbol_reachability              true
% 51.25/6.99  --bmc1_property_lemmas                  false
% 51.25/6.99  --bmc1_k_induction                      false
% 51.25/6.99  --bmc1_non_equiv_states                 false
% 51.25/6.99  --bmc1_deadlock                         false
% 51.25/6.99  --bmc1_ucm                              false
% 51.25/6.99  --bmc1_add_unsat_core                   none
% 51.25/6.99  --bmc1_unsat_core_children              false
% 51.25/6.99  --bmc1_unsat_core_extrapolate_axioms    false
% 51.25/6.99  --bmc1_out_stat                         full
% 51.25/6.99  --bmc1_ground_init                      false
% 51.25/6.99  --bmc1_pre_inst_next_state              false
% 51.25/6.99  --bmc1_pre_inst_state                   false
% 51.25/6.99  --bmc1_pre_inst_reach_state             false
% 51.25/6.99  --bmc1_out_unsat_core                   false
% 51.25/6.99  --bmc1_aig_witness_out                  false
% 51.25/6.99  --bmc1_verbose                          false
% 51.25/6.99  --bmc1_dump_clauses_tptp                false
% 51.25/6.99  --bmc1_dump_unsat_core_tptp             false
% 51.25/6.99  --bmc1_dump_file                        -
% 51.25/6.99  --bmc1_ucm_expand_uc_limit              128
% 51.25/6.99  --bmc1_ucm_n_expand_iterations          6
% 51.25/6.99  --bmc1_ucm_extend_mode                  1
% 51.25/6.99  --bmc1_ucm_init_mode                    2
% 51.25/6.99  --bmc1_ucm_cone_mode                    none
% 51.25/6.99  --bmc1_ucm_reduced_relation_type        0
% 51.25/6.99  --bmc1_ucm_relax_model                  4
% 51.25/6.99  --bmc1_ucm_full_tr_after_sat            true
% 51.25/6.99  --bmc1_ucm_expand_neg_assumptions       false
% 51.25/6.99  --bmc1_ucm_layered_model                none
% 51.25/6.99  --bmc1_ucm_max_lemma_size               10
% 51.25/6.99  
% 51.25/6.99  ------ AIG Options
% 51.25/6.99  
% 51.25/6.99  --aig_mode                              false
% 51.25/6.99  
% 51.25/6.99  ------ Instantiation Options
% 51.25/6.99  
% 51.25/6.99  --instantiation_flag                    true
% 51.25/6.99  --inst_sos_flag                         false
% 51.25/6.99  --inst_sos_phase                        true
% 51.25/6.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.25/6.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.25/6.99  --inst_lit_sel_side                     num_symb
% 51.25/6.99  --inst_solver_per_active                1400
% 51.25/6.99  --inst_solver_calls_frac                1.
% 51.25/6.99  --inst_passive_queue_type               priority_queues
% 51.25/6.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.25/6.99  --inst_passive_queues_freq              [25;2]
% 51.25/6.99  --inst_dismatching                      true
% 51.25/6.99  --inst_eager_unprocessed_to_passive     true
% 51.25/6.99  --inst_prop_sim_given                   true
% 51.25/6.99  --inst_prop_sim_new                     false
% 51.25/6.99  --inst_subs_new                         false
% 51.25/6.99  --inst_eq_res_simp                      false
% 51.25/6.99  --inst_subs_given                       false
% 51.25/6.99  --inst_orphan_elimination               true
% 51.25/6.99  --inst_learning_loop_flag               true
% 51.25/6.99  --inst_learning_start                   3000
% 51.25/6.99  --inst_learning_factor                  2
% 51.25/6.99  --inst_start_prop_sim_after_learn       3
% 51.25/6.99  --inst_sel_renew                        solver
% 51.25/6.99  --inst_lit_activity_flag                true
% 51.25/6.99  --inst_restr_to_given                   false
% 51.25/6.99  --inst_activity_threshold               500
% 51.25/6.99  --inst_out_proof                        true
% 51.25/6.99  
% 51.25/6.99  ------ Resolution Options
% 51.25/6.99  
% 51.25/6.99  --resolution_flag                       true
% 51.25/6.99  --res_lit_sel                           adaptive
% 51.25/6.99  --res_lit_sel_side                      none
% 51.25/6.99  --res_ordering                          kbo
% 51.25/6.99  --res_to_prop_solver                    active
% 51.25/6.99  --res_prop_simpl_new                    false
% 51.25/6.99  --res_prop_simpl_given                  true
% 51.25/6.99  --res_passive_queue_type                priority_queues
% 51.25/6.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.25/6.99  --res_passive_queues_freq               [15;5]
% 51.25/6.99  --res_forward_subs                      full
% 51.25/6.99  --res_backward_subs                     full
% 51.25/6.99  --res_forward_subs_resolution           true
% 51.25/6.99  --res_backward_subs_resolution          true
% 51.25/6.99  --res_orphan_elimination                true
% 51.25/6.99  --res_time_limit                        2.
% 51.25/6.99  --res_out_proof                         true
% 51.25/6.99  
% 51.25/6.99  ------ Superposition Options
% 51.25/6.99  
% 51.25/6.99  --superposition_flag                    true
% 51.25/6.99  --sup_passive_queue_type                priority_queues
% 51.25/6.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.25/6.99  --sup_passive_queues_freq               [8;1;4]
% 51.25/6.99  --demod_completeness_check              fast
% 51.25/6.99  --demod_use_ground                      true
% 51.25/6.99  --sup_to_prop_solver                    passive
% 51.25/6.99  --sup_prop_simpl_new                    true
% 51.25/6.99  --sup_prop_simpl_given                  true
% 51.25/6.99  --sup_fun_splitting                     false
% 51.25/6.99  --sup_smt_interval                      50000
% 51.25/6.99  
% 51.25/6.99  ------ Superposition Simplification Setup
% 51.25/6.99  
% 51.25/6.99  --sup_indices_passive                   []
% 51.25/6.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.25/6.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.25/6.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.25/6.99  --sup_full_triv                         [TrivRules;PropSubs]
% 51.25/6.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.25/6.99  --sup_full_bw                           [BwDemod]
% 51.25/6.99  --sup_immed_triv                        [TrivRules]
% 51.25/6.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.25/6.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.25/6.99  --sup_immed_bw_main                     []
% 51.25/6.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.25/6.99  --sup_input_triv                        [Unflattening;TrivRules]
% 51.25/6.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.25/6.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.25/6.99  
% 51.25/6.99  ------ Combination Options
% 51.25/6.99  
% 51.25/6.99  --comb_res_mult                         3
% 51.25/6.99  --comb_sup_mult                         2
% 51.25/6.99  --comb_inst_mult                        10
% 51.25/6.99  
% 51.25/6.99  ------ Debug Options
% 51.25/6.99  
% 51.25/6.99  --dbg_backtrace                         false
% 51.25/6.99  --dbg_dump_prop_clauses                 false
% 51.25/6.99  --dbg_dump_prop_clauses_file            -
% 51.25/6.99  --dbg_out_stat                          false
% 51.25/6.99  ------ Parsing...
% 51.25/6.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.25/6.99  
% 51.25/6.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 51.25/6.99  
% 51.25/6.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.25/6.99  
% 51.25/6.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.25/6.99  ------ Proving...
% 51.25/6.99  ------ Problem Properties 
% 51.25/6.99  
% 51.25/6.99  
% 51.25/6.99  clauses                                 26
% 51.25/6.99  conjectures                             1
% 51.25/6.99  EPR                                     1
% 51.25/6.99  Horn                                    25
% 51.25/6.99  unary                                   8
% 51.25/6.99  binary                                  18
% 51.25/6.99  lits                                    44
% 51.25/6.99  lits eq                                 18
% 51.25/6.99  fd_pure                                 0
% 51.25/6.99  fd_pseudo                               0
% 51.25/6.99  fd_cond                                 5
% 51.25/6.99  fd_pseudo_cond                          0
% 51.25/6.99  AC symbols                              0
% 51.25/6.99  
% 51.25/6.99  ------ Schedule dynamic 5 is on 
% 51.25/6.99  
% 51.25/6.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 51.25/6.99  
% 51.25/6.99  
% 51.25/6.99  ------ 
% 51.25/6.99  Current options:
% 51.25/6.99  ------ 
% 51.25/6.99  
% 51.25/6.99  ------ Input Options
% 51.25/6.99  
% 51.25/6.99  --out_options                           all
% 51.25/6.99  --tptp_safe_out                         true
% 51.25/6.99  --problem_path                          ""
% 51.25/6.99  --include_path                          ""
% 51.25/6.99  --clausifier                            res/vclausify_rel
% 51.25/6.99  --clausifier_options                    --mode clausify
% 51.25/6.99  --stdin                                 false
% 51.25/6.99  --stats_out                             all
% 51.25/6.99  
% 51.25/6.99  ------ General Options
% 51.25/6.99  
% 51.25/6.99  --fof                                   false
% 51.25/6.99  --time_out_real                         305.
% 51.25/6.99  --time_out_virtual                      -1.
% 51.25/6.99  --symbol_type_check                     false
% 51.25/6.99  --clausify_out                          false
% 51.25/6.99  --sig_cnt_out                           false
% 51.25/6.99  --trig_cnt_out                          false
% 51.25/6.99  --trig_cnt_out_tolerance                1.
% 51.25/6.99  --trig_cnt_out_sk_spl                   false
% 51.25/6.99  --abstr_cl_out                          false
% 51.25/6.99  
% 51.25/6.99  ------ Global Options
% 51.25/6.99  
% 51.25/6.99  --schedule                              default
% 51.25/6.99  --add_important_lit                     false
% 51.25/6.99  --prop_solver_per_cl                    1000
% 51.25/6.99  --min_unsat_core                        false
% 51.25/6.99  --soft_assumptions                      false
% 51.25/6.99  --soft_lemma_size                       3
% 51.25/6.99  --prop_impl_unit_size                   0
% 51.25/6.99  --prop_impl_unit                        []
% 51.25/6.99  --share_sel_clauses                     true
% 51.25/6.99  --reset_solvers                         false
% 51.25/6.99  --bc_imp_inh                            [conj_cone]
% 51.25/6.99  --conj_cone_tolerance                   3.
% 51.25/6.99  --extra_neg_conj                        none
% 51.25/6.99  --large_theory_mode                     true
% 51.25/6.99  --prolific_symb_bound                   200
% 51.25/6.99  --lt_threshold                          2000
% 51.25/6.99  --clause_weak_htbl                      true
% 51.25/6.99  --gc_record_bc_elim                     false
% 51.25/6.99  
% 51.25/6.99  ------ Preprocessing Options
% 51.25/6.99  
% 51.25/6.99  --preprocessing_flag                    true
% 51.25/6.99  --time_out_prep_mult                    0.1
% 51.25/6.99  --splitting_mode                        input
% 51.25/6.99  --splitting_grd                         true
% 51.25/6.99  --splitting_cvd                         false
% 51.25/6.99  --splitting_cvd_svl                     false
% 51.25/6.99  --splitting_nvd                         32
% 51.25/6.99  --sub_typing                            true
% 51.25/6.99  --prep_gs_sim                           true
% 51.25/6.99  --prep_unflatten                        true
% 51.25/6.99  --prep_res_sim                          true
% 51.25/6.99  --prep_upred                            true
% 51.25/6.99  --prep_sem_filter                       exhaustive
% 51.25/6.99  --prep_sem_filter_out                   false
% 51.25/6.99  --pred_elim                             true
% 51.25/6.99  --res_sim_input                         true
% 51.25/6.99  --eq_ax_congr_red                       true
% 51.25/6.99  --pure_diseq_elim                       true
% 51.25/6.99  --brand_transform                       false
% 51.25/6.99  --non_eq_to_eq                          false
% 51.25/6.99  --prep_def_merge                        true
% 51.25/6.99  --prep_def_merge_prop_impl              false
% 51.25/6.99  --prep_def_merge_mbd                    true
% 51.25/6.99  --prep_def_merge_tr_red                 false
% 51.25/6.99  --prep_def_merge_tr_cl                  false
% 51.25/6.99  --smt_preprocessing                     true
% 51.25/6.99  --smt_ac_axioms                         fast
% 51.25/6.99  --preprocessed_out                      false
% 51.25/6.99  --preprocessed_stats                    false
% 51.25/6.99  
% 51.25/6.99  ------ Abstraction refinement Options
% 51.25/6.99  
% 51.25/6.99  --abstr_ref                             []
% 51.25/6.99  --abstr_ref_prep                        false
% 51.25/6.99  --abstr_ref_until_sat                   false
% 51.25/6.99  --abstr_ref_sig_restrict                funpre
% 51.25/6.99  --abstr_ref_af_restrict_to_split_sk     false
% 51.25/6.99  --abstr_ref_under                       []
% 51.25/6.99  
% 51.25/6.99  ------ SAT Options
% 51.25/6.99  
% 51.25/6.99  --sat_mode                              false
% 51.25/6.99  --sat_fm_restart_options                ""
% 51.25/6.99  --sat_gr_def                            false
% 51.25/6.99  --sat_epr_types                         true
% 51.25/6.99  --sat_non_cyclic_types                  false
% 51.25/6.99  --sat_finite_models                     false
% 51.25/6.99  --sat_fm_lemmas                         false
% 51.25/6.99  --sat_fm_prep                           false
% 51.25/6.99  --sat_fm_uc_incr                        true
% 51.25/6.99  --sat_out_model                         small
% 51.25/6.99  --sat_out_clauses                       false
% 51.25/6.99  
% 51.25/6.99  ------ QBF Options
% 51.25/6.99  
% 51.25/6.99  --qbf_mode                              false
% 51.25/6.99  --qbf_elim_univ                         false
% 51.25/6.99  --qbf_dom_inst                          none
% 51.25/6.99  --qbf_dom_pre_inst                      false
% 51.25/6.99  --qbf_sk_in                             false
% 51.25/6.99  --qbf_pred_elim                         true
% 51.25/6.99  --qbf_split                             512
% 51.25/6.99  
% 51.25/6.99  ------ BMC1 Options
% 51.25/6.99  
% 51.25/6.99  --bmc1_incremental                      false
% 51.25/6.99  --bmc1_axioms                           reachable_all
% 51.25/6.99  --bmc1_min_bound                        0
% 51.25/6.99  --bmc1_max_bound                        -1
% 51.25/6.99  --bmc1_max_bound_default                -1
% 51.25/6.99  --bmc1_symbol_reachability              true
% 51.25/6.99  --bmc1_property_lemmas                  false
% 51.25/6.99  --bmc1_k_induction                      false
% 51.25/6.99  --bmc1_non_equiv_states                 false
% 51.25/6.99  --bmc1_deadlock                         false
% 51.25/6.99  --bmc1_ucm                              false
% 51.25/6.99  --bmc1_add_unsat_core                   none
% 51.25/6.99  --bmc1_unsat_core_children              false
% 51.25/6.99  --bmc1_unsat_core_extrapolate_axioms    false
% 51.25/6.99  --bmc1_out_stat                         full
% 51.25/6.99  --bmc1_ground_init                      false
% 51.25/6.99  --bmc1_pre_inst_next_state              false
% 51.25/6.99  --bmc1_pre_inst_state                   false
% 51.25/6.99  --bmc1_pre_inst_reach_state             false
% 51.25/6.99  --bmc1_out_unsat_core                   false
% 51.25/6.99  --bmc1_aig_witness_out                  false
% 51.25/6.99  --bmc1_verbose                          false
% 51.25/6.99  --bmc1_dump_clauses_tptp                false
% 51.25/6.99  --bmc1_dump_unsat_core_tptp             false
% 51.25/6.99  --bmc1_dump_file                        -
% 51.25/6.99  --bmc1_ucm_expand_uc_limit              128
% 51.25/6.99  --bmc1_ucm_n_expand_iterations          6
% 51.25/6.99  --bmc1_ucm_extend_mode                  1
% 51.25/6.99  --bmc1_ucm_init_mode                    2
% 51.25/6.99  --bmc1_ucm_cone_mode                    none
% 51.25/6.99  --bmc1_ucm_reduced_relation_type        0
% 51.25/6.99  --bmc1_ucm_relax_model                  4
% 51.25/6.99  --bmc1_ucm_full_tr_after_sat            true
% 51.25/6.99  --bmc1_ucm_expand_neg_assumptions       false
% 51.25/6.99  --bmc1_ucm_layered_model                none
% 51.25/6.99  --bmc1_ucm_max_lemma_size               10
% 51.25/6.99  
% 51.25/6.99  ------ AIG Options
% 51.25/6.99  
% 51.25/6.99  --aig_mode                              false
% 51.25/6.99  
% 51.25/6.99  ------ Instantiation Options
% 51.25/6.99  
% 51.25/6.99  --instantiation_flag                    true
% 51.25/6.99  --inst_sos_flag                         false
% 51.25/6.99  --inst_sos_phase                        true
% 51.25/6.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.25/6.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.25/6.99  --inst_lit_sel_side                     none
% 51.25/6.99  --inst_solver_per_active                1400
% 51.25/6.99  --inst_solver_calls_frac                1.
% 51.25/6.99  --inst_passive_queue_type               priority_queues
% 51.25/6.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.25/6.99  --inst_passive_queues_freq              [25;2]
% 51.25/6.99  --inst_dismatching                      true
% 51.25/6.99  --inst_eager_unprocessed_to_passive     true
% 51.25/6.99  --inst_prop_sim_given                   true
% 51.25/6.99  --inst_prop_sim_new                     false
% 51.25/6.99  --inst_subs_new                         false
% 51.25/6.99  --inst_eq_res_simp                      false
% 51.25/6.99  --inst_subs_given                       false
% 51.25/6.99  --inst_orphan_elimination               true
% 51.25/6.99  --inst_learning_loop_flag               true
% 51.25/6.99  --inst_learning_start                   3000
% 51.25/6.99  --inst_learning_factor                  2
% 51.25/6.99  --inst_start_prop_sim_after_learn       3
% 51.25/6.99  --inst_sel_renew                        solver
% 51.25/6.99  --inst_lit_activity_flag                true
% 51.25/6.99  --inst_restr_to_given                   false
% 51.25/6.99  --inst_activity_threshold               500
% 51.25/6.99  --inst_out_proof                        true
% 51.25/6.99  
% 51.25/6.99  ------ Resolution Options
% 51.25/6.99  
% 51.25/6.99  --resolution_flag                       false
% 51.25/6.99  --res_lit_sel                           adaptive
% 51.25/6.99  --res_lit_sel_side                      none
% 51.25/6.99  --res_ordering                          kbo
% 51.25/6.99  --res_to_prop_solver                    active
% 51.25/6.99  --res_prop_simpl_new                    false
% 51.25/6.99  --res_prop_simpl_given                  true
% 51.25/6.99  --res_passive_queue_type                priority_queues
% 51.25/6.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.25/6.99  --res_passive_queues_freq               [15;5]
% 51.25/6.99  --res_forward_subs                      full
% 51.25/6.99  --res_backward_subs                     full
% 51.25/6.99  --res_forward_subs_resolution           true
% 51.25/6.99  --res_backward_subs_resolution          true
% 51.25/6.99  --res_orphan_elimination                true
% 51.25/6.99  --res_time_limit                        2.
% 51.25/6.99  --res_out_proof                         true
% 51.25/6.99  
% 51.25/6.99  ------ Superposition Options
% 51.25/6.99  
% 51.25/6.99  --superposition_flag                    true
% 51.25/6.99  --sup_passive_queue_type                priority_queues
% 51.25/6.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.25/6.99  --sup_passive_queues_freq               [8;1;4]
% 51.25/6.99  --demod_completeness_check              fast
% 51.25/6.99  --demod_use_ground                      true
% 51.25/6.99  --sup_to_prop_solver                    passive
% 51.25/6.99  --sup_prop_simpl_new                    true
% 51.25/6.99  --sup_prop_simpl_given                  true
% 51.25/6.99  --sup_fun_splitting                     false
% 51.25/6.99  --sup_smt_interval                      50000
% 51.25/6.99  
% 51.25/6.99  ------ Superposition Simplification Setup
% 51.25/6.99  
% 51.25/6.99  --sup_indices_passive                   []
% 51.25/6.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.25/6.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.25/6.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.25/6.99  --sup_full_triv                         [TrivRules;PropSubs]
% 51.25/6.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.25/6.99  --sup_full_bw                           [BwDemod]
% 51.25/6.99  --sup_immed_triv                        [TrivRules]
% 51.25/6.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.25/6.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.25/6.99  --sup_immed_bw_main                     []
% 51.25/6.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.25/6.99  --sup_input_triv                        [Unflattening;TrivRules]
% 51.25/6.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.25/6.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.25/6.99  
% 51.25/6.99  ------ Combination Options
% 51.25/6.99  
% 51.25/6.99  --comb_res_mult                         3
% 51.25/6.99  --comb_sup_mult                         2
% 51.25/6.99  --comb_inst_mult                        10
% 51.25/6.99  
% 51.25/6.99  ------ Debug Options
% 51.25/6.99  
% 51.25/6.99  --dbg_backtrace                         false
% 51.25/6.99  --dbg_dump_prop_clauses                 false
% 51.25/6.99  --dbg_dump_prop_clauses_file            -
% 51.25/6.99  --dbg_out_stat                          false
% 51.25/6.99  
% 51.25/6.99  
% 51.25/6.99  
% 51.25/6.99  
% 51.25/6.99  ------ Proving...
% 51.25/6.99  
% 51.25/6.99  
% 51.25/6.99  % SZS status Theorem for theBenchmark.p
% 51.25/6.99  
% 51.25/6.99  % SZS output start CNFRefutation for theBenchmark.p
% 51.25/6.99  
% 51.25/6.99  fof(f22,conjecture,(
% 51.25/6.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 51.25/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.25/6.99  
% 51.25/6.99  fof(f23,negated_conjecture,(
% 51.25/6.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 51.25/6.99    inference(negated_conjecture,[],[f22])).
% 51.25/6.99  
% 51.25/6.99  fof(f36,plain,(
% 51.25/6.99    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> r1_tarski(X1,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 51.25/6.99    inference(ennf_transformation,[],[f23])).
% 51.25/6.99  
% 51.25/6.99  fof(f39,plain,(
% 51.25/6.99    ? [X0] : (? [X1] : (((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 51.25/6.99    inference(nnf_transformation,[],[f36])).
% 51.25/6.99  
% 51.25/6.99  fof(f40,plain,(
% 51.25/6.99    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 51.25/6.99    inference(flattening,[],[f39])).
% 51.25/6.99  
% 51.25/6.99  fof(f42,plain,(
% 51.25/6.99    ( ! [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~r1_tarski(sK1,k2_tops_1(X0,sK1)) | ~v2_tops_1(sK1,X0)) & (r1_tarski(sK1,k2_tops_1(X0,sK1)) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 51.25/6.99    introduced(choice_axiom,[])).
% 51.25/6.99  
% 51.25/6.99  fof(f41,plain,(
% 51.25/6.99    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 51.25/6.99    introduced(choice_axiom,[])).
% 51.25/6.99  
% 51.25/6.99  fof(f43,plain,(
% 51.25/6.99    ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 51.25/6.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).
% 51.25/6.99  
% 51.25/6.99  fof(f71,plain,(
% 51.25/6.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 51.25/6.99    inference(cnf_transformation,[],[f43])).
% 51.25/6.99  
% 51.25/6.99  fof(f72,plain,(
% 51.25/6.99    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 51.25/6.99    inference(cnf_transformation,[],[f43])).
% 51.25/6.99  
% 51.25/6.99  fof(f21,axiom,(
% 51.25/6.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 51.25/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.25/6.99  
% 51.25/6.99  fof(f35,plain,(
% 51.25/6.99    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 51.25/6.99    inference(ennf_transformation,[],[f21])).
% 51.25/6.99  
% 51.25/6.99  fof(f38,plain,(
% 51.25/6.99    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 51.25/6.99    inference(nnf_transformation,[],[f35])).
% 51.25/6.99  
% 51.25/6.99  fof(f68,plain,(
% 51.25/6.99    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 51.25/6.99    inference(cnf_transformation,[],[f38])).
% 51.25/6.99  
% 51.25/6.99  fof(f70,plain,(
% 51.25/6.99    l1_pre_topc(sK0)),
% 51.25/6.99    inference(cnf_transformation,[],[f43])).
% 51.25/6.99  
% 51.25/6.99  fof(f3,axiom,(
% 51.25/6.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 51.25/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.25/6.99  
% 51.25/6.99  fof(f25,plain,(
% 51.25/6.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 51.25/6.99    inference(ennf_transformation,[],[f3])).
% 51.25/6.99  
% 51.25/6.99  fof(f46,plain,(
% 51.25/6.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 51.25/6.99    inference(cnf_transformation,[],[f25])).
% 51.25/6.99  
% 51.25/6.99  fof(f8,axiom,(
% 51.25/6.99    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 51.25/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.25/6.99  
% 51.25/6.99  fof(f51,plain,(
% 51.25/6.99    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 51.25/6.99    inference(cnf_transformation,[],[f8])).
% 51.25/6.99  
% 51.25/6.99  fof(f1,axiom,(
% 51.25/6.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 51.25/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.25/6.99  
% 51.25/6.99  fof(f44,plain,(
% 51.25/6.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 51.25/6.99    inference(cnf_transformation,[],[f1])).
% 51.25/6.99  
% 51.25/6.99  fof(f77,plain,(
% 51.25/6.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))) = k1_xboole_0) )),
% 51.25/6.99    inference(definition_unfolding,[],[f51,f44])).
% 51.25/6.99  
% 51.25/6.99  fof(f9,axiom,(
% 51.25/6.99    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 51.25/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.25/6.99  
% 51.25/6.99  fof(f52,plain,(
% 51.25/6.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 51.25/6.99    inference(cnf_transformation,[],[f9])).
% 51.25/6.99  
% 51.25/6.99  fof(f74,plain,(
% 51.25/6.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 51.25/6.99    inference(definition_unfolding,[],[f52,f44,f44])).
% 51.25/6.99  
% 51.25/6.99  fof(f5,axiom,(
% 51.25/6.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 51.25/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.25/6.99  
% 51.25/6.99  fof(f48,plain,(
% 51.25/6.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 51.25/6.99    inference(cnf_transformation,[],[f5])).
% 51.25/6.99  
% 51.25/6.99  fof(f75,plain,(
% 51.25/6.99    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 51.25/6.99    inference(definition_unfolding,[],[f48,f44])).
% 51.25/6.99  
% 51.25/6.99  fof(f20,axiom,(
% 51.25/6.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 51.25/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.25/6.99  
% 51.25/6.99  fof(f34,plain,(
% 51.25/6.99    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 51.25/6.99    inference(ennf_transformation,[],[f20])).
% 51.25/6.99  
% 51.25/6.99  fof(f67,plain,(
% 51.25/6.99    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 51.25/6.99    inference(cnf_transformation,[],[f34])).
% 51.25/6.99  
% 51.25/6.99  fof(f17,axiom,(
% 51.25/6.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 51.25/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.25/6.99  
% 51.25/6.99  fof(f37,plain,(
% 51.25/6.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 51.25/6.99    inference(nnf_transformation,[],[f17])).
% 51.25/6.99  
% 51.25/6.99  fof(f60,plain,(
% 51.25/6.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 51.25/6.99    inference(cnf_transformation,[],[f37])).
% 51.25/6.99  
% 51.25/6.99  fof(f15,axiom,(
% 51.25/6.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 51.25/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.25/6.99  
% 51.25/6.99  fof(f31,plain,(
% 51.25/6.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.25/6.99    inference(ennf_transformation,[],[f15])).
% 51.25/6.99  
% 51.25/6.99  fof(f58,plain,(
% 51.25/6.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 51.25/6.99    inference(cnf_transformation,[],[f31])).
% 51.25/6.99  
% 51.25/6.99  fof(f79,plain,(
% 51.25/6.99    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 51.25/6.99    inference(definition_unfolding,[],[f58,f44])).
% 51.25/6.99  
% 51.25/6.99  fof(f61,plain,(
% 51.25/6.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 51.25/6.99    inference(cnf_transformation,[],[f37])).
% 51.25/6.99  
% 51.25/6.99  fof(f4,axiom,(
% 51.25/6.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 51.25/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.25/6.99  
% 51.25/6.99  fof(f47,plain,(
% 51.25/6.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 51.25/6.99    inference(cnf_transformation,[],[f4])).
% 51.25/6.99  
% 51.25/6.99  fof(f11,axiom,(
% 51.25/6.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 51.25/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.25/6.99  
% 51.25/6.99  fof(f54,plain,(
% 51.25/6.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 51.25/6.99    inference(cnf_transformation,[],[f11])).
% 51.25/6.99  
% 51.25/6.99  fof(f16,axiom,(
% 51.25/6.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 51.25/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.25/6.99  
% 51.25/6.99  fof(f59,plain,(
% 51.25/6.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 51.25/6.99    inference(cnf_transformation,[],[f16])).
% 51.25/6.99  
% 51.25/6.99  fof(f12,axiom,(
% 51.25/6.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 51.25/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.25/6.99  
% 51.25/6.99  fof(f28,plain,(
% 51.25/6.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 51.25/6.99    inference(ennf_transformation,[],[f12])).
% 51.25/6.99  
% 51.25/6.99  fof(f55,plain,(
% 51.25/6.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 51.25/6.99    inference(cnf_transformation,[],[f28])).
% 51.25/6.99  
% 51.25/6.99  fof(f78,plain,(
% 51.25/6.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 51.25/6.99    inference(definition_unfolding,[],[f55,f44])).
% 51.25/6.99  
% 51.25/6.99  fof(f6,axiom,(
% 51.25/6.99    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 51.25/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.25/6.99  
% 51.25/6.99  fof(f26,plain,(
% 51.25/6.99    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 51.25/6.99    inference(ennf_transformation,[],[f6])).
% 51.25/6.99  
% 51.25/6.99  fof(f49,plain,(
% 51.25/6.99    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 51.25/6.99    inference(cnf_transformation,[],[f26])).
% 51.25/6.99  
% 51.25/6.99  fof(f10,axiom,(
% 51.25/6.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 51.25/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.25/6.99  
% 51.25/6.99  fof(f53,plain,(
% 51.25/6.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 51.25/6.99    inference(cnf_transformation,[],[f10])).
% 51.25/6.99  
% 51.25/6.99  fof(f7,axiom,(
% 51.25/6.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 51.25/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.25/6.99  
% 51.25/6.99  fof(f27,plain,(
% 51.25/6.99    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 51.25/6.99    inference(ennf_transformation,[],[f7])).
% 51.25/6.99  
% 51.25/6.99  fof(f50,plain,(
% 51.25/6.99    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 51.25/6.99    inference(cnf_transformation,[],[f27])).
% 51.25/6.99  
% 51.25/6.99  fof(f76,plain,(
% 51.25/6.99    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 51.25/6.99    inference(definition_unfolding,[],[f50,f44])).
% 51.25/6.99  
% 51.25/6.99  fof(f73,plain,(
% 51.25/6.99    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)),
% 51.25/6.99    inference(cnf_transformation,[],[f43])).
% 51.25/6.99  
% 51.25/6.99  fof(f69,plain,(
% 51.25/6.99    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 51.25/6.99    inference(cnf_transformation,[],[f38])).
% 51.25/6.99  
% 51.25/6.99  cnf(c_889,plain,
% 51.25/6.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 51.25/6.99      theory(equality) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_166582,plain,
% 51.25/6.99      ( ~ r1_tarski(X0,X1)
% 51.25/6.99      | r1_tarski(X2,k2_tops_1(sK0,sK1))
% 51.25/6.99      | X2 != X0
% 51.25/6.99      | k2_tops_1(sK0,sK1) != X1 ),
% 51.25/6.99      inference(instantiation,[status(thm)],[c_889]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_176603,plain,
% 51.25/6.99      ( ~ r1_tarski(X0,k2_tops_1(sK0,sK1))
% 51.25/6.99      | r1_tarski(X1,k2_tops_1(sK0,sK1))
% 51.25/6.99      | X1 != X0
% 51.25/6.99      | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) ),
% 51.25/6.99      inference(instantiation,[status(thm)],[c_166582]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_192942,plain,
% 51.25/6.99      ( ~ r1_tarski(X0,k2_tops_1(sK0,sK1))
% 51.25/6.99      | r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)),k2_tops_1(sK0,sK1))
% 51.25/6.99      | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
% 51.25/6.99      | k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)) != X0 ),
% 51.25/6.99      inference(instantiation,[status(thm)],[c_176603]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_219750,plain,
% 51.25/6.99      ( ~ r1_tarski(k3_subset_1(sK1,k1_xboole_0),k2_tops_1(sK0,sK1))
% 51.25/6.99      | r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)),k2_tops_1(sK0,sK1))
% 51.25/6.99      | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
% 51.25/6.99      | k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)) != k3_subset_1(sK1,k1_xboole_0) ),
% 51.25/6.99      inference(instantiation,[status(thm)],[c_192942]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_27,negated_conjecture,
% 51.25/6.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 51.25/6.99      inference(cnf_transformation,[],[f71]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_26,negated_conjecture,
% 51.25/6.99      ( v2_tops_1(sK1,sK0) | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 51.25/6.99      inference(cnf_transformation,[],[f72]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_210,plain,
% 51.25/6.99      ( v2_tops_1(sK1,sK0) | r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 51.25/6.99      inference(prop_impl,[status(thm)],[c_26]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_24,plain,
% 51.25/6.99      ( ~ v2_tops_1(X0,X1)
% 51.25/6.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.25/6.99      | ~ l1_pre_topc(X1)
% 51.25/6.99      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 51.25/6.99      inference(cnf_transformation,[],[f68]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_28,negated_conjecture,
% 51.25/6.99      ( l1_pre_topc(sK0) ),
% 51.25/6.99      inference(cnf_transformation,[],[f70]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_354,plain,
% 51.25/6.99      ( ~ v2_tops_1(X0,X1)
% 51.25/6.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.25/6.99      | k1_tops_1(X1,X0) = k1_xboole_0
% 51.25/6.99      | sK0 != X1 ),
% 51.25/6.99      inference(resolution_lifted,[status(thm)],[c_24,c_28]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_355,plain,
% 51.25/6.99      ( ~ v2_tops_1(X0,sK0)
% 51.25/6.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.25/6.99      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 51.25/6.99      inference(unflattening,[status(thm)],[c_354]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_424,plain,
% 51.25/6.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.25/6.99      | r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 51.25/6.99      | k1_tops_1(sK0,X0) = k1_xboole_0
% 51.25/6.99      | sK0 != sK0
% 51.25/6.99      | sK1 != X0 ),
% 51.25/6.99      inference(resolution_lifted,[status(thm)],[c_210,c_355]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_425,plain,
% 51.25/6.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.25/6.99      | r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 51.25/6.99      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 51.25/6.99      inference(unflattening,[status(thm)],[c_424]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_662,plain,
% 51.25/6.99      ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 51.25/6.99      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 51.25/6.99      inference(prop_impl,[status(thm)],[c_27,c_425]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_1399,plain,
% 51.25/6.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 51.25/6.99      | r1_tarski(sK1,k2_tops_1(sK0,sK1)) = iProver_top ),
% 51.25/6.99      inference(predicate_to_equality,[status(thm)],[c_662]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_2,plain,
% 51.25/6.99      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 51.25/6.99      inference(cnf_transformation,[],[f46]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_1417,plain,
% 51.25/6.99      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 51.25/6.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_3108,plain,
% 51.25/6.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 51.25/6.99      | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 51.25/6.99      inference(superposition,[status(thm)],[c_1399,c_1417]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_7,plain,
% 51.25/6.99      ( k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))) = k1_xboole_0 ),
% 51.25/6.99      inference(cnf_transformation,[],[f77]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_0,plain,
% 51.25/6.99      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 51.25/6.99      inference(cnf_transformation,[],[f74]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_1865,plain,
% 51.25/6.99      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 51.25/6.99      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_4,plain,
% 51.25/6.99      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 51.25/6.99      inference(cnf_transformation,[],[f75]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_1870,plain,
% 51.25/6.99      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
% 51.25/6.99      inference(light_normalisation,[status(thm)],[c_1865,c_4]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_9107,plain,
% 51.25/6.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 51.25/6.99      | k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
% 51.25/6.99      inference(superposition,[status(thm)],[c_3108,c_1870]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_1406,plain,
% 51.25/6.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 51.25/6.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_22,plain,
% 51.25/6.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.25/6.99      | ~ l1_pre_topc(X1)
% 51.25/6.99      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 51.25/6.99      inference(cnf_transformation,[],[f67]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_384,plain,
% 51.25/6.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.25/6.99      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 51.25/6.99      | sK0 != X1 ),
% 51.25/6.99      inference(resolution_lifted,[status(thm)],[c_22,c_28]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_385,plain,
% 51.25/6.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.25/6.99      | k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 51.25/6.99      inference(unflattening,[status(thm)],[c_384]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_1401,plain,
% 51.25/6.99      ( k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 51.25/6.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 51.25/6.99      inference(predicate_to_equality,[status(thm)],[c_385]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_1632,plain,
% 51.25/6.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 51.25/6.99      inference(superposition,[status(thm)],[c_1406,c_1401]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_16,plain,
% 51.25/6.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 51.25/6.99      inference(cnf_transformation,[],[f60]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_1411,plain,
% 51.25/6.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 51.25/6.99      | r1_tarski(X0,X1) = iProver_top ),
% 51.25/6.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_4274,plain,
% 51.25/6.99      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 51.25/6.99      inference(superposition,[status(thm)],[c_1406,c_1411]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_13,plain,
% 51.25/6.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 51.25/6.99      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 51.25/6.99      inference(cnf_transformation,[],[f79]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_15,plain,
% 51.25/6.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 51.25/6.99      inference(cnf_transformation,[],[f61]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_206,plain,
% 51.25/6.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 51.25/6.99      inference(prop_impl,[status(thm)],[c_15]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_207,plain,
% 51.25/6.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 51.25/6.99      inference(renaming,[status(thm)],[c_206]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_254,plain,
% 51.25/6.99      ( ~ r1_tarski(X0,X1)
% 51.25/6.99      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 51.25/6.99      inference(bin_hyper_res,[status(thm)],[c_13,c_207]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_1402,plain,
% 51.25/6.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 51.25/6.99      | r1_tarski(X0,X2) != iProver_top ),
% 51.25/6.99      inference(predicate_to_equality,[status(thm)],[c_254]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_123881,plain,
% 51.25/6.99      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 51.25/6.99      inference(superposition,[status(thm)],[c_4274,c_1402]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_125984,plain,
% 51.25/6.99      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
% 51.25/6.99      inference(superposition,[status(thm)],[c_1632,c_123881]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_126050,plain,
% 51.25/6.99      ( k1_tops_1(sK0,sK1) = k5_xboole_0(sK1,sK1)
% 51.25/6.99      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 51.25/6.99      inference(superposition,[status(thm)],[c_9107,c_125984]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_2006,plain,
% 51.25/6.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 51.25/6.99      inference(demodulation,[status(thm)],[c_1870,c_7]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_126192,plain,
% 51.25/6.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 51.25/6.99      inference(demodulation,[status(thm)],[c_126050,c_2006]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_126220,plain,
% 51.25/6.99      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k1_xboole_0 ),
% 51.25/6.99      inference(demodulation,[status(thm)],[c_126192,c_125984]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_3,plain,
% 51.25/6.99      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 51.25/6.99      inference(cnf_transformation,[],[f47]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_1416,plain,
% 51.25/6.99      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 51.25/6.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_3106,plain,
% 51.25/6.99      ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
% 51.25/6.99      inference(superposition,[status(thm)],[c_1416,c_1417]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_4047,plain,
% 51.25/6.99      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 51.25/6.99      inference(superposition,[status(thm)],[c_3106,c_1870]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_9,plain,
% 51.25/6.99      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 51.25/6.99      inference(cnf_transformation,[],[f54]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_14,plain,
% 51.25/6.99      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
% 51.25/6.99      inference(cnf_transformation,[],[f59]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_1830,plain,
% 51.25/6.99      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X1,X0) ),
% 51.25/6.99      inference(superposition,[status(thm)],[c_9,c_14]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_2508,plain,
% 51.25/6.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 51.25/6.99      inference(superposition,[status(thm)],[c_1830,c_14]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_12208,plain,
% 51.25/6.99      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 51.25/6.99      inference(superposition,[status(thm)],[c_4047,c_2508]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_2516,plain,
% 51.25/6.99      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,X1) ),
% 51.25/6.99      inference(superposition,[status(thm)],[c_2508,c_0]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_4429,plain,
% 51.25/6.99      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0))) ),
% 51.25/6.99      inference(superposition,[status(thm)],[c_2516,c_0]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_14691,plain,
% 51.25/6.99      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 51.25/6.99      inference(demodulation,[status(thm)],[c_12208,c_4429]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_24541,plain,
% 51.25/6.99      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 51.25/6.99      inference(superposition,[status(thm)],[c_14691,c_1416]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_10,plain,
% 51.25/6.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 51.25/6.99      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 51.25/6.99      inference(cnf_transformation,[],[f78]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_251,plain,
% 51.25/6.99      ( ~ r1_tarski(X0,X1)
% 51.25/6.99      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 51.25/6.99      inference(bin_hyper_res,[status(thm)],[c_10,c_207]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_1405,plain,
% 51.25/6.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 51.25/6.99      | r1_tarski(X1,X0) != iProver_top ),
% 51.25/6.99      inference(predicate_to_equality,[status(thm)],[c_251]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_26658,plain,
% 51.25/6.99      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 51.25/6.99      inference(superposition,[status(thm)],[c_24541,c_1405]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_26727,plain,
% 51.25/6.99      ( k3_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,X1) ),
% 51.25/6.99      inference(light_normalisation,[status(thm)],[c_26658,c_0]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_126241,plain,
% 51.25/6.99      ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_xboole_0) ),
% 51.25/6.99      inference(superposition,[status(thm)],[c_126220,c_26727]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_2515,plain,
% 51.25/6.99      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 51.25/6.99      inference(superposition,[status(thm)],[c_2508,c_1416]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_127378,plain,
% 51.25/6.99      ( r1_tarski(k3_subset_1(sK1,k1_xboole_0),k2_tops_1(sK0,sK1)) = iProver_top ),
% 51.25/6.99      inference(superposition,[status(thm)],[c_126241,c_2515]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_127869,plain,
% 51.25/6.99      ( r1_tarski(k3_subset_1(sK1,k1_xboole_0),k2_tops_1(sK0,sK1)) ),
% 51.25/6.99      inference(predicate_to_equality_rev,[status(thm)],[c_127378]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_3033,plain,
% 51.25/6.99      ( ~ r1_tarski(X0,X1)
% 51.25/6.99      | r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 51.25/6.99      | k2_tops_1(sK0,sK1) != X1
% 51.25/6.99      | sK1 != X0 ),
% 51.25/6.99      inference(instantiation,[status(thm)],[c_889]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_15131,plain,
% 51.25/6.99      ( ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)),X0)
% 51.25/6.99      | r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 51.25/6.99      | k2_tops_1(sK0,sK1) != X0
% 51.25/6.99      | sK1 != k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)) ),
% 51.25/6.99      inference(instantiation,[status(thm)],[c_3033]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_46408,plain,
% 51.25/6.99      ( ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)),k2_tops_1(sK0,sK1))
% 51.25/6.99      | r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 51.25/6.99      | k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
% 51.25/6.99      | sK1 != k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)) ),
% 51.25/6.99      inference(instantiation,[status(thm)],[c_15131]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_33552,plain,
% 51.25/6.99      ( ~ r1_tarski(k1_xboole_0,sK1)
% 51.25/6.99      | k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)) = k3_subset_1(sK1,k1_xboole_0) ),
% 51.25/6.99      inference(instantiation,[status(thm)],[c_251]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_5,plain,
% 51.25/6.99      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 51.25/6.99      inference(cnf_transformation,[],[f49]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_11913,plain,
% 51.25/6.99      ( ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_xboole_0)
% 51.25/6.99      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 51.25/6.99      inference(instantiation,[status(thm)],[c_5]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_11917,plain,
% 51.25/6.99      ( ~ r1_tarski(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
% 51.25/6.99      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 51.25/6.99      inference(instantiation,[status(thm)],[c_11913]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_885,plain,( X0 = X0 ),theory(equality) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_9865,plain,
% 51.25/6.99      ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,sK1) ),
% 51.25/6.99      inference(instantiation,[status(thm)],[c_885]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_1696,plain,
% 51.25/6.99      ( r1_tarski(X0,X1)
% 51.25/6.99      | ~ r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X3)),X4)
% 51.25/6.99      | X1 != X4
% 51.25/6.99      | X0 != k5_xboole_0(X2,k3_xboole_0(X2,X3)) ),
% 51.25/6.99      inference(instantiation,[status(thm)],[c_889]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_3839,plain,
% 51.25/6.99      ( r1_tarski(X0,sK1)
% 51.25/6.99      | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)
% 51.25/6.99      | X0 != k5_xboole_0(X1,k3_xboole_0(X1,X2))
% 51.25/6.99      | sK1 != X3 ),
% 51.25/6.99      inference(instantiation,[status(thm)],[c_1696]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_8292,plain,
% 51.25/6.99      ( r1_tarski(X0,sK1)
% 51.25/6.99      | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),sK1)
% 51.25/6.99      | X0 != k5_xboole_0(X1,k3_xboole_0(X1,X2))
% 51.25/6.99      | sK1 != sK1 ),
% 51.25/6.99      inference(instantiation,[status(thm)],[c_3839]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_8294,plain,
% 51.25/6.99      ( ~ r1_tarski(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),sK1)
% 51.25/6.99      | r1_tarski(k1_xboole_0,sK1)
% 51.25/6.99      | sK1 != sK1
% 51.25/6.99      | k1_xboole_0 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 51.25/6.99      inference(instantiation,[status(thm)],[c_8292]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_886,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_2562,plain,
% 51.25/6.99      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 51.25/6.99      inference(instantiation,[status(thm)],[c_886]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_4773,plain,
% 51.25/6.99      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 51.25/6.99      inference(instantiation,[status(thm)],[c_2562]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_7084,plain,
% 51.25/6.99      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)) != sK1
% 51.25/6.99      | sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))
% 51.25/6.99      | sK1 != sK1 ),
% 51.25/6.99      inference(instantiation,[status(thm)],[c_4773]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_8,plain,
% 51.25/6.99      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 51.25/6.99      inference(cnf_transformation,[],[f53]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_5014,plain,
% 51.25/6.99      ( r1_tarski(X0,k2_xboole_0(X0,sK1)) ),
% 51.25/6.99      inference(instantiation,[status(thm)],[c_8]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_5016,plain,
% 51.25/6.99      ( r1_tarski(k1_xboole_0,k2_xboole_0(k1_xboole_0,sK1)) ),
% 51.25/6.99      inference(instantiation,[status(thm)],[c_5014]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_6,plain,
% 51.25/6.99      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 51.25/6.99      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
% 51.25/6.99      inference(cnf_transformation,[],[f76]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_2637,plain,
% 51.25/6.99      ( ~ r1_tarski(X0,k2_xboole_0(X1,sK1))
% 51.25/6.99      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),sK1) ),
% 51.25/6.99      inference(instantiation,[status(thm)],[c_6]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_2639,plain,
% 51.25/6.99      ( r1_tarski(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),sK1)
% 51.25/6.99      | ~ r1_tarski(k1_xboole_0,k2_xboole_0(k1_xboole_0,sK1)) ),
% 51.25/6.99      inference(instantiation,[status(thm)],[c_2637]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_1784,plain,
% 51.25/6.99      ( sK1 = sK1 ),
% 51.25/6.99      inference(instantiation,[status(thm)],[c_885]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_1752,plain,
% 51.25/6.99      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)) = sK1 ),
% 51.25/6.99      inference(instantiation,[status(thm)],[c_4]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_25,negated_conjecture,
% 51.25/6.99      ( ~ v2_tops_1(sK1,sK0) | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 51.25/6.99      inference(cnf_transformation,[],[f73]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_208,plain,
% 51.25/6.99      ( ~ v2_tops_1(sK1,sK0) | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 51.25/6.99      inference(prop_impl,[status(thm)],[c_25]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_23,plain,
% 51.25/6.99      ( v2_tops_1(X0,X1)
% 51.25/6.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.25/6.99      | ~ l1_pre_topc(X1)
% 51.25/6.99      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 51.25/6.99      inference(cnf_transformation,[],[f69]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_369,plain,
% 51.25/6.99      ( v2_tops_1(X0,X1)
% 51.25/6.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 51.25/6.99      | k1_tops_1(X1,X0) != k1_xboole_0
% 51.25/6.99      | sK0 != X1 ),
% 51.25/6.99      inference(resolution_lifted,[status(thm)],[c_23,c_28]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_370,plain,
% 51.25/6.99      ( v2_tops_1(X0,sK0)
% 51.25/6.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.25/6.99      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 51.25/6.99      inference(unflattening,[status(thm)],[c_369]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_438,plain,
% 51.25/6.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.25/6.99      | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 51.25/6.99      | k1_tops_1(sK0,X0) != k1_xboole_0
% 51.25/6.99      | sK0 != sK0
% 51.25/6.99      | sK1 != X0 ),
% 51.25/6.99      inference(resolution_lifted,[status(thm)],[c_208,c_370]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_439,plain,
% 51.25/6.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 51.25/6.99      | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 51.25/6.99      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 51.25/6.99      inference(unflattening,[status(thm)],[c_438]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_441,plain,
% 51.25/6.99      ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 51.25/6.99      | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 51.25/6.99      inference(global_propositional_subsumption,
% 51.25/6.99                [status(thm)],
% 51.25/6.99                [c_439,c_27]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_76,plain,
% 51.25/6.99      ( r1_tarski(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
% 51.25/6.99      | ~ r1_tarski(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 51.25/6.99      inference(instantiation,[status(thm)],[c_6]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(c_72,plain,
% 51.25/6.99      ( r1_tarski(k1_xboole_0,k2_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 51.25/6.99      inference(instantiation,[status(thm)],[c_8]) ).
% 51.25/6.99  
% 51.25/6.99  cnf(contradiction,plain,
% 51.25/6.99      ( $false ),
% 51.25/6.99      inference(minisat,
% 51.25/6.99                [status(thm)],
% 51.25/6.99                [c_219750,c_127869,c_126192,c_46408,c_33552,c_11917,
% 51.25/6.99                 c_9865,c_8294,c_7084,c_5016,c_2639,c_1784,c_1752,c_441,
% 51.25/6.99                 c_76,c_72]) ).
% 51.25/6.99  
% 51.25/6.99  
% 51.25/6.99  % SZS output end CNFRefutation for theBenchmark.p
% 51.25/6.99  
% 51.25/6.99  ------                               Statistics
% 51.25/6.99  
% 51.25/6.99  ------ General
% 51.25/6.99  
% 51.25/6.99  abstr_ref_over_cycles:                  0
% 51.25/6.99  abstr_ref_under_cycles:                 0
% 51.25/6.99  gc_basic_clause_elim:                   0
% 51.25/6.99  forced_gc_time:                         0
% 51.25/6.99  parsing_time:                           0.009
% 51.25/6.99  unif_index_cands_time:                  0.
% 51.25/6.99  unif_index_add_time:                    0.
% 51.25/6.99  orderings_time:                         0.
% 51.25/6.99  out_proof_time:                         0.021
% 51.25/6.99  total_time:                             6.098
% 51.25/6.99  num_of_symbols:                         50
% 51.25/6.99  num_of_terms:                           233879
% 51.25/6.99  
% 51.25/6.99  ------ Preprocessing
% 51.25/6.99  
% 51.25/6.99  num_of_splits:                          0
% 51.25/6.99  num_of_split_atoms:                     0
% 51.25/6.99  num_of_reused_defs:                     0
% 51.25/6.99  num_eq_ax_congr_red:                    35
% 51.25/6.99  num_of_sem_filtered_clauses:            1
% 51.25/6.99  num_of_subtypes:                        0
% 51.25/6.99  monotx_restored_types:                  0
% 51.25/6.99  sat_num_of_epr_types:                   0
% 51.25/6.99  sat_num_of_non_cyclic_types:            0
% 51.25/6.99  sat_guarded_non_collapsed_types:        0
% 51.25/6.99  num_pure_diseq_elim:                    0
% 51.25/6.99  simp_replaced_by:                       0
% 51.25/6.99  res_preprocessed:                       134
% 51.25/6.99  prep_upred:                             0
% 51.25/6.99  prep_unflattend:                        22
% 51.25/6.99  smt_new_axioms:                         0
% 51.25/6.99  pred_elim_cands:                        2
% 51.25/6.99  pred_elim:                              2
% 51.25/6.99  pred_elim_cl:                           3
% 51.25/6.99  pred_elim_cycles:                       4
% 51.25/6.99  merged_defs:                            16
% 51.25/6.99  merged_defs_ncl:                        0
% 51.25/6.99  bin_hyper_res:                          20
% 51.25/6.99  prep_cycles:                            4
% 51.25/6.99  pred_elim_time:                         0.006
% 51.25/6.99  splitting_time:                         0.
% 51.25/6.99  sem_filter_time:                        0.
% 51.25/6.99  monotx_time:                            0.
% 51.25/6.99  subtype_inf_time:                       0.
% 51.25/6.99  
% 51.25/6.99  ------ Problem properties
% 51.25/6.99  
% 51.25/6.99  clauses:                                26
% 51.25/6.99  conjectures:                            1
% 51.25/6.99  epr:                                    1
% 51.25/6.99  horn:                                   25
% 51.25/6.99  ground:                                 3
% 51.25/6.99  unary:                                  8
% 51.25/6.99  binary:                                 18
% 51.25/6.99  lits:                                   44
% 51.25/6.99  lits_eq:                                18
% 51.25/6.99  fd_pure:                                0
% 51.25/6.99  fd_pseudo:                              0
% 51.25/6.99  fd_cond:                                5
% 51.25/6.99  fd_pseudo_cond:                         0
% 51.25/6.99  ac_symbols:                             0
% 51.25/6.99  
% 51.25/6.99  ------ Propositional Solver
% 51.25/6.99  
% 51.25/6.99  prop_solver_calls:                      74
% 51.25/6.99  prop_fast_solver_calls:                 1702
% 51.25/6.99  smt_solver_calls:                       0
% 51.25/6.99  smt_fast_solver_calls:                  0
% 51.25/6.99  prop_num_of_clauses:                    73797
% 51.25/6.99  prop_preprocess_simplified:             79373
% 51.25/6.99  prop_fo_subsumed:                       15
% 51.25/6.99  prop_solver_time:                       0.
% 51.25/6.99  smt_solver_time:                        0.
% 51.25/6.99  smt_fast_solver_time:                   0.
% 51.25/6.99  prop_fast_solver_time:                  0.
% 51.25/6.99  prop_unsat_core_time:                   0.009
% 51.25/6.99  
% 51.25/6.99  ------ QBF
% 51.25/6.99  
% 51.25/6.99  qbf_q_res:                              0
% 51.25/6.99  qbf_num_tautologies:                    0
% 51.25/6.99  qbf_prep_cycles:                        0
% 51.25/6.99  
% 51.25/6.99  ------ BMC1
% 51.25/6.99  
% 51.25/6.99  bmc1_current_bound:                     -1
% 51.25/6.99  bmc1_last_solved_bound:                 -1
% 51.25/6.99  bmc1_unsat_core_size:                   -1
% 51.25/6.99  bmc1_unsat_core_parents_size:           -1
% 51.25/6.99  bmc1_merge_next_fun:                    0
% 51.25/6.99  bmc1_unsat_core_clauses_time:           0.
% 51.25/6.99  
% 51.25/6.99  ------ Instantiation
% 51.25/6.99  
% 51.25/6.99  inst_num_of_clauses:                    2212
% 51.25/6.99  inst_num_in_passive:                    610
% 51.25/6.99  inst_num_in_active:                     3269
% 51.25/6.99  inst_num_in_unprocessed:                801
% 51.25/6.99  inst_num_of_loops:                      3842
% 51.25/6.99  inst_num_of_learning_restarts:          1
% 51.25/6.99  inst_num_moves_active_passive:          568
% 51.25/6.99  inst_lit_activity:                      0
% 51.25/6.99  inst_lit_activity_moves:                1
% 51.25/6.99  inst_num_tautologies:                   0
% 51.25/6.99  inst_num_prop_implied:                  0
% 51.25/6.99  inst_num_existing_simplified:           0
% 51.25/6.99  inst_num_eq_res_simplified:             0
% 51.25/6.99  inst_num_child_elim:                    0
% 51.25/6.99  inst_num_of_dismatching_blockings:      12754
% 51.25/6.99  inst_num_of_non_proper_insts:           11199
% 51.25/6.99  inst_num_of_duplicates:                 0
% 51.25/6.99  inst_inst_num_from_inst_to_res:         0
% 51.25/6.99  inst_dismatching_checking_time:         0.
% 51.25/6.99  
% 51.25/6.99  ------ Resolution
% 51.25/6.99  
% 51.25/6.99  res_num_of_clauses:                     39
% 51.25/6.99  res_num_in_passive:                     39
% 51.25/6.99  res_num_in_active:                      0
% 51.25/6.99  res_num_of_loops:                       138
% 51.25/6.99  res_forward_subset_subsumed:            678
% 51.25/6.99  res_backward_subset_subsumed:           42
% 51.25/6.99  res_forward_subsumed:                   0
% 51.25/6.99  res_backward_subsumed:                  0
% 51.25/6.99  res_forward_subsumption_resolution:     0
% 51.25/6.99  res_backward_subsumption_resolution:    0
% 51.25/6.99  res_clause_to_clause_subsumption:       63631
% 51.25/6.99  res_orphan_elimination:                 0
% 51.25/6.99  res_tautology_del:                      366
% 51.25/6.99  res_num_eq_res_simplified:              0
% 51.25/6.99  res_num_sel_changes:                    0
% 51.25/6.99  res_moves_from_active_to_pass:          0
% 51.25/6.99  
% 51.25/6.99  ------ Superposition
% 51.25/6.99  
% 51.25/6.99  sup_time_total:                         0.
% 51.25/6.99  sup_time_generating:                    0.
% 51.25/6.99  sup_time_sim_full:                      0.
% 51.25/6.99  sup_time_sim_immed:                     0.
% 51.25/6.99  
% 51.25/6.99  sup_num_of_clauses:                     12968
% 51.25/6.99  sup_num_in_active:                      648
% 51.25/6.99  sup_num_in_passive:                     12320
% 51.25/6.99  sup_num_of_loops:                       768
% 51.25/6.99  sup_fw_superposition:                   23890
% 51.25/6.99  sup_bw_superposition:                   12936
% 51.25/6.99  sup_immediate_simplified:               15029
% 51.25/6.99  sup_given_eliminated:                   16
% 51.25/6.99  comparisons_done:                       0
% 51.25/6.99  comparisons_avoided:                    54
% 51.25/6.99  
% 51.25/6.99  ------ Simplifications
% 51.25/6.99  
% 51.25/6.99  
% 51.25/6.99  sim_fw_subset_subsumed:                 427
% 51.25/6.99  sim_bw_subset_subsumed:                 416
% 51.25/6.99  sim_fw_subsumed:                        1224
% 51.25/6.99  sim_bw_subsumed:                        76
% 51.25/6.99  sim_fw_subsumption_res:                 6
% 51.25/6.99  sim_bw_subsumption_res:                 0
% 51.25/6.99  sim_tautology_del:                      95
% 51.25/6.99  sim_eq_tautology_del:                   2436
% 51.25/6.99  sim_eq_res_simp:                        1
% 51.25/6.99  sim_fw_demodulated:                     7387
% 51.25/6.99  sim_bw_demodulated:                     903
% 51.25/6.99  sim_light_normalised:                   7521
% 51.25/6.99  sim_joinable_taut:                      0
% 51.25/6.99  sim_joinable_simp:                      0
% 51.25/6.99  sim_ac_normalised:                      0
% 51.25/6.99  sim_smt_subsumption:                    0
% 51.25/6.99  
%------------------------------------------------------------------------------
