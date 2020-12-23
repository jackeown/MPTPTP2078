%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:35 EST 2020

% Result     : Theorem 7.32s
% Output     : CNFRefutation 7.32s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 335 expanded)
%              Number of clauses        :   75 ( 146 expanded)
%              Number of leaves         :   18 (  90 expanded)
%              Depth                    :   22
%              Number of atoms          :  297 ( 931 expanded)
%              Number of equality atoms :   42 ( 102 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,sK2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),sK1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),k2_pre_topc(X0,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f24,f23,f22])).

fof(f39,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f31])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f27,f31])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f31])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_147,negated_conjecture,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_166,plain,
    ( ~ m1_subset_1(X0_40,X0_43)
    | m1_subset_1(X1_40,X1_43)
    | X1_43 != X0_43
    | X1_40 != X0_40 ),
    theory(equality)).

cnf(c_157,plain,
    ( X0_40 = X0_40 ),
    theory(equality)).

cnf(c_1760,plain,
    ( ~ m1_subset_1(X0_40,X0_43)
    | m1_subset_1(X0_40,X1_43)
    | X1_43 != X0_43 ),
    inference(resolution,[status(thm)],[c_166,c_157])).

cnf(c_165,plain,
    ( k1_zfmisc_1(X0_40) = k1_zfmisc_1(X1_40)
    | X0_40 != X1_40 ),
    theory(equality)).

cnf(c_1775,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
    | m1_subset_1(X0_40,k1_zfmisc_1(X2_40))
    | X2_40 != X1_40 ),
    inference(resolution,[status(thm)],[c_1760,c_165])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_82,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_83,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_82])).

cnf(c_103,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_83])).

cnf(c_143,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | k9_subset_1(X1_40,X2_40,X0_40) = k1_setfam_1(k2_tarski(X2_40,X0_40)) ),
    inference(subtyping,[status(esa)],[c_103])).

cnf(c_1785,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(k9_subset_1(X1_40,X2_40,X3_40)))
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(k1_setfam_1(k2_tarski(X2_40,X3_40))))
    | ~ r1_tarski(X3_40,X1_40) ),
    inference(resolution,[status(thm)],[c_1775,c_143])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_150,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
    | r1_tarski(X0_40,X1_40) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_15985,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(k1_setfam_1(k2_tarski(X1_40,X2_40))))
    | ~ r1_tarski(X2_40,X3_40)
    | r1_tarski(X0_40,k9_subset_1(X3_40,X1_40,X2_40)) ),
    inference(resolution,[status(thm)],[c_1785,c_150])).

cnf(c_151,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
    | ~ r1_tarski(X0_40,X1_40) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_17232,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | r1_tarski(X2_40,k9_subset_1(X1_40,X3_40,X0_40))
    | ~ r1_tarski(X2_40,k1_setfam_1(k2_tarski(X3_40,X0_40))) ),
    inference(resolution,[status(thm)],[c_15985,c_151])).

cnf(c_17346,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))))
    | ~ r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[status(thm)],[c_147,c_17232])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_153,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | ~ r1_tarski(X0_40,X2_40)
    | r1_tarski(X0_40,k1_setfam_1(k2_tarski(X1_40,X2_40))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_17354,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k2_pre_topc(sK0,sK2))
    | ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[status(thm)],[c_17346,c_153])).

cnf(c_12,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_175,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_157])).

cnf(c_578,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_150])).

cnf(c_581,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_150])).

cnf(c_677,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | k9_subset_1(u1_struct_0(sK0),X0_40,sK2) = k1_setfam_1(k2_tarski(X0_40,sK2)) ),
    inference(instantiation,[status(thm)],[c_143])).

cnf(c_685,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_677])).

cnf(c_858,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_157])).

cnf(c_163,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | r1_tarski(X2_40,X3_40)
    | X2_40 != X0_40
    | X3_40 != X1_40 ),
    theory(equality)).

cnf(c_631,plain,
    ( r1_tarski(X0_40,X1_40)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(X2_40,X3_40)),X2_40)
    | X1_40 != X2_40
    | X0_40 != k1_setfam_1(k2_tarski(X2_40,X3_40)) ),
    inference(instantiation,[status(thm)],[c_163])).

cnf(c_1002,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X0_40,sK2),X1_40)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(X0_40,sK2)),X0_40)
    | X1_40 != X0_40
    | k9_subset_1(u1_struct_0(sK0),X0_40,sK2) != k1_setfam_1(k2_tarski(X0_40,sK2)) ),
    inference(instantiation,[status(thm)],[c_631])).

cnf(c_1004,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1)
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1002])).

cnf(c_1,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_154,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0_40,X1_40)),X0_40) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1463,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0_40,sK2)),X0_40) ),
    inference(instantiation,[status(thm)],[c_154])).

cnf(c_1465,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) ),
    inference(instantiation,[status(thm)],[c_1463])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_148,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ m1_subset_1(X1_40,k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ r1_tarski(X0_40,X1_40)
    | r1_tarski(k2_pre_topc(X0_42,X0_40),k2_pre_topc(X0_42,X1_40))
    | ~ l1_pre_topc(X0_42) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2314,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1_40,sK2),k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),X1_40,sK2),X0_40)
    | r1_tarski(k2_pre_topc(X0_42,k9_subset_1(u1_struct_0(sK0),X1_40,sK2)),k2_pre_topc(X0_42,X0_40))
    | ~ l1_pre_topc(X0_42) ),
    inference(instantiation,[status(thm)],[c_148])).

cnf(c_2336,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2314])).

cnf(c_816,plain,
    ( r1_tarski(X0_40,X1_40)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,X2_40)),u1_struct_0(sK0))
    | X1_40 != u1_struct_0(sK0)
    | X0_40 != k1_setfam_1(k2_tarski(sK1,X2_40)) ),
    inference(instantiation,[status(thm)],[c_163])).

cnf(c_1456,plain,
    ( r1_tarski(X0_40,u1_struct_0(sK0))
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,X1_40)),u1_struct_0(sK0))
    | X0_40 != k1_setfam_1(k2_tarski(sK1,X1_40))
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_816])).

cnf(c_2804,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2))
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1456])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_155,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | r1_tarski(k1_setfam_1(k2_tarski(X0_40,X2_40)),X1_40) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_704,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,X0_40)),u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_155])).

cnf(c_4748,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_704])).

cnf(c_2192,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_40,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_151])).

cnf(c_10949,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0_40,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),X0_40,sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_2192])).

cnf(c_10958,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_10949])).

cnf(c_17913,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k2_pre_topc(sK0,sK2))
    | ~ r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17354,c_12,c_11,c_10,c_175,c_578,c_581,c_685,c_858,c_1004,c_1465,c_2336,c_2804,c_4748,c_10958])).

cnf(c_17929,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2)
    | ~ r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_17913,c_148])).

cnf(c_17932,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17929,c_12,c_11,c_10,c_578,c_581,c_685,c_858,c_2804,c_4748,c_10958])).

cnf(c_17933,plain,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2)
    | ~ r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0)) ),
    inference(renaming,[status(thm)],[c_17932])).

cnf(c_1441,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | r1_tarski(X2_40,X1_40)
    | X2_40 != X0_40 ),
    inference(resolution,[status(thm)],[c_163,c_157])).

cnf(c_1587,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | r1_tarski(k9_subset_1(X1_40,X2_40,X0_40),X3_40)
    | ~ r1_tarski(k1_setfam_1(k2_tarski(X2_40,X0_40)),X3_40) ),
    inference(resolution,[status(thm)],[c_1441,c_143])).

cnf(c_18510,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2)
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[status(thm)],[c_17933,c_1587])).

cnf(c_18513,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2)
    | ~ r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18510,c_10,c_578])).

cnf(c_18514,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) ),
    inference(renaming,[status(thm)],[c_18513])).

cnf(c_3,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_152,plain,
    ( k2_tarski(X0_40,X1_40) = k2_tarski(X1_40,X0_40) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_162,plain,
    ( X0_41 != X1_41
    | k1_setfam_1(X0_41) = k1_setfam_1(X1_41) ),
    theory(equality)).

cnf(c_1592,plain,
    ( ~ r1_tarski(k1_setfam_1(X0_41),X0_40)
    | r1_tarski(k1_setfam_1(X1_41),X0_40)
    | X1_41 != X0_41 ),
    inference(resolution,[status(thm)],[c_1441,c_162])).

cnf(c_2404,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(X0_40,X1_40)),X2_40)
    | r1_tarski(k1_setfam_1(k2_tarski(X1_40,X0_40)),X2_40) ),
    inference(resolution,[status(thm)],[c_152,c_1592])).

cnf(c_2714,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0_40,X1_40)),X1_40) ),
    inference(resolution,[status(thm)],[c_2404,c_154])).

cnf(c_18519,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_18514,c_2714])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_149,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42)))
    | m1_subset_1(k2_pre_topc(X0_42,X0_40),k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ l1_pre_topc(X0_42) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1417,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42)))
    | r1_tarski(k2_pre_topc(X0_42,X0_40),u1_struct_0(X0_42))
    | ~ l1_pre_topc(X0_42) ),
    inference(resolution,[status(thm)],[c_149,c_150])).

cnf(c_18527,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_18519,c_1417])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18527,c_10,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:27:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.32/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.32/1.50  
% 7.32/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.32/1.50  
% 7.32/1.50  ------  iProver source info
% 7.32/1.50  
% 7.32/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.32/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.32/1.50  git: non_committed_changes: false
% 7.32/1.50  git: last_make_outside_of_git: false
% 7.32/1.50  
% 7.32/1.50  ------ 
% 7.32/1.50  ------ Parsing...
% 7.32/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.32/1.50  
% 7.32/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.32/1.50  
% 7.32/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.32/1.50  
% 7.32/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.32/1.50  ------ Proving...
% 7.32/1.50  ------ Problem Properties 
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  clauses                                 13
% 7.32/1.50  conjectures                             4
% 7.32/1.50  EPR                                     1
% 7.32/1.50  Horn                                    13
% 7.32/1.50  unary                                   6
% 7.32/1.50  binary                                  4
% 7.32/1.50  lits                                    25
% 7.32/1.50  lits eq                                 2
% 7.32/1.50  fd_pure                                 0
% 7.32/1.50  fd_pseudo                               0
% 7.32/1.50  fd_cond                                 0
% 7.32/1.50  fd_pseudo_cond                          0
% 7.32/1.50  AC symbols                              0
% 7.32/1.50  
% 7.32/1.50  ------ Input Options Time Limit: Unbounded
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  ------ 
% 7.32/1.50  Current options:
% 7.32/1.50  ------ 
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  ------ Proving...
% 7.32/1.50  
% 7.32/1.50  
% 7.32/1.50  % SZS status Theorem for theBenchmark.p
% 7.32/1.50  
% 7.32/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.32/1.50  
% 7.32/1.50  fof(f10,conjecture,(
% 7.32/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 7.32/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.50  
% 7.32/1.50  fof(f11,negated_conjecture,(
% 7.32/1.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 7.32/1.50    inference(negated_conjecture,[],[f10])).
% 7.32/1.50  
% 7.32/1.50  fof(f20,plain,(
% 7.32/1.50    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.32/1.50    inference(ennf_transformation,[],[f11])).
% 7.32/1.50  
% 7.32/1.50  fof(f24,plain,(
% 7.32/1.50    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,sK2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.32/1.50    introduced(choice_axiom,[])).
% 7.32/1.50  
% 7.32/1.50  fof(f23,plain,(
% 7.32/1.50    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),sK1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,sK1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.32/1.51    introduced(choice_axiom,[])).
% 7.32/1.51  
% 7.32/1.51  fof(f22,plain,(
% 7.32/1.51    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 7.32/1.51    introduced(choice_axiom,[])).
% 7.32/1.51  
% 7.32/1.51  fof(f25,plain,(
% 7.32/1.51    ((~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 7.32/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f24,f23,f22])).
% 7.32/1.51  
% 7.32/1.51  fof(f39,plain,(
% 7.32/1.51    ~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),
% 7.32/1.51    inference(cnf_transformation,[],[f25])).
% 7.32/1.51  
% 7.32/1.51  fof(f5,axiom,(
% 7.32/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.32/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f15,plain,(
% 7.32/1.51    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.32/1.51    inference(ennf_transformation,[],[f5])).
% 7.32/1.51  
% 7.32/1.51  fof(f30,plain,(
% 7.32/1.51    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.32/1.51    inference(cnf_transformation,[],[f15])).
% 7.32/1.51  
% 7.32/1.51  fof(f6,axiom,(
% 7.32/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.32/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f31,plain,(
% 7.32/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.32/1.51    inference(cnf_transformation,[],[f6])).
% 7.32/1.51  
% 7.32/1.51  fof(f43,plain,(
% 7.32/1.51    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.32/1.51    inference(definition_unfolding,[],[f30,f31])).
% 7.32/1.51  
% 7.32/1.51  fof(f7,axiom,(
% 7.32/1.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.32/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f21,plain,(
% 7.32/1.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.32/1.51    inference(nnf_transformation,[],[f7])).
% 7.32/1.51  
% 7.32/1.51  fof(f33,plain,(
% 7.32/1.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f21])).
% 7.32/1.51  
% 7.32/1.51  fof(f32,plain,(
% 7.32/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.32/1.51    inference(cnf_transformation,[],[f21])).
% 7.32/1.51  
% 7.32/1.51  fof(f3,axiom,(
% 7.32/1.51    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 7.32/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f13,plain,(
% 7.32/1.51    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 7.32/1.51    inference(ennf_transformation,[],[f3])).
% 7.32/1.51  
% 7.32/1.51  fof(f14,plain,(
% 7.32/1.51    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 7.32/1.51    inference(flattening,[],[f13])).
% 7.32/1.51  
% 7.32/1.51  fof(f28,plain,(
% 7.32/1.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f14])).
% 7.32/1.51  
% 7.32/1.51  fof(f42,plain,(
% 7.32/1.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 7.32/1.51    inference(definition_unfolding,[],[f28,f31])).
% 7.32/1.51  
% 7.32/1.51  fof(f36,plain,(
% 7.32/1.51    l1_pre_topc(sK0)),
% 7.32/1.51    inference(cnf_transformation,[],[f25])).
% 7.32/1.51  
% 7.32/1.51  fof(f37,plain,(
% 7.32/1.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.32/1.51    inference(cnf_transformation,[],[f25])).
% 7.32/1.51  
% 7.32/1.51  fof(f38,plain,(
% 7.32/1.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.32/1.51    inference(cnf_transformation,[],[f25])).
% 7.32/1.51  
% 7.32/1.51  fof(f2,axiom,(
% 7.32/1.51    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 7.32/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f27,plain,(
% 7.32/1.51    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f2])).
% 7.32/1.51  
% 7.32/1.51  fof(f41,plain,(
% 7.32/1.51    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 7.32/1.51    inference(definition_unfolding,[],[f27,f31])).
% 7.32/1.51  
% 7.32/1.51  fof(f9,axiom,(
% 7.32/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 7.32/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f18,plain,(
% 7.32/1.51    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.32/1.51    inference(ennf_transformation,[],[f9])).
% 7.32/1.51  
% 7.32/1.51  fof(f19,plain,(
% 7.32/1.51    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.32/1.51    inference(flattening,[],[f18])).
% 7.32/1.51  
% 7.32/1.51  fof(f35,plain,(
% 7.32/1.51    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f19])).
% 7.32/1.51  
% 7.32/1.51  fof(f1,axiom,(
% 7.32/1.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 7.32/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f12,plain,(
% 7.32/1.51    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 7.32/1.51    inference(ennf_transformation,[],[f1])).
% 7.32/1.51  
% 7.32/1.51  fof(f26,plain,(
% 7.32/1.51    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f12])).
% 7.32/1.51  
% 7.32/1.51  fof(f40,plain,(
% 7.32/1.51    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) | ~r1_tarski(X0,X1)) )),
% 7.32/1.51    inference(definition_unfolding,[],[f26,f31])).
% 7.32/1.51  
% 7.32/1.51  fof(f4,axiom,(
% 7.32/1.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.32/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f29,plain,(
% 7.32/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f4])).
% 7.32/1.51  
% 7.32/1.51  fof(f8,axiom,(
% 7.32/1.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.32/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.32/1.51  
% 7.32/1.51  fof(f16,plain,(
% 7.32/1.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.32/1.51    inference(ennf_transformation,[],[f8])).
% 7.32/1.51  
% 7.32/1.51  fof(f17,plain,(
% 7.32/1.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.32/1.51    inference(flattening,[],[f16])).
% 7.32/1.51  
% 7.32/1.51  fof(f34,plain,(
% 7.32/1.51    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.32/1.51    inference(cnf_transformation,[],[f17])).
% 7.32/1.51  
% 7.32/1.51  cnf(c_9,negated_conjecture,
% 7.32/1.51      ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
% 7.32/1.51      inference(cnf_transformation,[],[f39]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_147,negated_conjecture,
% 7.32/1.51      ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
% 7.32/1.51      inference(subtyping,[status(esa)],[c_9]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_166,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0_40,X0_43)
% 7.32/1.51      | m1_subset_1(X1_40,X1_43)
% 7.32/1.51      | X1_43 != X0_43
% 7.32/1.51      | X1_40 != X0_40 ),
% 7.32/1.51      theory(equality) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_157,plain,( X0_40 = X0_40 ),theory(equality) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1760,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0_40,X0_43)
% 7.32/1.51      | m1_subset_1(X0_40,X1_43)
% 7.32/1.51      | X1_43 != X0_43 ),
% 7.32/1.51      inference(resolution,[status(thm)],[c_166,c_157]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_165,plain,
% 7.32/1.51      ( k1_zfmisc_1(X0_40) = k1_zfmisc_1(X1_40) | X0_40 != X1_40 ),
% 7.32/1.51      theory(equality) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1775,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
% 7.32/1.51      | m1_subset_1(X0_40,k1_zfmisc_1(X2_40))
% 7.32/1.51      | X2_40 != X1_40 ),
% 7.32/1.51      inference(resolution,[status(thm)],[c_1760,c_165]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_4,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.32/1.51      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 7.32/1.51      inference(cnf_transformation,[],[f43]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_5,plain,
% 7.32/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.32/1.51      inference(cnf_transformation,[],[f33]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_82,plain,
% 7.32/1.51      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.32/1.51      inference(prop_impl,[status(thm)],[c_5]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_83,plain,
% 7.32/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.32/1.51      inference(renaming,[status(thm)],[c_82]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_103,plain,
% 7.32/1.51      ( ~ r1_tarski(X0,X1)
% 7.32/1.51      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 7.32/1.51      inference(bin_hyper_res,[status(thm)],[c_4,c_83]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_143,plain,
% 7.32/1.51      ( ~ r1_tarski(X0_40,X1_40)
% 7.32/1.51      | k9_subset_1(X1_40,X2_40,X0_40) = k1_setfam_1(k2_tarski(X2_40,X0_40)) ),
% 7.32/1.51      inference(subtyping,[status(esa)],[c_103]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1785,plain,
% 7.32/1.51      ( m1_subset_1(X0_40,k1_zfmisc_1(k9_subset_1(X1_40,X2_40,X3_40)))
% 7.32/1.51      | ~ m1_subset_1(X0_40,k1_zfmisc_1(k1_setfam_1(k2_tarski(X2_40,X3_40))))
% 7.32/1.51      | ~ r1_tarski(X3_40,X1_40) ),
% 7.32/1.51      inference(resolution,[status(thm)],[c_1775,c_143]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_6,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.32/1.51      inference(cnf_transformation,[],[f32]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_150,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
% 7.32/1.51      | r1_tarski(X0_40,X1_40) ),
% 7.32/1.51      inference(subtyping,[status(esa)],[c_6]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_15985,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(k1_setfam_1(k2_tarski(X1_40,X2_40))))
% 7.32/1.51      | ~ r1_tarski(X2_40,X3_40)
% 7.32/1.51      | r1_tarski(X0_40,k9_subset_1(X3_40,X1_40,X2_40)) ),
% 7.32/1.51      inference(resolution,[status(thm)],[c_1785,c_150]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_151,plain,
% 7.32/1.51      ( m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
% 7.32/1.51      | ~ r1_tarski(X0_40,X1_40) ),
% 7.32/1.51      inference(subtyping,[status(esa)],[c_5]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_17232,plain,
% 7.32/1.51      ( ~ r1_tarski(X0_40,X1_40)
% 7.32/1.51      | r1_tarski(X2_40,k9_subset_1(X1_40,X3_40,X0_40))
% 7.32/1.51      | ~ r1_tarski(X2_40,k1_setfam_1(k2_tarski(X3_40,X0_40))) ),
% 7.32/1.51      inference(resolution,[status(thm)],[c_15985,c_151]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_17346,plain,
% 7.32/1.51      ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))))
% 7.32/1.51      | ~ r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0)) ),
% 7.32/1.51      inference(resolution,[status(thm)],[c_147,c_17232]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_2,plain,
% 7.32/1.51      ( ~ r1_tarski(X0,X1)
% 7.32/1.51      | ~ r1_tarski(X0,X2)
% 7.32/1.51      | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
% 7.32/1.51      inference(cnf_transformation,[],[f42]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_153,plain,
% 7.32/1.51      ( ~ r1_tarski(X0_40,X1_40)
% 7.32/1.51      | ~ r1_tarski(X0_40,X2_40)
% 7.32/1.51      | r1_tarski(X0_40,k1_setfam_1(k2_tarski(X1_40,X2_40))) ),
% 7.32/1.51      inference(subtyping,[status(esa)],[c_2]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_17354,plain,
% 7.32/1.51      ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k2_pre_topc(sK0,sK2))
% 7.32/1.51      | ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k2_pre_topc(sK0,sK1))
% 7.32/1.51      | ~ r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0)) ),
% 7.32/1.51      inference(resolution,[status(thm)],[c_17346,c_153]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_12,negated_conjecture,
% 7.32/1.51      ( l1_pre_topc(sK0) ),
% 7.32/1.51      inference(cnf_transformation,[],[f36]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_11,negated_conjecture,
% 7.32/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.32/1.51      inference(cnf_transformation,[],[f37]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_10,negated_conjecture,
% 7.32/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.32/1.51      inference(cnf_transformation,[],[f38]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_175,plain,
% 7.32/1.51      ( sK1 = sK1 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_157]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_578,plain,
% 7.32/1.51      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.32/1.51      | r1_tarski(sK2,u1_struct_0(sK0)) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_150]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_581,plain,
% 7.32/1.51      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.32/1.51      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_150]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_677,plain,
% 7.32/1.51      ( ~ r1_tarski(sK2,u1_struct_0(sK0))
% 7.32/1.51      | k9_subset_1(u1_struct_0(sK0),X0_40,sK2) = k1_setfam_1(k2_tarski(X0_40,sK2)) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_143]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_685,plain,
% 7.32/1.51      ( ~ r1_tarski(sK2,u1_struct_0(sK0))
% 7.32/1.51      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k1_setfam_1(k2_tarski(sK1,sK2)) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_677]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_858,plain,
% 7.32/1.51      ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_157]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_163,plain,
% 7.32/1.51      ( ~ r1_tarski(X0_40,X1_40)
% 7.32/1.51      | r1_tarski(X2_40,X3_40)
% 7.32/1.51      | X2_40 != X0_40
% 7.32/1.51      | X3_40 != X1_40 ),
% 7.32/1.51      theory(equality) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_631,plain,
% 7.32/1.51      ( r1_tarski(X0_40,X1_40)
% 7.32/1.51      | ~ r1_tarski(k1_setfam_1(k2_tarski(X2_40,X3_40)),X2_40)
% 7.32/1.51      | X1_40 != X2_40
% 7.32/1.51      | X0_40 != k1_setfam_1(k2_tarski(X2_40,X3_40)) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_163]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1002,plain,
% 7.32/1.51      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X0_40,sK2),X1_40)
% 7.32/1.51      | ~ r1_tarski(k1_setfam_1(k2_tarski(X0_40,sK2)),X0_40)
% 7.32/1.51      | X1_40 != X0_40
% 7.32/1.51      | k9_subset_1(u1_struct_0(sK0),X0_40,sK2) != k1_setfam_1(k2_tarski(X0_40,sK2)) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_631]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1004,plain,
% 7.32/1.51      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
% 7.32/1.51      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1)
% 7.32/1.51      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2))
% 7.32/1.51      | sK1 != sK1 ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_1002]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1,plain,
% 7.32/1.51      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 7.32/1.51      inference(cnf_transformation,[],[f41]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_154,plain,
% 7.32/1.51      ( r1_tarski(k1_setfam_1(k2_tarski(X0_40,X1_40)),X0_40) ),
% 7.32/1.51      inference(subtyping,[status(esa)],[c_1]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1463,plain,
% 7.32/1.51      ( r1_tarski(k1_setfam_1(k2_tarski(X0_40,sK2)),X0_40) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_154]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1465,plain,
% 7.32/1.51      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_1463]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_8,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.32/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.32/1.51      | ~ r1_tarski(X0,X2)
% 7.32/1.51      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 7.32/1.51      | ~ l1_pre_topc(X1) ),
% 7.32/1.51      inference(cnf_transformation,[],[f35]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_148,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42)))
% 7.32/1.51      | ~ m1_subset_1(X1_40,k1_zfmisc_1(u1_struct_0(X0_42)))
% 7.32/1.51      | ~ r1_tarski(X0_40,X1_40)
% 7.32/1.51      | r1_tarski(k2_pre_topc(X0_42,X0_40),k2_pre_topc(X0_42,X1_40))
% 7.32/1.51      | ~ l1_pre_topc(X0_42) ),
% 7.32/1.51      inference(subtyping,[status(esa)],[c_8]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_2314,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42)))
% 7.32/1.51      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1_40,sK2),k1_zfmisc_1(u1_struct_0(X0_42)))
% 7.32/1.51      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),X1_40,sK2),X0_40)
% 7.32/1.51      | r1_tarski(k2_pre_topc(X0_42,k9_subset_1(u1_struct_0(sK0),X1_40,sK2)),k2_pre_topc(X0_42,X0_40))
% 7.32/1.51      | ~ l1_pre_topc(X0_42) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_148]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_2336,plain,
% 7.32/1.51      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.32/1.51      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.32/1.51      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
% 7.32/1.51      | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k2_pre_topc(sK0,sK1))
% 7.32/1.51      | ~ l1_pre_topc(sK0) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_2314]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_816,plain,
% 7.32/1.51      ( r1_tarski(X0_40,X1_40)
% 7.32/1.51      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,X2_40)),u1_struct_0(sK0))
% 7.32/1.51      | X1_40 != u1_struct_0(sK0)
% 7.32/1.51      | X0_40 != k1_setfam_1(k2_tarski(sK1,X2_40)) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_163]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1456,plain,
% 7.32/1.51      ( r1_tarski(X0_40,u1_struct_0(sK0))
% 7.32/1.51      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,X1_40)),u1_struct_0(sK0))
% 7.32/1.51      | X0_40 != k1_setfam_1(k2_tarski(sK1,X1_40))
% 7.32/1.51      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_816]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_2804,plain,
% 7.32/1.51      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0))
% 7.32/1.51      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0))
% 7.32/1.51      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2))
% 7.32/1.51      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_1456]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_0,plain,
% 7.32/1.51      ( ~ r1_tarski(X0,X1)
% 7.32/1.51      | r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) ),
% 7.32/1.51      inference(cnf_transformation,[],[f40]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_155,plain,
% 7.32/1.51      ( ~ r1_tarski(X0_40,X1_40)
% 7.32/1.51      | r1_tarski(k1_setfam_1(k2_tarski(X0_40,X2_40)),X1_40) ),
% 7.32/1.51      inference(subtyping,[status(esa)],[c_0]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_704,plain,
% 7.32/1.51      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,X0_40)),u1_struct_0(sK0))
% 7.32/1.51      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_155]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_4748,plain,
% 7.32/1.51      ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0))
% 7.32/1.51      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_704]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_2192,plain,
% 7.32/1.51      ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.32/1.51      | ~ r1_tarski(X0_40,u1_struct_0(sK0)) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_151]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_10949,plain,
% 7.32/1.51      ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0_40,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.32/1.51      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),X0_40,sK2),u1_struct_0(sK0)) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_2192]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_10958,plain,
% 7.32/1.51      ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.32/1.51      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0)) ),
% 7.32/1.51      inference(instantiation,[status(thm)],[c_10949]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_17913,plain,
% 7.32/1.51      ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k2_pre_topc(sK0,sK2))
% 7.32/1.51      | ~ r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0)) ),
% 7.32/1.51      inference(global_propositional_subsumption,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_17354,c_12,c_11,c_10,c_175,c_578,c_581,c_685,c_858,
% 7.32/1.51                 c_1004,c_1465,c_2336,c_2804,c_4748,c_10958]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_17929,plain,
% 7.32/1.51      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.32/1.51      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.32/1.51      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2)
% 7.32/1.51      | ~ r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0))
% 7.32/1.51      | ~ l1_pre_topc(sK0) ),
% 7.32/1.51      inference(resolution,[status(thm)],[c_17913,c_148]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_17932,plain,
% 7.32/1.51      ( ~ r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0))
% 7.32/1.51      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2) ),
% 7.32/1.51      inference(global_propositional_subsumption,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_17929,c_12,c_11,c_10,c_578,c_581,c_685,c_858,c_2804,
% 7.32/1.51                 c_4748,c_10958]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_17933,plain,
% 7.32/1.51      ( ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK2)
% 7.32/1.51      | ~ r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0)) ),
% 7.32/1.51      inference(renaming,[status(thm)],[c_17932]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1441,plain,
% 7.32/1.51      ( ~ r1_tarski(X0_40,X1_40)
% 7.32/1.51      | r1_tarski(X2_40,X1_40)
% 7.32/1.51      | X2_40 != X0_40 ),
% 7.32/1.51      inference(resolution,[status(thm)],[c_163,c_157]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1587,plain,
% 7.32/1.51      ( ~ r1_tarski(X0_40,X1_40)
% 7.32/1.51      | r1_tarski(k9_subset_1(X1_40,X2_40,X0_40),X3_40)
% 7.32/1.51      | ~ r1_tarski(k1_setfam_1(k2_tarski(X2_40,X0_40)),X3_40) ),
% 7.32/1.51      inference(resolution,[status(thm)],[c_1441,c_143]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_18510,plain,
% 7.32/1.51      ( ~ r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0))
% 7.32/1.51      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2)
% 7.32/1.51      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 7.32/1.51      inference(resolution,[status(thm)],[c_17933,c_1587]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_18513,plain,
% 7.32/1.51      ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2)
% 7.32/1.51      | ~ r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0)) ),
% 7.32/1.51      inference(global_propositional_subsumption,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_18510,c_10,c_578]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_18514,plain,
% 7.32/1.51      ( ~ r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0))
% 7.32/1.51      | ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) ),
% 7.32/1.51      inference(renaming,[status(thm)],[c_18513]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_3,plain,
% 7.32/1.51      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 7.32/1.51      inference(cnf_transformation,[],[f29]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_152,plain,
% 7.32/1.51      ( k2_tarski(X0_40,X1_40) = k2_tarski(X1_40,X0_40) ),
% 7.32/1.51      inference(subtyping,[status(esa)],[c_3]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_162,plain,
% 7.32/1.51      ( X0_41 != X1_41 | k1_setfam_1(X0_41) = k1_setfam_1(X1_41) ),
% 7.32/1.51      theory(equality) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1592,plain,
% 7.32/1.51      ( ~ r1_tarski(k1_setfam_1(X0_41),X0_40)
% 7.32/1.51      | r1_tarski(k1_setfam_1(X1_41),X0_40)
% 7.32/1.51      | X1_41 != X0_41 ),
% 7.32/1.51      inference(resolution,[status(thm)],[c_1441,c_162]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_2404,plain,
% 7.32/1.51      ( ~ r1_tarski(k1_setfam_1(k2_tarski(X0_40,X1_40)),X2_40)
% 7.32/1.51      | r1_tarski(k1_setfam_1(k2_tarski(X1_40,X0_40)),X2_40) ),
% 7.32/1.51      inference(resolution,[status(thm)],[c_152,c_1592]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_2714,plain,
% 7.32/1.51      ( r1_tarski(k1_setfam_1(k2_tarski(X0_40,X1_40)),X1_40) ),
% 7.32/1.51      inference(resolution,[status(thm)],[c_2404,c_154]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_18519,plain,
% 7.32/1.51      ( ~ r1_tarski(k2_pre_topc(sK0,sK2),u1_struct_0(sK0)) ),
% 7.32/1.51      inference(forward_subsumption_resolution,
% 7.32/1.51                [status(thm)],
% 7.32/1.51                [c_18514,c_2714]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_7,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.32/1.51      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.32/1.51      | ~ l1_pre_topc(X1) ),
% 7.32/1.51      inference(cnf_transformation,[],[f34]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_149,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42)))
% 7.32/1.51      | m1_subset_1(k2_pre_topc(X0_42,X0_40),k1_zfmisc_1(u1_struct_0(X0_42)))
% 7.32/1.51      | ~ l1_pre_topc(X0_42) ),
% 7.32/1.51      inference(subtyping,[status(esa)],[c_7]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_1417,plain,
% 7.32/1.51      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42)))
% 7.32/1.51      | r1_tarski(k2_pre_topc(X0_42,X0_40),u1_struct_0(X0_42))
% 7.32/1.51      | ~ l1_pre_topc(X0_42) ),
% 7.32/1.51      inference(resolution,[status(thm)],[c_149,c_150]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(c_18527,plain,
% 7.32/1.51      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.32/1.51      | ~ l1_pre_topc(sK0) ),
% 7.32/1.51      inference(resolution,[status(thm)],[c_18519,c_1417]) ).
% 7.32/1.51  
% 7.32/1.51  cnf(contradiction,plain,
% 7.32/1.51      ( $false ),
% 7.32/1.51      inference(minisat,[status(thm)],[c_18527,c_10,c_12]) ).
% 7.32/1.51  
% 7.32/1.51  
% 7.32/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.32/1.51  
% 7.32/1.51  ------                               Statistics
% 7.32/1.51  
% 7.32/1.51  ------ Selected
% 7.32/1.51  
% 7.32/1.51  total_time:                             0.616
% 7.32/1.51  
%------------------------------------------------------------------------------
