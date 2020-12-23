%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:25 EST 2020

% Result     : Theorem 0.92s
% Output     : CNFRefutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :   65 (  97 expanded)
%              Number of clauses        :   37 (  37 expanded)
%              Number of leaves         :   13 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  196 ( 392 expanded)
%              Number of equality atoms :   35 (  35 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v1_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v1_tops_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v1_tops_2(X1,X0)
               => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( v1_tops_2(X1,X0)
                 => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
          & v1_tops_2(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2),X0)
        & v1_tops_2(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v1_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ? [X2] :
            ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK1,X2),X0)
            & v1_tops_2(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
                & v1_tops_2(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0)
              & v1_tops_2(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    & v1_tops_2(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17,f16,f15])).

fof(f25,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f29,plain,(
    ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_223,plain,
    ( ~ v1_tops_2(X0_41,X0_42)
    | v1_tops_2(X1_41,X0_42)
    | X1_41 != X0_41 ),
    theory(equality)).

cnf(c_435,plain,
    ( ~ v1_tops_2(X0_41,sK0)
    | v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) != X0_41 ),
    inference(instantiation,[status(thm)],[c_223])).

cnf(c_752,plain,
    ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | ~ v1_tops_2(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)
    | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_218,plain,
    ( X0_41 != X1_41
    | X2_41 != X1_41
    | X2_41 = X0_41 ),
    theory(equality)).

cnf(c_518,plain,
    ( X0_41 != X1_41
    | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) != X1_41
    | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = X0_41 ),
    inference(instantiation,[status(thm)],[c_218])).

cnf(c_584,plain,
    ( X0_41 != k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)
    | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = X0_41
    | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) != k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_518])).

cnf(c_741,plain,
    ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) != k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)
    | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_584])).

cnf(c_0,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_4,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_103,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | X0 != X3
    | k4_xboole_0(X3,X4) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_104,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(k4_xboole_0(X0,X2),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(k4_xboole_0(X0,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_103])).

cnf(c_9,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_130,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(k4_xboole_0(X0,X2),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(k4_xboole_0(X0,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_104,c_9])).

cnf(c_131,plain,
    ( ~ v1_tops_2(X0,sK0)
    | v1_tops_2(k4_xboole_0(X0,X1),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_130])).

cnf(c_207,plain,
    ( ~ v1_tops_2(X0_41,sK0)
    | v1_tops_2(k4_xboole_0(X0_41,X1_41),sK0)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(k4_xboole_0(X0_41,X1_41),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subtyping,[status(esa)],[c_131])).

cnf(c_672,plain,
    ( ~ v1_tops_2(X0_41,sK0)
    | v1_tops_2(k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK2)),sK0)
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(instantiation,[status(thm)],[c_207])).

cnf(c_674,plain,
    ( v1_tops_2(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)
    | ~ v1_tops_2(sK1,sK0)
    | ~ m1_subset_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_221,plain,
    ( ~ m1_subset_1(X0_41,X0_43)
    | m1_subset_1(X1_41,X0_43)
    | X1_41 != X0_41 ),
    theory(equality)).

cnf(c_491,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | m1_subset_1(X1_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | X1_41 != X0_41 ),
    inference(instantiation,[status(thm)],[c_221])).

cnf(c_535,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | m1_subset_1(k4_xboole_0(X1_41,X2_41),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k4_xboole_0(X1_41,X2_41) != X0_41 ),
    inference(instantiation,[status(thm)],[c_491])).

cnf(c_608,plain,
    ( ~ m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | m1_subset_1(k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK2)) != k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK2) ),
    inference(instantiation,[status(thm)],[c_535])).

cnf(c_610,plain,
    ( ~ m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | m1_subset_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_608])).

cnf(c_216,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_585,plain,
    ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_216])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_213,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
    | k4_xboole_0(X1_41,k4_xboole_0(X1_41,X0_41)) = k9_subset_1(X0_43,X1_41,X0_41) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_440,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK2)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK2) ),
    inference(instantiation,[status(thm)],[c_213])).

cnf(c_442,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_440])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_214,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
    | m1_subset_1(k9_subset_1(X0_43,X1_41,X0_41),k1_zfmisc_1(X0_43)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_419,plain,
    ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(c_421,plain,
    ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(instantiation,[status(thm)],[c_419])).

cnf(c_5,negated_conjecture,
    ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_6,negated_conjecture,
    ( v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_8,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_752,c_741,c_674,c_610,c_585,c_442,c_421,c_5,c_6,c_7,c_8])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:46:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 0.92/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.92/1.00  
% 0.92/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.92/1.00  
% 0.92/1.00  ------  iProver source info
% 0.92/1.00  
% 0.92/1.00  git: date: 2020-06-30 10:37:57 +0100
% 0.92/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.92/1.00  git: non_committed_changes: false
% 0.92/1.00  git: last_make_outside_of_git: false
% 0.92/1.00  
% 0.92/1.00  ------ 
% 0.92/1.00  
% 0.92/1.00  ------ Input Options
% 0.92/1.00  
% 0.92/1.00  --out_options                           all
% 0.92/1.00  --tptp_safe_out                         true
% 0.92/1.00  --problem_path                          ""
% 0.92/1.00  --include_path                          ""
% 0.92/1.00  --clausifier                            res/vclausify_rel
% 0.92/1.00  --clausifier_options                    --mode clausify
% 0.92/1.00  --stdin                                 false
% 0.92/1.00  --stats_out                             all
% 0.92/1.00  
% 0.92/1.00  ------ General Options
% 0.92/1.00  
% 0.92/1.00  --fof                                   false
% 0.92/1.00  --time_out_real                         305.
% 0.92/1.00  --time_out_virtual                      -1.
% 0.92/1.00  --symbol_type_check                     false
% 0.92/1.00  --clausify_out                          false
% 0.92/1.00  --sig_cnt_out                           false
% 0.92/1.00  --trig_cnt_out                          false
% 0.92/1.00  --trig_cnt_out_tolerance                1.
% 0.92/1.00  --trig_cnt_out_sk_spl                   false
% 0.92/1.00  --abstr_cl_out                          false
% 0.92/1.00  
% 0.92/1.00  ------ Global Options
% 0.92/1.00  
% 0.92/1.00  --schedule                              default
% 0.92/1.00  --add_important_lit                     false
% 0.92/1.00  --prop_solver_per_cl                    1000
% 0.92/1.00  --min_unsat_core                        false
% 0.92/1.00  --soft_assumptions                      false
% 0.92/1.00  --soft_lemma_size                       3
% 0.92/1.00  --prop_impl_unit_size                   0
% 0.92/1.00  --prop_impl_unit                        []
% 0.92/1.00  --share_sel_clauses                     true
% 0.92/1.00  --reset_solvers                         false
% 0.92/1.00  --bc_imp_inh                            [conj_cone]
% 0.92/1.00  --conj_cone_tolerance                   3.
% 0.92/1.00  --extra_neg_conj                        none
% 0.92/1.00  --large_theory_mode                     true
% 0.92/1.00  --prolific_symb_bound                   200
% 0.92/1.00  --lt_threshold                          2000
% 0.92/1.00  --clause_weak_htbl                      true
% 0.92/1.00  --gc_record_bc_elim                     false
% 0.92/1.00  
% 0.92/1.00  ------ Preprocessing Options
% 0.92/1.00  
% 0.92/1.00  --preprocessing_flag                    true
% 0.92/1.00  --time_out_prep_mult                    0.1
% 0.92/1.00  --splitting_mode                        input
% 0.92/1.00  --splitting_grd                         true
% 0.92/1.00  --splitting_cvd                         false
% 0.92/1.00  --splitting_cvd_svl                     false
% 0.92/1.00  --splitting_nvd                         32
% 0.92/1.00  --sub_typing                            true
% 0.92/1.00  --prep_gs_sim                           true
% 0.92/1.00  --prep_unflatten                        true
% 0.92/1.00  --prep_res_sim                          true
% 0.92/1.00  --prep_upred                            true
% 0.92/1.00  --prep_sem_filter                       exhaustive
% 0.92/1.00  --prep_sem_filter_out                   false
% 0.92/1.00  --pred_elim                             true
% 0.92/1.00  --res_sim_input                         true
% 0.92/1.00  --eq_ax_congr_red                       true
% 0.92/1.00  --pure_diseq_elim                       true
% 0.92/1.00  --brand_transform                       false
% 0.92/1.00  --non_eq_to_eq                          false
% 0.92/1.00  --prep_def_merge                        true
% 0.92/1.00  --prep_def_merge_prop_impl              false
% 0.92/1.00  --prep_def_merge_mbd                    true
% 0.92/1.00  --prep_def_merge_tr_red                 false
% 0.92/1.00  --prep_def_merge_tr_cl                  false
% 0.92/1.00  --smt_preprocessing                     true
% 0.92/1.00  --smt_ac_axioms                         fast
% 0.92/1.00  --preprocessed_out                      false
% 0.92/1.00  --preprocessed_stats                    false
% 0.92/1.00  
% 0.92/1.00  ------ Abstraction refinement Options
% 0.92/1.00  
% 0.92/1.00  --abstr_ref                             []
% 0.92/1.00  --abstr_ref_prep                        false
% 0.92/1.00  --abstr_ref_until_sat                   false
% 0.92/1.00  --abstr_ref_sig_restrict                funpre
% 0.92/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 0.92/1.00  --abstr_ref_under                       []
% 0.92/1.00  
% 0.92/1.00  ------ SAT Options
% 0.92/1.00  
% 0.92/1.00  --sat_mode                              false
% 0.92/1.00  --sat_fm_restart_options                ""
% 0.92/1.00  --sat_gr_def                            false
% 0.92/1.00  --sat_epr_types                         true
% 0.92/1.00  --sat_non_cyclic_types                  false
% 0.92/1.00  --sat_finite_models                     false
% 0.92/1.00  --sat_fm_lemmas                         false
% 0.92/1.00  --sat_fm_prep                           false
% 0.92/1.00  --sat_fm_uc_incr                        true
% 0.92/1.00  --sat_out_model                         small
% 0.92/1.00  --sat_out_clauses                       false
% 0.92/1.00  
% 0.92/1.00  ------ QBF Options
% 0.92/1.00  
% 0.92/1.00  --qbf_mode                              false
% 0.92/1.00  --qbf_elim_univ                         false
% 0.92/1.00  --qbf_dom_inst                          none
% 0.92/1.00  --qbf_dom_pre_inst                      false
% 0.92/1.00  --qbf_sk_in                             false
% 0.92/1.00  --qbf_pred_elim                         true
% 0.92/1.00  --qbf_split                             512
% 0.92/1.00  
% 0.92/1.00  ------ BMC1 Options
% 0.92/1.00  
% 0.92/1.00  --bmc1_incremental                      false
% 0.92/1.00  --bmc1_axioms                           reachable_all
% 0.92/1.00  --bmc1_min_bound                        0
% 0.92/1.00  --bmc1_max_bound                        -1
% 0.92/1.00  --bmc1_max_bound_default                -1
% 0.92/1.00  --bmc1_symbol_reachability              true
% 0.92/1.00  --bmc1_property_lemmas                  false
% 0.92/1.00  --bmc1_k_induction                      false
% 0.92/1.00  --bmc1_non_equiv_states                 false
% 0.92/1.00  --bmc1_deadlock                         false
% 0.92/1.00  --bmc1_ucm                              false
% 0.92/1.00  --bmc1_add_unsat_core                   none
% 0.92/1.00  --bmc1_unsat_core_children              false
% 0.92/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 0.92/1.00  --bmc1_out_stat                         full
% 0.92/1.00  --bmc1_ground_init                      false
% 0.92/1.00  --bmc1_pre_inst_next_state              false
% 0.92/1.00  --bmc1_pre_inst_state                   false
% 0.92/1.00  --bmc1_pre_inst_reach_state             false
% 0.92/1.00  --bmc1_out_unsat_core                   false
% 0.92/1.00  --bmc1_aig_witness_out                  false
% 0.92/1.00  --bmc1_verbose                          false
% 0.92/1.00  --bmc1_dump_clauses_tptp                false
% 0.92/1.00  --bmc1_dump_unsat_core_tptp             false
% 0.92/1.00  --bmc1_dump_file                        -
% 0.92/1.00  --bmc1_ucm_expand_uc_limit              128
% 0.92/1.00  --bmc1_ucm_n_expand_iterations          6
% 0.92/1.00  --bmc1_ucm_extend_mode                  1
% 0.92/1.00  --bmc1_ucm_init_mode                    2
% 0.92/1.00  --bmc1_ucm_cone_mode                    none
% 0.92/1.00  --bmc1_ucm_reduced_relation_type        0
% 0.92/1.00  --bmc1_ucm_relax_model                  4
% 0.92/1.00  --bmc1_ucm_full_tr_after_sat            true
% 0.92/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 0.92/1.00  --bmc1_ucm_layered_model                none
% 0.92/1.00  --bmc1_ucm_max_lemma_size               10
% 0.92/1.00  
% 0.92/1.00  ------ AIG Options
% 0.92/1.00  
% 0.92/1.00  --aig_mode                              false
% 0.92/1.00  
% 0.92/1.00  ------ Instantiation Options
% 0.92/1.00  
% 0.92/1.00  --instantiation_flag                    true
% 0.92/1.00  --inst_sos_flag                         false
% 0.92/1.00  --inst_sos_phase                        true
% 0.92/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.92/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.92/1.00  --inst_lit_sel_side                     num_symb
% 0.92/1.00  --inst_solver_per_active                1400
% 0.92/1.00  --inst_solver_calls_frac                1.
% 0.92/1.00  --inst_passive_queue_type               priority_queues
% 0.92/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.92/1.00  --inst_passive_queues_freq              [25;2]
% 0.92/1.00  --inst_dismatching                      true
% 0.92/1.00  --inst_eager_unprocessed_to_passive     true
% 0.92/1.00  --inst_prop_sim_given                   true
% 0.92/1.00  --inst_prop_sim_new                     false
% 0.92/1.00  --inst_subs_new                         false
% 0.92/1.00  --inst_eq_res_simp                      false
% 0.92/1.00  --inst_subs_given                       false
% 0.92/1.00  --inst_orphan_elimination               true
% 0.92/1.00  --inst_learning_loop_flag               true
% 0.92/1.00  --inst_learning_start                   3000
% 0.92/1.00  --inst_learning_factor                  2
% 0.92/1.00  --inst_start_prop_sim_after_learn       3
% 0.92/1.00  --inst_sel_renew                        solver
% 0.92/1.00  --inst_lit_activity_flag                true
% 0.92/1.00  --inst_restr_to_given                   false
% 0.92/1.00  --inst_activity_threshold               500
% 0.92/1.00  --inst_out_proof                        true
% 0.92/1.00  
% 0.92/1.00  ------ Resolution Options
% 0.92/1.00  
% 0.92/1.00  --resolution_flag                       true
% 0.92/1.00  --res_lit_sel                           adaptive
% 0.92/1.00  --res_lit_sel_side                      none
% 0.92/1.00  --res_ordering                          kbo
% 0.92/1.00  --res_to_prop_solver                    active
% 0.92/1.00  --res_prop_simpl_new                    false
% 0.92/1.00  --res_prop_simpl_given                  true
% 0.92/1.00  --res_passive_queue_type                priority_queues
% 0.92/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.92/1.00  --res_passive_queues_freq               [15;5]
% 0.92/1.00  --res_forward_subs                      full
% 0.92/1.00  --res_backward_subs                     full
% 0.92/1.00  --res_forward_subs_resolution           true
% 0.92/1.00  --res_backward_subs_resolution          true
% 0.92/1.00  --res_orphan_elimination                true
% 0.92/1.00  --res_time_limit                        2.
% 0.92/1.00  --res_out_proof                         true
% 0.92/1.00  
% 0.92/1.00  ------ Superposition Options
% 0.92/1.00  
% 0.92/1.00  --superposition_flag                    true
% 0.92/1.00  --sup_passive_queue_type                priority_queues
% 0.92/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.92/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.92/1.00  --demod_completeness_check              fast
% 0.92/1.00  --demod_use_ground                      true
% 0.92/1.00  --sup_to_prop_solver                    passive
% 0.92/1.00  --sup_prop_simpl_new                    true
% 0.92/1.00  --sup_prop_simpl_given                  true
% 0.92/1.00  --sup_fun_splitting                     false
% 0.92/1.00  --sup_smt_interval                      50000
% 0.92/1.00  
% 0.92/1.00  ------ Superposition Simplification Setup
% 0.92/1.00  
% 0.92/1.00  --sup_indices_passive                   []
% 0.92/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.92/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.92/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.92/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.92/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.92/1.00  --sup_full_bw                           [BwDemod]
% 0.92/1.00  --sup_immed_triv                        [TrivRules]
% 0.92/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.92/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.92/1.00  --sup_immed_bw_main                     []
% 0.92/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.92/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.92/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.92/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.92/1.00  
% 0.92/1.00  ------ Combination Options
% 0.92/1.00  
% 0.92/1.00  --comb_res_mult                         3
% 0.92/1.00  --comb_sup_mult                         2
% 0.92/1.00  --comb_inst_mult                        10
% 0.92/1.00  
% 0.92/1.00  ------ Debug Options
% 0.92/1.00  
% 0.92/1.00  --dbg_backtrace                         false
% 0.92/1.00  --dbg_dump_prop_clauses                 false
% 0.92/1.00  --dbg_dump_prop_clauses_file            -
% 0.92/1.00  --dbg_out_stat                          false
% 0.92/1.00  ------ Parsing...
% 0.92/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.92/1.00  
% 0.92/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 0.92/1.00  
% 0.92/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.92/1.00  
% 0.92/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.92/1.00  ------ Proving...
% 0.92/1.00  ------ Problem Properties 
% 0.92/1.00  
% 0.92/1.00  
% 0.92/1.00  clauses                                 8
% 0.92/1.00  conjectures                             4
% 0.92/1.00  EPR                                     1
% 0.92/1.00  Horn                                    8
% 0.92/1.00  unary                                   5
% 0.92/1.00  binary                                  2
% 0.92/1.00  lits                                    13
% 0.92/1.00  lits eq                                 2
% 0.92/1.00  fd_pure                                 0
% 0.92/1.00  fd_pseudo                               0
% 0.92/1.00  fd_cond                                 0
% 0.92/1.00  fd_pseudo_cond                          0
% 0.92/1.00  AC symbols                              0
% 0.92/1.00  
% 0.92/1.00  ------ Schedule dynamic 5 is on 
% 0.92/1.00  
% 0.92/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.92/1.00  
% 0.92/1.00  
% 0.92/1.00  ------ 
% 0.92/1.00  Current options:
% 0.92/1.00  ------ 
% 0.92/1.00  
% 0.92/1.00  ------ Input Options
% 0.92/1.00  
% 0.92/1.00  --out_options                           all
% 0.92/1.00  --tptp_safe_out                         true
% 0.92/1.00  --problem_path                          ""
% 0.92/1.00  --include_path                          ""
% 0.92/1.00  --clausifier                            res/vclausify_rel
% 0.92/1.00  --clausifier_options                    --mode clausify
% 0.92/1.00  --stdin                                 false
% 0.92/1.00  --stats_out                             all
% 0.92/1.00  
% 0.92/1.00  ------ General Options
% 0.92/1.00  
% 0.92/1.00  --fof                                   false
% 0.92/1.00  --time_out_real                         305.
% 0.92/1.00  --time_out_virtual                      -1.
% 0.92/1.00  --symbol_type_check                     false
% 0.92/1.00  --clausify_out                          false
% 0.92/1.00  --sig_cnt_out                           false
% 0.92/1.00  --trig_cnt_out                          false
% 0.92/1.00  --trig_cnt_out_tolerance                1.
% 0.92/1.00  --trig_cnt_out_sk_spl                   false
% 0.92/1.00  --abstr_cl_out                          false
% 0.92/1.00  
% 0.92/1.00  ------ Global Options
% 0.92/1.00  
% 0.92/1.00  --schedule                              default
% 0.92/1.00  --add_important_lit                     false
% 0.92/1.00  --prop_solver_per_cl                    1000
% 0.92/1.00  --min_unsat_core                        false
% 0.92/1.00  --soft_assumptions                      false
% 0.92/1.00  --soft_lemma_size                       3
% 0.92/1.00  --prop_impl_unit_size                   0
% 0.92/1.00  --prop_impl_unit                        []
% 0.92/1.00  --share_sel_clauses                     true
% 0.92/1.00  --reset_solvers                         false
% 0.92/1.00  --bc_imp_inh                            [conj_cone]
% 0.92/1.00  --conj_cone_tolerance                   3.
% 0.92/1.00  --extra_neg_conj                        none
% 0.92/1.00  --large_theory_mode                     true
% 0.92/1.00  --prolific_symb_bound                   200
% 0.92/1.00  --lt_threshold                          2000
% 0.92/1.00  --clause_weak_htbl                      true
% 0.92/1.00  --gc_record_bc_elim                     false
% 0.92/1.00  
% 0.92/1.00  ------ Preprocessing Options
% 0.92/1.00  
% 0.92/1.00  --preprocessing_flag                    true
% 0.92/1.00  --time_out_prep_mult                    0.1
% 0.92/1.00  --splitting_mode                        input
% 0.92/1.00  --splitting_grd                         true
% 0.92/1.00  --splitting_cvd                         false
% 0.92/1.00  --splitting_cvd_svl                     false
% 0.92/1.00  --splitting_nvd                         32
% 0.92/1.00  --sub_typing                            true
% 0.92/1.00  --prep_gs_sim                           true
% 0.92/1.00  --prep_unflatten                        true
% 0.92/1.00  --prep_res_sim                          true
% 0.92/1.00  --prep_upred                            true
% 0.92/1.00  --prep_sem_filter                       exhaustive
% 0.92/1.00  --prep_sem_filter_out                   false
% 0.92/1.00  --pred_elim                             true
% 0.92/1.00  --res_sim_input                         true
% 0.92/1.00  --eq_ax_congr_red                       true
% 0.92/1.00  --pure_diseq_elim                       true
% 0.92/1.00  --brand_transform                       false
% 0.92/1.00  --non_eq_to_eq                          false
% 0.92/1.00  --prep_def_merge                        true
% 0.92/1.00  --prep_def_merge_prop_impl              false
% 0.92/1.00  --prep_def_merge_mbd                    true
% 0.92/1.00  --prep_def_merge_tr_red                 false
% 0.92/1.00  --prep_def_merge_tr_cl                  false
% 0.92/1.00  --smt_preprocessing                     true
% 0.92/1.00  --smt_ac_axioms                         fast
% 0.92/1.00  --preprocessed_out                      false
% 0.92/1.00  --preprocessed_stats                    false
% 0.92/1.00  
% 0.92/1.00  ------ Abstraction refinement Options
% 0.92/1.00  
% 0.92/1.00  --abstr_ref                             []
% 0.92/1.00  --abstr_ref_prep                        false
% 0.92/1.00  --abstr_ref_until_sat                   false
% 0.92/1.00  --abstr_ref_sig_restrict                funpre
% 0.92/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 0.92/1.00  --abstr_ref_under                       []
% 0.92/1.00  
% 0.92/1.00  ------ SAT Options
% 0.92/1.00  
% 0.92/1.00  --sat_mode                              false
% 0.92/1.00  --sat_fm_restart_options                ""
% 0.92/1.00  --sat_gr_def                            false
% 0.92/1.00  --sat_epr_types                         true
% 0.92/1.00  --sat_non_cyclic_types                  false
% 0.92/1.00  --sat_finite_models                     false
% 0.92/1.00  --sat_fm_lemmas                         false
% 0.92/1.00  --sat_fm_prep                           false
% 0.92/1.00  --sat_fm_uc_incr                        true
% 0.92/1.00  --sat_out_model                         small
% 0.92/1.00  --sat_out_clauses                       false
% 0.92/1.00  
% 0.92/1.00  ------ QBF Options
% 0.92/1.00  
% 0.92/1.00  --qbf_mode                              false
% 0.92/1.00  --qbf_elim_univ                         false
% 0.92/1.00  --qbf_dom_inst                          none
% 0.92/1.00  --qbf_dom_pre_inst                      false
% 0.92/1.00  --qbf_sk_in                             false
% 0.92/1.00  --qbf_pred_elim                         true
% 0.92/1.00  --qbf_split                             512
% 0.92/1.00  
% 0.92/1.00  ------ BMC1 Options
% 0.92/1.00  
% 0.92/1.00  --bmc1_incremental                      false
% 0.92/1.00  --bmc1_axioms                           reachable_all
% 0.92/1.00  --bmc1_min_bound                        0
% 0.92/1.00  --bmc1_max_bound                        -1
% 0.92/1.00  --bmc1_max_bound_default                -1
% 0.92/1.00  --bmc1_symbol_reachability              true
% 0.92/1.00  --bmc1_property_lemmas                  false
% 0.92/1.00  --bmc1_k_induction                      false
% 0.92/1.00  --bmc1_non_equiv_states                 false
% 0.92/1.00  --bmc1_deadlock                         false
% 0.92/1.00  --bmc1_ucm                              false
% 0.92/1.00  --bmc1_add_unsat_core                   none
% 0.92/1.00  --bmc1_unsat_core_children              false
% 0.92/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 0.92/1.00  --bmc1_out_stat                         full
% 0.92/1.00  --bmc1_ground_init                      false
% 0.92/1.00  --bmc1_pre_inst_next_state              false
% 0.92/1.00  --bmc1_pre_inst_state                   false
% 0.92/1.00  --bmc1_pre_inst_reach_state             false
% 0.92/1.00  --bmc1_out_unsat_core                   false
% 0.92/1.00  --bmc1_aig_witness_out                  false
% 0.92/1.00  --bmc1_verbose                          false
% 0.92/1.00  --bmc1_dump_clauses_tptp                false
% 0.92/1.00  --bmc1_dump_unsat_core_tptp             false
% 0.92/1.00  --bmc1_dump_file                        -
% 0.92/1.00  --bmc1_ucm_expand_uc_limit              128
% 0.92/1.00  --bmc1_ucm_n_expand_iterations          6
% 0.92/1.00  --bmc1_ucm_extend_mode                  1
% 0.92/1.00  --bmc1_ucm_init_mode                    2
% 0.92/1.00  --bmc1_ucm_cone_mode                    none
% 0.92/1.00  --bmc1_ucm_reduced_relation_type        0
% 0.92/1.00  --bmc1_ucm_relax_model                  4
% 0.92/1.00  --bmc1_ucm_full_tr_after_sat            true
% 0.92/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 0.92/1.00  --bmc1_ucm_layered_model                none
% 0.92/1.00  --bmc1_ucm_max_lemma_size               10
% 0.92/1.00  
% 0.92/1.00  ------ AIG Options
% 0.92/1.00  
% 0.92/1.00  --aig_mode                              false
% 0.92/1.00  
% 0.92/1.00  ------ Instantiation Options
% 0.92/1.00  
% 0.92/1.00  --instantiation_flag                    true
% 0.92/1.00  --inst_sos_flag                         false
% 0.92/1.00  --inst_sos_phase                        true
% 0.92/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.92/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.92/1.00  --inst_lit_sel_side                     none
% 0.92/1.00  --inst_solver_per_active                1400
% 0.92/1.00  --inst_solver_calls_frac                1.
% 0.92/1.00  --inst_passive_queue_type               priority_queues
% 0.92/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.92/1.00  --inst_passive_queues_freq              [25;2]
% 0.92/1.00  --inst_dismatching                      true
% 0.92/1.00  --inst_eager_unprocessed_to_passive     true
% 0.92/1.00  --inst_prop_sim_given                   true
% 0.92/1.00  --inst_prop_sim_new                     false
% 0.92/1.00  --inst_subs_new                         false
% 0.92/1.00  --inst_eq_res_simp                      false
% 0.92/1.00  --inst_subs_given                       false
% 0.92/1.00  --inst_orphan_elimination               true
% 0.92/1.00  --inst_learning_loop_flag               true
% 0.92/1.00  --inst_learning_start                   3000
% 0.92/1.00  --inst_learning_factor                  2
% 0.92/1.00  --inst_start_prop_sim_after_learn       3
% 0.92/1.00  --inst_sel_renew                        solver
% 0.92/1.00  --inst_lit_activity_flag                true
% 0.92/1.00  --inst_restr_to_given                   false
% 0.92/1.00  --inst_activity_threshold               500
% 0.92/1.00  --inst_out_proof                        true
% 0.92/1.00  
% 0.92/1.00  ------ Resolution Options
% 0.92/1.00  
% 0.92/1.00  --resolution_flag                       false
% 0.92/1.00  --res_lit_sel                           adaptive
% 0.92/1.00  --res_lit_sel_side                      none
% 0.92/1.00  --res_ordering                          kbo
% 0.92/1.00  --res_to_prop_solver                    active
% 0.92/1.00  --res_prop_simpl_new                    false
% 0.92/1.00  --res_prop_simpl_given                  true
% 0.92/1.00  --res_passive_queue_type                priority_queues
% 0.92/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.92/1.00  --res_passive_queues_freq               [15;5]
% 0.92/1.00  --res_forward_subs                      full
% 0.92/1.00  --res_backward_subs                     full
% 0.92/1.00  --res_forward_subs_resolution           true
% 0.92/1.00  --res_backward_subs_resolution          true
% 0.92/1.00  --res_orphan_elimination                true
% 0.92/1.00  --res_time_limit                        2.
% 0.92/1.00  --res_out_proof                         true
% 0.92/1.00  
% 0.92/1.00  ------ Superposition Options
% 0.92/1.00  
% 0.92/1.00  --superposition_flag                    true
% 0.92/1.00  --sup_passive_queue_type                priority_queues
% 0.92/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.92/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.92/1.00  --demod_completeness_check              fast
% 0.92/1.00  --demod_use_ground                      true
% 0.92/1.00  --sup_to_prop_solver                    passive
% 0.92/1.00  --sup_prop_simpl_new                    true
% 0.92/1.00  --sup_prop_simpl_given                  true
% 0.92/1.00  --sup_fun_splitting                     false
% 0.92/1.00  --sup_smt_interval                      50000
% 0.92/1.00  
% 0.92/1.00  ------ Superposition Simplification Setup
% 0.92/1.00  
% 0.92/1.00  --sup_indices_passive                   []
% 0.92/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.92/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.92/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.92/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.92/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.92/1.00  --sup_full_bw                           [BwDemod]
% 0.92/1.00  --sup_immed_triv                        [TrivRules]
% 0.92/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.92/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.92/1.00  --sup_immed_bw_main                     []
% 0.92/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.92/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.92/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.92/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.92/1.00  
% 0.92/1.00  ------ Combination Options
% 0.92/1.00  
% 0.92/1.00  --comb_res_mult                         3
% 0.92/1.00  --comb_sup_mult                         2
% 0.92/1.00  --comb_inst_mult                        10
% 0.92/1.00  
% 0.92/1.00  ------ Debug Options
% 0.92/1.00  
% 0.92/1.00  --dbg_backtrace                         false
% 0.92/1.00  --dbg_dump_prop_clauses                 false
% 0.92/1.00  --dbg_dump_prop_clauses_file            -
% 0.92/1.00  --dbg_out_stat                          false
% 0.92/1.00  
% 0.92/1.00  
% 0.92/1.00  
% 0.92/1.00  
% 0.92/1.00  ------ Proving...
% 0.92/1.00  
% 0.92/1.00  
% 0.92/1.00  % SZS status Theorem for theBenchmark.p
% 0.92/1.00  
% 0.92/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 0.92/1.00  
% 0.92/1.00  fof(f1,axiom,(
% 0.92/1.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.92/1.00  
% 0.92/1.00  fof(f19,plain,(
% 0.92/1.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.92/1.00    inference(cnf_transformation,[],[f1])).
% 0.92/1.00  
% 0.92/1.00  fof(f6,axiom,(
% 0.92/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 0.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.92/1.00  
% 0.92/1.00  fof(f11,plain,(
% 0.92/1.00    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_2(X1,X0) | (~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.92/1.00    inference(ennf_transformation,[],[f6])).
% 0.92/1.00  
% 0.92/1.00  fof(f12,plain,(
% 0.92/1.00    ! [X0] : (! [X1] : (! [X2] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.92/1.00    inference(flattening,[],[f11])).
% 0.92/1.00  
% 0.92/1.00  fof(f24,plain,(
% 0.92/1.00    ( ! [X2,X0,X1] : (v1_tops_2(X1,X0) | ~v1_tops_2(X2,X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.92/1.00    inference(cnf_transformation,[],[f12])).
% 0.92/1.00  
% 0.92/1.00  fof(f7,conjecture,(
% 0.92/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.92/1.00  
% 0.92/1.00  fof(f8,negated_conjecture,(
% 0.92/1.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.92/1.00    inference(negated_conjecture,[],[f7])).
% 0.92/1.00  
% 0.92/1.00  fof(f13,plain,(
% 0.92/1.00    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.92/1.00    inference(ennf_transformation,[],[f8])).
% 0.92/1.00  
% 0.92/1.00  fof(f14,plain,(
% 0.92/1.00    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.92/1.00    inference(flattening,[],[f13])).
% 0.92/1.00  
% 0.92/1.00  fof(f17,plain,(
% 0.92/1.00    ( ! [X0,X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2),X0) & v1_tops_2(X1,X0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 0.92/1.00    introduced(choice_axiom,[])).
% 0.92/1.00  
% 0.92/1.00  fof(f16,plain,(
% 0.92/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK1,X2),X0) & v1_tops_2(sK1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 0.92/1.00    introduced(choice_axiom,[])).
% 0.92/1.00  
% 0.92/1.00  fof(f15,plain,(
% 0.92/1.00    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v1_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2),sK0) & v1_tops_2(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.92/1.00    introduced(choice_axiom,[])).
% 0.92/1.00  
% 0.92/1.00  fof(f18,plain,(
% 0.92/1.00    ((~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) & v1_tops_2(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.92/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17,f16,f15])).
% 0.92/1.00  
% 0.92/1.00  fof(f25,plain,(
% 0.92/1.00    l1_pre_topc(sK0)),
% 0.92/1.00    inference(cnf_transformation,[],[f18])).
% 0.92/1.00  
% 0.92/1.00  fof(f4,axiom,(
% 0.92/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 0.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.92/1.00  
% 0.92/1.00  fof(f10,plain,(
% 0.92/1.00    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.92/1.00    inference(ennf_transformation,[],[f4])).
% 0.92/1.00  
% 0.92/1.00  fof(f22,plain,(
% 0.92/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.92/1.00    inference(cnf_transformation,[],[f10])).
% 0.92/1.00  
% 0.92/1.00  fof(f2,axiom,(
% 0.92/1.00    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.92/1.00  
% 0.92/1.00  fof(f20,plain,(
% 0.92/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.92/1.00    inference(cnf_transformation,[],[f2])).
% 0.92/1.00  
% 0.92/1.00  fof(f30,plain,(
% 0.92/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.92/1.00    inference(definition_unfolding,[],[f22,f20])).
% 0.92/1.00  
% 0.92/1.00  fof(f3,axiom,(
% 0.92/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.92/1.00  
% 0.92/1.00  fof(f9,plain,(
% 0.92/1.00    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.92/1.00    inference(ennf_transformation,[],[f3])).
% 0.92/1.00  
% 0.92/1.00  fof(f21,plain,(
% 0.92/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.92/1.00    inference(cnf_transformation,[],[f9])).
% 0.92/1.00  
% 0.92/1.00  fof(f29,plain,(
% 0.92/1.00    ~v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.92/1.00    inference(cnf_transformation,[],[f18])).
% 0.92/1.00  
% 0.92/1.00  fof(f28,plain,(
% 0.92/1.00    v1_tops_2(sK1,sK0)),
% 0.92/1.00    inference(cnf_transformation,[],[f18])).
% 0.92/1.00  
% 0.92/1.00  fof(f27,plain,(
% 0.92/1.00    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.92/1.00    inference(cnf_transformation,[],[f18])).
% 0.92/1.00  
% 0.92/1.00  fof(f26,plain,(
% 0.92/1.00    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.92/1.00    inference(cnf_transformation,[],[f18])).
% 0.92/1.00  
% 0.92/1.00  cnf(c_223,plain,
% 0.92/1.00      ( ~ v1_tops_2(X0_41,X0_42)
% 0.92/1.00      | v1_tops_2(X1_41,X0_42)
% 0.92/1.00      | X1_41 != X0_41 ),
% 0.92/1.00      theory(equality) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_435,plain,
% 0.92/1.00      ( ~ v1_tops_2(X0_41,sK0)
% 0.92/1.00      | v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
% 0.92/1.00      | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) != X0_41 ),
% 0.92/1.00      inference(instantiation,[status(thm)],[c_223]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_752,plain,
% 0.92/1.00      ( v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
% 0.92/1.00      | ~ v1_tops_2(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)
% 0.92/1.00      | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 0.92/1.00      inference(instantiation,[status(thm)],[c_435]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_218,plain,
% 0.92/1.00      ( X0_41 != X1_41 | X2_41 != X1_41 | X2_41 = X0_41 ),
% 0.92/1.00      theory(equality) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_518,plain,
% 0.92/1.00      ( X0_41 != X1_41
% 0.92/1.00      | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) != X1_41
% 0.92/1.00      | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = X0_41 ),
% 0.92/1.00      inference(instantiation,[status(thm)],[c_218]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_584,plain,
% 0.92/1.00      ( X0_41 != k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)
% 0.92/1.00      | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = X0_41
% 0.92/1.00      | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) != k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) ),
% 0.92/1.00      inference(instantiation,[status(thm)],[c_518]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_741,plain,
% 0.92/1.00      ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) != k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)
% 0.92/1.00      | k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
% 0.92/1.00      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) ),
% 0.92/1.00      inference(instantiation,[status(thm)],[c_584]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_0,plain,
% 0.92/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 0.92/1.00      inference(cnf_transformation,[],[f19]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_4,plain,
% 0.92/1.00      ( ~ v1_tops_2(X0,X1)
% 0.92/1.00      | v1_tops_2(X2,X1)
% 0.92/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 0.92/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 0.92/1.00      | ~ r1_tarski(X2,X0)
% 0.92/1.00      | ~ l1_pre_topc(X1) ),
% 0.92/1.00      inference(cnf_transformation,[],[f24]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_103,plain,
% 0.92/1.00      ( ~ v1_tops_2(X0,X1)
% 0.92/1.00      | v1_tops_2(X2,X1)
% 0.92/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 0.92/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 0.92/1.00      | ~ l1_pre_topc(X1)
% 0.92/1.00      | X0 != X3
% 0.92/1.00      | k4_xboole_0(X3,X4) != X2 ),
% 0.92/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_104,plain,
% 0.92/1.00      ( ~ v1_tops_2(X0,X1)
% 0.92/1.00      | v1_tops_2(k4_xboole_0(X0,X2),X1)
% 0.92/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 0.92/1.00      | ~ m1_subset_1(k4_xboole_0(X0,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 0.92/1.00      | ~ l1_pre_topc(X1) ),
% 0.92/1.00      inference(unflattening,[status(thm)],[c_103]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_9,negated_conjecture,
% 0.92/1.00      ( l1_pre_topc(sK0) ),
% 0.92/1.00      inference(cnf_transformation,[],[f25]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_130,plain,
% 0.92/1.00      ( ~ v1_tops_2(X0,X1)
% 0.92/1.00      | v1_tops_2(k4_xboole_0(X0,X2),X1)
% 0.92/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 0.92/1.00      | ~ m1_subset_1(k4_xboole_0(X0,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 0.92/1.00      | sK0 != X1 ),
% 0.92/1.00      inference(resolution_lifted,[status(thm)],[c_104,c_9]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_131,plain,
% 0.92/1.00      ( ~ v1_tops_2(X0,sK0)
% 0.92/1.00      | v1_tops_2(k4_xboole_0(X0,X1),sK0)
% 0.92/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 0.92/1.00      | ~ m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 0.92/1.00      inference(unflattening,[status(thm)],[c_130]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_207,plain,
% 0.92/1.00      ( ~ v1_tops_2(X0_41,sK0)
% 0.92/1.00      | v1_tops_2(k4_xboole_0(X0_41,X1_41),sK0)
% 0.92/1.00      | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 0.92/1.00      | ~ m1_subset_1(k4_xboole_0(X0_41,X1_41),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 0.92/1.00      inference(subtyping,[status(esa)],[c_131]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_672,plain,
% 0.92/1.00      ( ~ v1_tops_2(X0_41,sK0)
% 0.92/1.00      | v1_tops_2(k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK2)),sK0)
% 0.92/1.00      | ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 0.92/1.00      | ~ m1_subset_1(k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 0.92/1.00      inference(instantiation,[status(thm)],[c_207]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_674,plain,
% 0.92/1.00      ( v1_tops_2(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)
% 0.92/1.00      | ~ v1_tops_2(sK1,sK0)
% 0.92/1.00      | ~ m1_subset_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 0.92/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 0.92/1.00      inference(instantiation,[status(thm)],[c_672]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_221,plain,
% 0.92/1.00      ( ~ m1_subset_1(X0_41,X0_43)
% 0.92/1.00      | m1_subset_1(X1_41,X0_43)
% 0.92/1.00      | X1_41 != X0_41 ),
% 0.92/1.00      theory(equality) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_491,plain,
% 0.92/1.00      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 0.92/1.00      | m1_subset_1(X1_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 0.92/1.00      | X1_41 != X0_41 ),
% 0.92/1.00      inference(instantiation,[status(thm)],[c_221]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_535,plain,
% 0.92/1.00      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 0.92/1.00      | m1_subset_1(k4_xboole_0(X1_41,X2_41),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 0.92/1.00      | k4_xboole_0(X1_41,X2_41) != X0_41 ),
% 0.92/1.00      inference(instantiation,[status(thm)],[c_491]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_608,plain,
% 0.92/1.00      ( ~ m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 0.92/1.00      | m1_subset_1(k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 0.92/1.00      | k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK2)) != k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK2) ),
% 0.92/1.00      inference(instantiation,[status(thm)],[c_535]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_610,plain,
% 0.92/1.00      ( ~ m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 0.92/1.00      | m1_subset_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 0.92/1.00      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) ),
% 0.92/1.00      inference(instantiation,[status(thm)],[c_608]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_216,plain,( X0_41 = X0_41 ),theory(equality) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_585,plain,
% 0.92/1.00      ( k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) ),
% 0.92/1.00      inference(instantiation,[status(thm)],[c_216]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_2,plain,
% 0.92/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.92/1.00      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 0.92/1.00      inference(cnf_transformation,[],[f30]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_213,plain,
% 0.92/1.00      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
% 0.92/1.00      | k4_xboole_0(X1_41,k4_xboole_0(X1_41,X0_41)) = k9_subset_1(X0_43,X1_41,X0_41) ),
% 0.92/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_440,plain,
% 0.92/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 0.92/1.00      | k4_xboole_0(X0_41,k4_xboole_0(X0_41,sK2)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK2) ),
% 0.92/1.00      inference(instantiation,[status(thm)],[c_213]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_442,plain,
% 0.92/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 0.92/1.00      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2) ),
% 0.92/1.00      inference(instantiation,[status(thm)],[c_440]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_1,plain,
% 0.92/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.92/1.00      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 0.92/1.00      inference(cnf_transformation,[],[f21]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_214,plain,
% 0.92/1.00      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_43))
% 0.92/1.00      | m1_subset_1(k9_subset_1(X0_43,X1_41,X0_41),k1_zfmisc_1(X0_43)) ),
% 0.92/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_419,plain,
% 0.92/1.00      ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X0_41,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 0.92/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 0.92/1.00      inference(instantiation,[status(thm)],[c_214]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_421,plain,
% 0.92/1.00      ( m1_subset_1(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 0.92/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 0.92/1.00      inference(instantiation,[status(thm)],[c_419]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_5,negated_conjecture,
% 0.92/1.00      ( ~ v1_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
% 0.92/1.00      inference(cnf_transformation,[],[f29]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_6,negated_conjecture,
% 0.92/1.00      ( v1_tops_2(sK1,sK0) ),
% 0.92/1.00      inference(cnf_transformation,[],[f28]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_7,negated_conjecture,
% 0.92/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 0.92/1.00      inference(cnf_transformation,[],[f27]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(c_8,negated_conjecture,
% 0.92/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 0.92/1.00      inference(cnf_transformation,[],[f26]) ).
% 0.92/1.00  
% 0.92/1.00  cnf(contradiction,plain,
% 0.92/1.00      ( $false ),
% 0.92/1.00      inference(minisat,
% 0.92/1.00                [status(thm)],
% 0.92/1.00                [c_752,c_741,c_674,c_610,c_585,c_442,c_421,c_5,c_6,c_7,
% 0.92/1.00                 c_8]) ).
% 0.92/1.00  
% 0.92/1.00  
% 0.92/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 0.92/1.00  
% 0.92/1.00  ------                               Statistics
% 0.92/1.00  
% 0.92/1.00  ------ General
% 0.92/1.00  
% 0.92/1.00  abstr_ref_over_cycles:                  0
% 0.92/1.00  abstr_ref_under_cycles:                 0
% 0.92/1.00  gc_basic_clause_elim:                   0
% 0.92/1.00  forced_gc_time:                         0
% 0.92/1.00  parsing_time:                           0.009
% 0.92/1.00  unif_index_cands_time:                  0.
% 0.92/1.00  unif_index_add_time:                    0.
% 0.92/1.00  orderings_time:                         0.
% 0.92/1.00  out_proof_time:                         0.01
% 0.92/1.00  total_time:                             0.059
% 0.92/1.00  num_of_symbols:                         48
% 0.92/1.00  num_of_terms:                           1030
% 0.92/1.00  
% 0.92/1.00  ------ Preprocessing
% 0.92/1.00  
% 0.92/1.00  num_of_splits:                          0
% 0.92/1.00  num_of_split_atoms:                     0
% 0.92/1.00  num_of_reused_defs:                     0
% 0.92/1.00  num_eq_ax_congr_red:                    15
% 0.92/1.00  num_of_sem_filtered_clauses:            1
% 0.92/1.00  num_of_subtypes:                        4
% 0.92/1.00  monotx_restored_types:                  0
% 0.92/1.00  sat_num_of_epr_types:                   0
% 0.92/1.00  sat_num_of_non_cyclic_types:            0
% 0.92/1.00  sat_guarded_non_collapsed_types:        0
% 0.92/1.00  num_pure_diseq_elim:                    0
% 0.92/1.00  simp_replaced_by:                       0
% 0.92/1.00  res_preprocessed:                       51
% 0.92/1.00  prep_upred:                             0
% 0.92/1.00  prep_unflattend:                        3
% 0.92/1.00  smt_new_axioms:                         0
% 0.92/1.00  pred_elim_cands:                        2
% 0.92/1.00  pred_elim:                              2
% 0.92/1.00  pred_elim_cl:                           2
% 0.92/1.00  pred_elim_cycles:                       4
% 0.92/1.00  merged_defs:                            0
% 0.92/1.00  merged_defs_ncl:                        0
% 0.92/1.00  bin_hyper_res:                          0
% 0.92/1.00  prep_cycles:                            4
% 0.92/1.00  pred_elim_time:                         0.001
% 0.92/1.00  splitting_time:                         0.
% 0.92/1.00  sem_filter_time:                        0.
% 0.92/1.00  monotx_time:                            0.
% 0.92/1.00  subtype_inf_time:                       0.
% 0.92/1.00  
% 0.92/1.00  ------ Problem properties
% 0.92/1.00  
% 0.92/1.00  clauses:                                8
% 0.92/1.00  conjectures:                            4
% 0.92/1.00  epr:                                    1
% 0.92/1.00  horn:                                   8
% 0.92/1.00  ground:                                 4
% 0.92/1.00  unary:                                  5
% 0.92/1.00  binary:                                 2
% 0.92/1.00  lits:                                   13
% 0.92/1.00  lits_eq:                                2
% 0.92/1.00  fd_pure:                                0
% 0.92/1.00  fd_pseudo:                              0
% 0.92/1.00  fd_cond:                                0
% 0.92/1.00  fd_pseudo_cond:                         0
% 0.92/1.00  ac_symbols:                             0
% 0.92/1.00  
% 0.92/1.00  ------ Propositional Solver
% 0.92/1.00  
% 0.92/1.00  prop_solver_calls:                      25
% 0.92/1.00  prop_fast_solver_calls:                 212
% 0.92/1.00  smt_solver_calls:                       0
% 0.92/1.00  smt_fast_solver_calls:                  0
% 0.92/1.00  prop_num_of_clauses:                    235
% 0.92/1.00  prop_preprocess_simplified:             1320
% 0.92/1.00  prop_fo_subsumed:                       0
% 0.92/1.00  prop_solver_time:                       0.
% 0.92/1.00  smt_solver_time:                        0.
% 0.92/1.00  smt_fast_solver_time:                   0.
% 0.92/1.00  prop_fast_solver_time:                  0.
% 0.92/1.00  prop_unsat_core_time:                   0.
% 0.92/1.00  
% 0.92/1.00  ------ QBF
% 0.92/1.00  
% 0.92/1.00  qbf_q_res:                              0
% 0.92/1.00  qbf_num_tautologies:                    0
% 0.92/1.00  qbf_prep_cycles:                        0
% 0.92/1.00  
% 0.92/1.00  ------ BMC1
% 0.92/1.00  
% 0.92/1.00  bmc1_current_bound:                     -1
% 0.92/1.00  bmc1_last_solved_bound:                 -1
% 0.92/1.00  bmc1_unsat_core_size:                   -1
% 0.92/1.00  bmc1_unsat_core_parents_size:           -1
% 0.92/1.00  bmc1_merge_next_fun:                    0
% 0.92/1.00  bmc1_unsat_core_clauses_time:           0.
% 0.92/1.00  
% 0.92/1.00  ------ Instantiation
% 0.92/1.00  
% 0.92/1.00  inst_num_of_clauses:                    74
% 0.92/1.00  inst_num_in_passive:                    24
% 0.92/1.00  inst_num_in_active:                     49
% 0.92/1.00  inst_num_in_unprocessed:                0
% 0.92/1.00  inst_num_of_loops:                      53
% 0.92/1.00  inst_num_of_learning_restarts:          0
% 0.92/1.00  inst_num_moves_active_passive:          0
% 0.92/1.00  inst_lit_activity:                      0
% 0.92/1.00  inst_lit_activity_moves:                0
% 0.92/1.00  inst_num_tautologies:                   0
% 0.92/1.00  inst_num_prop_implied:                  0
% 0.92/1.00  inst_num_existing_simplified:           0
% 0.92/1.00  inst_num_eq_res_simplified:             0
% 0.92/1.00  inst_num_child_elim:                    0
% 0.92/1.00  inst_num_of_dismatching_blockings:      17
% 0.92/1.00  inst_num_of_non_proper_insts:           75
% 0.92/1.00  inst_num_of_duplicates:                 0
% 0.92/1.00  inst_inst_num_from_inst_to_res:         0
% 0.92/1.00  inst_dismatching_checking_time:         0.
% 0.92/1.00  
% 0.92/1.00  ------ Resolution
% 0.92/1.00  
% 0.92/1.00  res_num_of_clauses:                     0
% 0.92/1.00  res_num_in_passive:                     0
% 0.92/1.00  res_num_in_active:                      0
% 0.92/1.00  res_num_of_loops:                       55
% 0.92/1.00  res_forward_subset_subsumed:            4
% 0.92/1.00  res_backward_subset_subsumed:           0
% 0.92/1.00  res_forward_subsumed:                   0
% 0.92/1.00  res_backward_subsumed:                  0
% 0.92/1.00  res_forward_subsumption_resolution:     0
% 0.92/1.00  res_backward_subsumption_resolution:    0
% 0.92/1.00  res_clause_to_clause_subsumption:       16
% 0.92/1.00  res_orphan_elimination:                 0
% 0.92/1.00  res_tautology_del:                      5
% 0.92/1.00  res_num_eq_res_simplified:              0
% 0.92/1.00  res_num_sel_changes:                    0
% 0.92/1.00  res_moves_from_active_to_pass:          0
% 0.92/1.00  
% 0.92/1.00  ------ Superposition
% 0.92/1.00  
% 0.92/1.00  sup_time_total:                         0.
% 0.92/1.00  sup_time_generating:                    0.
% 0.92/1.00  sup_time_sim_full:                      0.
% 0.92/1.00  sup_time_sim_immed:                     0.
% 0.92/1.00  
% 0.92/1.00  sup_num_of_clauses:                     14
% 0.92/1.00  sup_num_in_active:                      10
% 0.92/1.00  sup_num_in_passive:                     4
% 0.92/1.00  sup_num_of_loops:                       10
% 0.92/1.00  sup_fw_superposition:                   5
% 0.92/1.00  sup_bw_superposition:                   8
% 0.92/1.00  sup_immediate_simplified:               6
% 0.92/1.00  sup_given_eliminated:                   0
% 0.92/1.00  comparisons_done:                       0
% 0.92/1.00  comparisons_avoided:                    0
% 0.92/1.00  
% 0.92/1.00  ------ Simplifications
% 0.92/1.00  
% 0.92/1.00  
% 0.92/1.00  sim_fw_subset_subsumed:                 0
% 0.92/1.00  sim_bw_subset_subsumed:                 0
% 0.92/1.00  sim_fw_subsumed:                        2
% 0.92/1.00  sim_bw_subsumed:                        0
% 0.92/1.00  sim_fw_subsumption_res:                 0
% 0.92/1.00  sim_bw_subsumption_res:                 0
% 0.92/1.00  sim_tautology_del:                      0
% 0.92/1.00  sim_eq_tautology_del:                   1
% 0.92/1.00  sim_eq_res_simp:                        0
% 0.92/1.00  sim_fw_demodulated:                     0
% 0.92/1.00  sim_bw_demodulated:                     0
% 0.92/1.00  sim_light_normalised:                   5
% 0.92/1.00  sim_joinable_taut:                      0
% 0.92/1.00  sim_joinable_simp:                      0
% 0.92/1.00  sim_ac_normalised:                      0
% 0.92/1.00  sim_smt_subsumption:                    0
% 0.92/1.00  
%------------------------------------------------------------------------------
