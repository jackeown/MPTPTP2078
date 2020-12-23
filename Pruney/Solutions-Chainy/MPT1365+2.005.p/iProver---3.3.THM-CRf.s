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
% DateTime   : Thu Dec  3 12:17:57 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 258 expanded)
%              Number of clauses        :   66 (  81 expanded)
%              Number of leaves         :   16 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :  402 (1643 expanded)
%              Number of equality atoms :   54 (  63 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & v4_pre_topc(X1,X0) )
               => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_compts_1(X2,X0)
                  & v2_compts_1(X1,X0)
                  & v8_pre_topc(X0) )
               => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_compts_1(X2,X0)
                    & v2_compts_1(X1,X0)
                    & v8_pre_topc(X0) )
                 => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
          & v2_compts_1(X2,X0)
          & v2_compts_1(X1,X0)
          & v8_pre_topc(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0)
        & v2_compts_1(sK2,X0)
        & v2_compts_1(X1,X0)
        & v8_pre_topc(X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_compts_1(X2,X0)
              & v2_compts_1(X1,X0)
              & v8_pre_topc(X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0)
            & v2_compts_1(X2,X0)
            & v2_compts_1(sK1,X0)
            & v8_pre_topc(X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v2_compts_1(X2,X0)
                & v2_compts_1(X1,X0)
                & v8_pre_topc(X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v2_compts_1(X2,sK0)
              & v2_compts_1(X1,sK0)
              & v8_pre_topc(sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v2_compts_1(sK2,sK0)
    & v2_compts_1(sK1,sK0)
    & v8_pre_topc(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26,f25,f24])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v2_compts_1(X1,X0)
      | ~ v8_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f33,f29])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & v2_compts_1(X1,X0) )
               => v2_compts_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_442,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(X0_47))
    | m1_subset_1(k7_subset_1(X0_47,X0_45,X1_45),k1_zfmisc_1(X0_47)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_821,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0_45),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_4072,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_821])).

cnf(c_452,plain,
    ( ~ m1_subset_1(X0_45,X0_48)
    | m1_subset_1(X1_45,X0_48)
    | X1_45 != X0_45 ),
    theory(equality)).

cnf(c_915,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK0)))
    | X1_45 != X0_45 ),
    inference(instantiation,[status(thm)],[c_452])).

cnf(c_1025,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0_45 ),
    inference(instantiation,[status(thm)],[c_915])).

cnf(c_2321,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k7_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1025])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_441,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(X0_47))
    | k7_subset_1(X0_47,X0_45,X1_45) = k4_xboole_0(X0_45,X1_45) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_846,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,X0_45) = k4_xboole_0(sK1,X0_45) ),
    inference(instantiation,[status(thm)],[c_441])).

cnf(c_1076,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(sK1,X0_45)) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0_45)) ),
    inference(instantiation,[status(thm)],[c_846])).

cnf(c_1677,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1076])).

cnf(c_448,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_941,plain,
    ( X0_45 != X1_45
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X1_45
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = X0_45 ),
    inference(instantiation,[status(thm)],[c_448])).

cnf(c_1269,plain,
    ( X0_45 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = X0_45
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_941])).

cnf(c_1676,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(sK1,sK2))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | k7_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_0,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_444,plain,
    ( r1_tarski(k4_xboole_0(X0_45,k4_xboole_0(X0_45,X1_45)),X0_45) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1658,plain,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1) ),
    inference(instantiation,[status(thm)],[c_444])).

cnf(c_451,plain,
    ( ~ r1_tarski(X0_45,X1_45)
    | r1_tarski(X2_45,X1_45)
    | X2_45 != X0_45 ),
    theory(equality)).

cnf(c_865,plain,
    ( r1_tarski(X0_45,X1_45)
    | ~ r1_tarski(k4_xboole_0(X1_45,k4_xboole_0(X1_45,X2_45)),X1_45)
    | X0_45 != k4_xboole_0(X1_45,k4_xboole_0(X1_45,X2_45)) ),
    inference(instantiation,[status(thm)],[c_451])).

cnf(c_1266,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_865])).

cnf(c_1028,plain,
    ( X0_45 != k9_subset_1(u1_struct_0(sK0),sK1,sK2)
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = X0_45
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_941])).

cnf(c_1174,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,sK2)
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_446,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_1029,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_446])).

cnf(c_6,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_254,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_15])).

cnf(c_255,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_254])).

cnf(c_16,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_259,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ v4_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_255,c_16])).

cnf(c_260,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_259])).

cnf(c_431,plain,
    ( ~ v4_pre_topc(X0_45,sK0)
    | ~ v4_pre_topc(X1_45,sK0)
    | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1_45,X0_45),sK0)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_260])).

cnf(c_950,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_431])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_435,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_714,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_435])).

cnf(c_7,plain,
    ( ~ v2_compts_1(X0,X1)
    | v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v8_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_12,negated_conjecture,
    ( v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_169,plain,
    ( ~ v2_compts_1(X0,X1)
    | v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_12])).

cnf(c_170,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_169])).

cnf(c_174,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_170,c_16,c_15])).

cnf(c_433,plain,
    ( ~ v2_compts_1(X0_45,sK0)
    | v4_pre_topc(X0_45,sK0)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_174])).

cnf(c_716,plain,
    ( v2_compts_1(X0_45,sK0) != iProver_top
    | v4_pre_topc(X0_45,sK0) = iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_433])).

cnf(c_928,plain,
    ( v2_compts_1(sK2,sK0) != iProver_top
    | v4_pre_topc(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_714,c_716])).

cnf(c_938,plain,
    ( ~ v2_compts_1(sK2,sK0)
    | v4_pre_topc(sK2,sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_928])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_440,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(X0_47))
    | k4_xboole_0(X1_45,k4_xboole_0(X1_45,X0_45)) = k9_subset_1(X0_47,X1_45,X0_45) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_851,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_xboole_0(X0_45,k4_xboole_0(X0_45,sK2)) = k9_subset_1(u1_struct_0(sK0),X0_45,sK2) ),
    inference(instantiation,[status(thm)],[c_440])).

cnf(c_853,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_851])).

cnf(c_8,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_228,plain,
    ( ~ v2_compts_1(X0,X1)
    | v2_compts_1(X2,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ v2_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_15])).

cnf(c_229,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | ~ v2_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_228])).

cnf(c_231,plain,
    ( ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(X1,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v2_compts_1(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_229,c_16])).

cnf(c_232,plain,
    ( ~ v2_compts_1(X0,sK0)
    | v2_compts_1(X1,sK0)
    | ~ v4_pre_topc(X1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0) ),
    inference(renaming,[status(thm)],[c_231])).

cnf(c_432,plain,
    ( ~ v2_compts_1(X0_45,sK0)
    | v2_compts_1(X1_45,sK0)
    | ~ v4_pre_topc(X1_45,sK0)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1_45,X0_45) ),
    inference(subtyping,[status(esa)],[c_232])).

cnf(c_811,plain,
    ( ~ v2_compts_1(X0_45,sK0)
    | v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0_45) ),
    inference(instantiation,[status(thm)],[c_432])).

cnf(c_813,plain,
    ( v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ v2_compts_1(sK1,sK0)
    | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(c_487,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_433])).

cnf(c_9,negated_conjecture,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_10,negated_conjecture,
    ( v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_11,negated_conjecture,
    ( v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4072,c_2321,c_1677,c_1676,c_1658,c_1266,c_1174,c_1029,c_950,c_938,c_853,c_813,c_487,c_9,c_10,c_11,c_13,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.47/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/0.99  
% 2.47/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.47/0.99  
% 2.47/0.99  ------  iProver source info
% 2.47/0.99  
% 2.47/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.47/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.47/0.99  git: non_committed_changes: false
% 2.47/0.99  git: last_make_outside_of_git: false
% 2.47/0.99  
% 2.47/0.99  ------ 
% 2.47/0.99  
% 2.47/0.99  ------ Input Options
% 2.47/0.99  
% 2.47/0.99  --out_options                           all
% 2.47/0.99  --tptp_safe_out                         true
% 2.47/0.99  --problem_path                          ""
% 2.47/0.99  --include_path                          ""
% 2.47/0.99  --clausifier                            res/vclausify_rel
% 2.47/0.99  --clausifier_options                    --mode clausify
% 2.47/0.99  --stdin                                 false
% 2.47/0.99  --stats_out                             all
% 2.47/0.99  
% 2.47/0.99  ------ General Options
% 2.47/0.99  
% 2.47/0.99  --fof                                   false
% 2.47/0.99  --time_out_real                         305.
% 2.47/0.99  --time_out_virtual                      -1.
% 2.47/0.99  --symbol_type_check                     false
% 2.47/0.99  --clausify_out                          false
% 2.47/0.99  --sig_cnt_out                           false
% 2.47/0.99  --trig_cnt_out                          false
% 2.47/0.99  --trig_cnt_out_tolerance                1.
% 2.47/0.99  --trig_cnt_out_sk_spl                   false
% 2.47/0.99  --abstr_cl_out                          false
% 2.47/0.99  
% 2.47/0.99  ------ Global Options
% 2.47/0.99  
% 2.47/0.99  --schedule                              default
% 2.47/0.99  --add_important_lit                     false
% 2.47/0.99  --prop_solver_per_cl                    1000
% 2.47/0.99  --min_unsat_core                        false
% 2.47/0.99  --soft_assumptions                      false
% 2.47/0.99  --soft_lemma_size                       3
% 2.47/0.99  --prop_impl_unit_size                   0
% 2.47/0.99  --prop_impl_unit                        []
% 2.47/0.99  --share_sel_clauses                     true
% 2.47/0.99  --reset_solvers                         false
% 2.47/0.99  --bc_imp_inh                            [conj_cone]
% 2.47/0.99  --conj_cone_tolerance                   3.
% 2.47/0.99  --extra_neg_conj                        none
% 2.47/0.99  --large_theory_mode                     true
% 2.47/0.99  --prolific_symb_bound                   200
% 2.47/0.99  --lt_threshold                          2000
% 2.47/0.99  --clause_weak_htbl                      true
% 2.47/0.99  --gc_record_bc_elim                     false
% 2.47/0.99  
% 2.47/0.99  ------ Preprocessing Options
% 2.47/0.99  
% 2.47/0.99  --preprocessing_flag                    true
% 2.47/0.99  --time_out_prep_mult                    0.1
% 2.47/0.99  --splitting_mode                        input
% 2.47/0.99  --splitting_grd                         true
% 2.47/0.99  --splitting_cvd                         false
% 2.47/0.99  --splitting_cvd_svl                     false
% 2.47/0.99  --splitting_nvd                         32
% 2.47/0.99  --sub_typing                            true
% 2.47/0.99  --prep_gs_sim                           true
% 2.47/0.99  --prep_unflatten                        true
% 2.47/0.99  --prep_res_sim                          true
% 2.47/0.99  --prep_upred                            true
% 2.47/0.99  --prep_sem_filter                       exhaustive
% 2.47/0.99  --prep_sem_filter_out                   false
% 2.47/0.99  --pred_elim                             true
% 2.47/0.99  --res_sim_input                         true
% 2.47/0.99  --eq_ax_congr_red                       true
% 2.47/0.99  --pure_diseq_elim                       true
% 2.47/0.99  --brand_transform                       false
% 2.47/0.99  --non_eq_to_eq                          false
% 2.47/0.99  --prep_def_merge                        true
% 2.47/0.99  --prep_def_merge_prop_impl              false
% 2.47/0.99  --prep_def_merge_mbd                    true
% 2.47/0.99  --prep_def_merge_tr_red                 false
% 2.47/0.99  --prep_def_merge_tr_cl                  false
% 2.47/0.99  --smt_preprocessing                     true
% 2.47/0.99  --smt_ac_axioms                         fast
% 2.47/0.99  --preprocessed_out                      false
% 2.47/0.99  --preprocessed_stats                    false
% 2.47/0.99  
% 2.47/0.99  ------ Abstraction refinement Options
% 2.47/0.99  
% 2.47/0.99  --abstr_ref                             []
% 2.47/0.99  --abstr_ref_prep                        false
% 2.47/0.99  --abstr_ref_until_sat                   false
% 2.47/0.99  --abstr_ref_sig_restrict                funpre
% 2.47/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.47/0.99  --abstr_ref_under                       []
% 2.47/0.99  
% 2.47/0.99  ------ SAT Options
% 2.47/0.99  
% 2.47/0.99  --sat_mode                              false
% 2.47/0.99  --sat_fm_restart_options                ""
% 2.47/0.99  --sat_gr_def                            false
% 2.47/0.99  --sat_epr_types                         true
% 2.47/0.99  --sat_non_cyclic_types                  false
% 2.47/0.99  --sat_finite_models                     false
% 2.47/0.99  --sat_fm_lemmas                         false
% 2.47/0.99  --sat_fm_prep                           false
% 2.47/0.99  --sat_fm_uc_incr                        true
% 2.47/0.99  --sat_out_model                         small
% 2.47/0.99  --sat_out_clauses                       false
% 2.47/0.99  
% 2.47/0.99  ------ QBF Options
% 2.47/0.99  
% 2.47/0.99  --qbf_mode                              false
% 2.47/0.99  --qbf_elim_univ                         false
% 2.47/0.99  --qbf_dom_inst                          none
% 2.47/0.99  --qbf_dom_pre_inst                      false
% 2.47/0.99  --qbf_sk_in                             false
% 2.47/0.99  --qbf_pred_elim                         true
% 2.47/0.99  --qbf_split                             512
% 2.47/0.99  
% 2.47/0.99  ------ BMC1 Options
% 2.47/0.99  
% 2.47/0.99  --bmc1_incremental                      false
% 2.47/0.99  --bmc1_axioms                           reachable_all
% 2.47/0.99  --bmc1_min_bound                        0
% 2.47/0.99  --bmc1_max_bound                        -1
% 2.47/0.99  --bmc1_max_bound_default                -1
% 2.47/0.99  --bmc1_symbol_reachability              true
% 2.47/0.99  --bmc1_property_lemmas                  false
% 2.47/0.99  --bmc1_k_induction                      false
% 2.47/0.99  --bmc1_non_equiv_states                 false
% 2.47/0.99  --bmc1_deadlock                         false
% 2.47/0.99  --bmc1_ucm                              false
% 2.47/0.99  --bmc1_add_unsat_core                   none
% 2.47/0.99  --bmc1_unsat_core_children              false
% 2.47/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.47/0.99  --bmc1_out_stat                         full
% 2.47/0.99  --bmc1_ground_init                      false
% 2.47/0.99  --bmc1_pre_inst_next_state              false
% 2.47/0.99  --bmc1_pre_inst_state                   false
% 2.47/0.99  --bmc1_pre_inst_reach_state             false
% 2.47/0.99  --bmc1_out_unsat_core                   false
% 2.47/0.99  --bmc1_aig_witness_out                  false
% 2.47/0.99  --bmc1_verbose                          false
% 2.47/0.99  --bmc1_dump_clauses_tptp                false
% 2.47/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.47/0.99  --bmc1_dump_file                        -
% 2.47/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.47/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.47/0.99  --bmc1_ucm_extend_mode                  1
% 2.47/0.99  --bmc1_ucm_init_mode                    2
% 2.47/0.99  --bmc1_ucm_cone_mode                    none
% 2.47/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.47/0.99  --bmc1_ucm_relax_model                  4
% 2.47/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.47/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.47/0.99  --bmc1_ucm_layered_model                none
% 2.47/0.99  --bmc1_ucm_max_lemma_size               10
% 2.47/0.99  
% 2.47/0.99  ------ AIG Options
% 2.47/0.99  
% 2.47/0.99  --aig_mode                              false
% 2.47/0.99  
% 2.47/0.99  ------ Instantiation Options
% 2.47/0.99  
% 2.47/0.99  --instantiation_flag                    true
% 2.47/0.99  --inst_sos_flag                         false
% 2.47/0.99  --inst_sos_phase                        true
% 2.47/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.47/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.47/0.99  --inst_lit_sel_side                     num_symb
% 2.47/0.99  --inst_solver_per_active                1400
% 2.47/0.99  --inst_solver_calls_frac                1.
% 2.47/0.99  --inst_passive_queue_type               priority_queues
% 2.47/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.47/0.99  --inst_passive_queues_freq              [25;2]
% 2.47/0.99  --inst_dismatching                      true
% 2.47/0.99  --inst_eager_unprocessed_to_passive     true
% 2.47/0.99  --inst_prop_sim_given                   true
% 2.47/0.99  --inst_prop_sim_new                     false
% 2.47/0.99  --inst_subs_new                         false
% 2.47/0.99  --inst_eq_res_simp                      false
% 2.47/0.99  --inst_subs_given                       false
% 2.47/0.99  --inst_orphan_elimination               true
% 2.47/0.99  --inst_learning_loop_flag               true
% 2.47/0.99  --inst_learning_start                   3000
% 2.47/0.99  --inst_learning_factor                  2
% 2.47/0.99  --inst_start_prop_sim_after_learn       3
% 2.47/0.99  --inst_sel_renew                        solver
% 2.47/0.99  --inst_lit_activity_flag                true
% 2.47/0.99  --inst_restr_to_given                   false
% 2.47/0.99  --inst_activity_threshold               500
% 2.47/0.99  --inst_out_proof                        true
% 2.47/0.99  
% 2.47/0.99  ------ Resolution Options
% 2.47/0.99  
% 2.47/0.99  --resolution_flag                       true
% 2.47/0.99  --res_lit_sel                           adaptive
% 2.47/0.99  --res_lit_sel_side                      none
% 2.47/0.99  --res_ordering                          kbo
% 2.47/0.99  --res_to_prop_solver                    active
% 2.47/0.99  --res_prop_simpl_new                    false
% 2.47/0.99  --res_prop_simpl_given                  true
% 2.47/0.99  --res_passive_queue_type                priority_queues
% 2.47/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.47/0.99  --res_passive_queues_freq               [15;5]
% 2.47/0.99  --res_forward_subs                      full
% 2.47/0.99  --res_backward_subs                     full
% 2.47/0.99  --res_forward_subs_resolution           true
% 2.47/0.99  --res_backward_subs_resolution          true
% 2.47/0.99  --res_orphan_elimination                true
% 2.47/0.99  --res_time_limit                        2.
% 2.47/0.99  --res_out_proof                         true
% 2.47/0.99  
% 2.47/0.99  ------ Superposition Options
% 2.47/0.99  
% 2.47/0.99  --superposition_flag                    true
% 2.47/0.99  --sup_passive_queue_type                priority_queues
% 2.47/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.47/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.47/0.99  --demod_completeness_check              fast
% 2.47/0.99  --demod_use_ground                      true
% 2.47/0.99  --sup_to_prop_solver                    passive
% 2.47/0.99  --sup_prop_simpl_new                    true
% 2.47/0.99  --sup_prop_simpl_given                  true
% 2.47/0.99  --sup_fun_splitting                     false
% 2.47/0.99  --sup_smt_interval                      50000
% 2.47/0.99  
% 2.47/0.99  ------ Superposition Simplification Setup
% 2.47/0.99  
% 2.47/0.99  --sup_indices_passive                   []
% 2.47/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.47/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.99  --sup_full_bw                           [BwDemod]
% 2.47/0.99  --sup_immed_triv                        [TrivRules]
% 2.47/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.47/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.99  --sup_immed_bw_main                     []
% 2.47/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.47/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/0.99  
% 2.47/0.99  ------ Combination Options
% 2.47/0.99  
% 2.47/0.99  --comb_res_mult                         3
% 2.47/0.99  --comb_sup_mult                         2
% 2.47/0.99  --comb_inst_mult                        10
% 2.47/0.99  
% 2.47/0.99  ------ Debug Options
% 2.47/0.99  
% 2.47/0.99  --dbg_backtrace                         false
% 2.47/0.99  --dbg_dump_prop_clauses                 false
% 2.47/0.99  --dbg_dump_prop_clauses_file            -
% 2.47/0.99  --dbg_out_stat                          false
% 2.47/0.99  ------ Parsing...
% 2.47/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.47/0.99  
% 2.47/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.47/0.99  
% 2.47/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.47/0.99  
% 2.47/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.47/0.99  ------ Proving...
% 2.47/0.99  ------ Problem Properties 
% 2.47/0.99  
% 2.47/0.99  
% 2.47/0.99  clauses                                 14
% 2.47/0.99  conjectures                             5
% 2.47/0.99  EPR                                     2
% 2.47/0.99  Horn                                    14
% 2.47/0.99  unary                                   8
% 2.47/0.99  binary                                  3
% 2.47/0.99  lits                                    28
% 2.47/0.99  lits eq                                 4
% 2.47/0.99  fd_pure                                 0
% 2.47/0.99  fd_pseudo                               0
% 2.47/0.99  fd_cond                                 0
% 2.47/0.99  fd_pseudo_cond                          0
% 2.47/0.99  AC symbols                              0
% 2.47/0.99  
% 2.47/0.99  ------ Schedule dynamic 5 is on 
% 2.47/0.99  
% 2.47/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.47/0.99  
% 2.47/0.99  
% 2.47/0.99  ------ 
% 2.47/0.99  Current options:
% 2.47/0.99  ------ 
% 2.47/0.99  
% 2.47/0.99  ------ Input Options
% 2.47/0.99  
% 2.47/0.99  --out_options                           all
% 2.47/0.99  --tptp_safe_out                         true
% 2.47/0.99  --problem_path                          ""
% 2.47/0.99  --include_path                          ""
% 2.47/0.99  --clausifier                            res/vclausify_rel
% 2.47/0.99  --clausifier_options                    --mode clausify
% 2.47/0.99  --stdin                                 false
% 2.47/0.99  --stats_out                             all
% 2.47/0.99  
% 2.47/0.99  ------ General Options
% 2.47/0.99  
% 2.47/0.99  --fof                                   false
% 2.47/0.99  --time_out_real                         305.
% 2.47/0.99  --time_out_virtual                      -1.
% 2.47/0.99  --symbol_type_check                     false
% 2.47/0.99  --clausify_out                          false
% 2.47/0.99  --sig_cnt_out                           false
% 2.47/0.99  --trig_cnt_out                          false
% 2.47/0.99  --trig_cnt_out_tolerance                1.
% 2.47/0.99  --trig_cnt_out_sk_spl                   false
% 2.47/0.99  --abstr_cl_out                          false
% 2.47/0.99  
% 2.47/0.99  ------ Global Options
% 2.47/0.99  
% 2.47/0.99  --schedule                              default
% 2.47/0.99  --add_important_lit                     false
% 2.47/0.99  --prop_solver_per_cl                    1000
% 2.47/0.99  --min_unsat_core                        false
% 2.47/0.99  --soft_assumptions                      false
% 2.47/0.99  --soft_lemma_size                       3
% 2.47/0.99  --prop_impl_unit_size                   0
% 2.47/0.99  --prop_impl_unit                        []
% 2.47/0.99  --share_sel_clauses                     true
% 2.47/0.99  --reset_solvers                         false
% 2.47/0.99  --bc_imp_inh                            [conj_cone]
% 2.47/0.99  --conj_cone_tolerance                   3.
% 2.47/0.99  --extra_neg_conj                        none
% 2.47/0.99  --large_theory_mode                     true
% 2.47/0.99  --prolific_symb_bound                   200
% 2.47/0.99  --lt_threshold                          2000
% 2.47/0.99  --clause_weak_htbl                      true
% 2.47/0.99  --gc_record_bc_elim                     false
% 2.47/0.99  
% 2.47/0.99  ------ Preprocessing Options
% 2.47/0.99  
% 2.47/0.99  --preprocessing_flag                    true
% 2.47/0.99  --time_out_prep_mult                    0.1
% 2.47/0.99  --splitting_mode                        input
% 2.47/0.99  --splitting_grd                         true
% 2.47/0.99  --splitting_cvd                         false
% 2.47/0.99  --splitting_cvd_svl                     false
% 2.47/0.99  --splitting_nvd                         32
% 2.47/0.99  --sub_typing                            true
% 2.47/0.99  --prep_gs_sim                           true
% 2.47/0.99  --prep_unflatten                        true
% 2.47/0.99  --prep_res_sim                          true
% 2.47/0.99  --prep_upred                            true
% 2.47/0.99  --prep_sem_filter                       exhaustive
% 2.47/0.99  --prep_sem_filter_out                   false
% 2.47/0.99  --pred_elim                             true
% 2.47/0.99  --res_sim_input                         true
% 2.47/0.99  --eq_ax_congr_red                       true
% 2.47/0.99  --pure_diseq_elim                       true
% 2.47/0.99  --brand_transform                       false
% 2.47/0.99  --non_eq_to_eq                          false
% 2.47/0.99  --prep_def_merge                        true
% 2.47/0.99  --prep_def_merge_prop_impl              false
% 2.47/0.99  --prep_def_merge_mbd                    true
% 2.47/0.99  --prep_def_merge_tr_red                 false
% 2.47/0.99  --prep_def_merge_tr_cl                  false
% 2.47/0.99  --smt_preprocessing                     true
% 2.47/0.99  --smt_ac_axioms                         fast
% 2.47/0.99  --preprocessed_out                      false
% 2.47/0.99  --preprocessed_stats                    false
% 2.47/0.99  
% 2.47/0.99  ------ Abstraction refinement Options
% 2.47/0.99  
% 2.47/0.99  --abstr_ref                             []
% 2.47/0.99  --abstr_ref_prep                        false
% 2.47/0.99  --abstr_ref_until_sat                   false
% 2.47/0.99  --abstr_ref_sig_restrict                funpre
% 2.47/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.47/0.99  --abstr_ref_under                       []
% 2.47/0.99  
% 2.47/0.99  ------ SAT Options
% 2.47/0.99  
% 2.47/0.99  --sat_mode                              false
% 2.47/0.99  --sat_fm_restart_options                ""
% 2.47/0.99  --sat_gr_def                            false
% 2.47/0.99  --sat_epr_types                         true
% 2.47/0.99  --sat_non_cyclic_types                  false
% 2.47/0.99  --sat_finite_models                     false
% 2.47/0.99  --sat_fm_lemmas                         false
% 2.47/0.99  --sat_fm_prep                           false
% 2.47/0.99  --sat_fm_uc_incr                        true
% 2.47/0.99  --sat_out_model                         small
% 2.47/0.99  --sat_out_clauses                       false
% 2.47/0.99  
% 2.47/0.99  ------ QBF Options
% 2.47/0.99  
% 2.47/0.99  --qbf_mode                              false
% 2.47/0.99  --qbf_elim_univ                         false
% 2.47/0.99  --qbf_dom_inst                          none
% 2.47/0.99  --qbf_dom_pre_inst                      false
% 2.47/0.99  --qbf_sk_in                             false
% 2.47/0.99  --qbf_pred_elim                         true
% 2.47/0.99  --qbf_split                             512
% 2.47/0.99  
% 2.47/0.99  ------ BMC1 Options
% 2.47/0.99  
% 2.47/0.99  --bmc1_incremental                      false
% 2.47/0.99  --bmc1_axioms                           reachable_all
% 2.47/0.99  --bmc1_min_bound                        0
% 2.47/0.99  --bmc1_max_bound                        -1
% 2.47/0.99  --bmc1_max_bound_default                -1
% 2.47/0.99  --bmc1_symbol_reachability              true
% 2.47/0.99  --bmc1_property_lemmas                  false
% 2.47/0.99  --bmc1_k_induction                      false
% 2.47/0.99  --bmc1_non_equiv_states                 false
% 2.47/0.99  --bmc1_deadlock                         false
% 2.47/0.99  --bmc1_ucm                              false
% 2.47/0.99  --bmc1_add_unsat_core                   none
% 2.47/0.99  --bmc1_unsat_core_children              false
% 2.47/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.47/0.99  --bmc1_out_stat                         full
% 2.47/0.99  --bmc1_ground_init                      false
% 2.47/0.99  --bmc1_pre_inst_next_state              false
% 2.47/0.99  --bmc1_pre_inst_state                   false
% 2.47/0.99  --bmc1_pre_inst_reach_state             false
% 2.47/0.99  --bmc1_out_unsat_core                   false
% 2.47/0.99  --bmc1_aig_witness_out                  false
% 2.47/0.99  --bmc1_verbose                          false
% 2.47/0.99  --bmc1_dump_clauses_tptp                false
% 2.47/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.47/0.99  --bmc1_dump_file                        -
% 2.47/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.47/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.47/0.99  --bmc1_ucm_extend_mode                  1
% 2.47/0.99  --bmc1_ucm_init_mode                    2
% 2.47/0.99  --bmc1_ucm_cone_mode                    none
% 2.47/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.47/0.99  --bmc1_ucm_relax_model                  4
% 2.47/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.47/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.47/0.99  --bmc1_ucm_layered_model                none
% 2.47/0.99  --bmc1_ucm_max_lemma_size               10
% 2.47/0.99  
% 2.47/0.99  ------ AIG Options
% 2.47/0.99  
% 2.47/0.99  --aig_mode                              false
% 2.47/0.99  
% 2.47/0.99  ------ Instantiation Options
% 2.47/0.99  
% 2.47/0.99  --instantiation_flag                    true
% 2.47/0.99  --inst_sos_flag                         false
% 2.47/0.99  --inst_sos_phase                        true
% 2.47/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.47/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.47/0.99  --inst_lit_sel_side                     none
% 2.47/0.99  --inst_solver_per_active                1400
% 2.47/0.99  --inst_solver_calls_frac                1.
% 2.47/0.99  --inst_passive_queue_type               priority_queues
% 2.47/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.47/0.99  --inst_passive_queues_freq              [25;2]
% 2.47/0.99  --inst_dismatching                      true
% 2.47/0.99  --inst_eager_unprocessed_to_passive     true
% 2.47/0.99  --inst_prop_sim_given                   true
% 2.47/0.99  --inst_prop_sim_new                     false
% 2.47/0.99  --inst_subs_new                         false
% 2.47/0.99  --inst_eq_res_simp                      false
% 2.47/0.99  --inst_subs_given                       false
% 2.47/0.99  --inst_orphan_elimination               true
% 2.47/0.99  --inst_learning_loop_flag               true
% 2.47/0.99  --inst_learning_start                   3000
% 2.47/0.99  --inst_learning_factor                  2
% 2.47/0.99  --inst_start_prop_sim_after_learn       3
% 2.47/0.99  --inst_sel_renew                        solver
% 2.47/0.99  --inst_lit_activity_flag                true
% 2.47/0.99  --inst_restr_to_given                   false
% 2.47/0.99  --inst_activity_threshold               500
% 2.47/0.99  --inst_out_proof                        true
% 2.47/0.99  
% 2.47/0.99  ------ Resolution Options
% 2.47/0.99  
% 2.47/0.99  --resolution_flag                       false
% 2.47/0.99  --res_lit_sel                           adaptive
% 2.47/0.99  --res_lit_sel_side                      none
% 2.47/0.99  --res_ordering                          kbo
% 2.47/0.99  --res_to_prop_solver                    active
% 2.47/0.99  --res_prop_simpl_new                    false
% 2.47/0.99  --res_prop_simpl_given                  true
% 2.47/0.99  --res_passive_queue_type                priority_queues
% 2.47/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.47/0.99  --res_passive_queues_freq               [15;5]
% 2.47/0.99  --res_forward_subs                      full
% 2.47/0.99  --res_backward_subs                     full
% 2.47/0.99  --res_forward_subs_resolution           true
% 2.47/0.99  --res_backward_subs_resolution          true
% 2.47/0.99  --res_orphan_elimination                true
% 2.47/0.99  --res_time_limit                        2.
% 2.47/0.99  --res_out_proof                         true
% 2.47/0.99  
% 2.47/0.99  ------ Superposition Options
% 2.47/0.99  
% 2.47/0.99  --superposition_flag                    true
% 2.47/0.99  --sup_passive_queue_type                priority_queues
% 2.47/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.47/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.47/0.99  --demod_completeness_check              fast
% 2.47/0.99  --demod_use_ground                      true
% 2.47/0.99  --sup_to_prop_solver                    passive
% 2.47/0.99  --sup_prop_simpl_new                    true
% 2.47/0.99  --sup_prop_simpl_given                  true
% 2.47/0.99  --sup_fun_splitting                     false
% 2.47/0.99  --sup_smt_interval                      50000
% 2.47/0.99  
% 2.47/0.99  ------ Superposition Simplification Setup
% 2.47/0.99  
% 2.47/0.99  --sup_indices_passive                   []
% 2.47/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.47/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.99  --sup_full_bw                           [BwDemod]
% 2.47/0.99  --sup_immed_triv                        [TrivRules]
% 2.47/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.47/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.99  --sup_immed_bw_main                     []
% 2.47/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.47/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/0.99  
% 2.47/0.99  ------ Combination Options
% 2.47/0.99  
% 2.47/0.99  --comb_res_mult                         3
% 2.47/0.99  --comb_sup_mult                         2
% 2.47/0.99  --comb_inst_mult                        10
% 2.47/0.99  
% 2.47/0.99  ------ Debug Options
% 2.47/0.99  
% 2.47/0.99  --dbg_backtrace                         false
% 2.47/0.99  --dbg_dump_prop_clauses                 false
% 2.47/0.99  --dbg_dump_prop_clauses_file            -
% 2.47/0.99  --dbg_out_stat                          false
% 2.47/0.99  
% 2.47/0.99  
% 2.47/0.99  
% 2.47/0.99  
% 2.47/0.99  ------ Proving...
% 2.47/0.99  
% 2.47/0.99  
% 2.47/0.99  % SZS status Theorem for theBenchmark.p
% 2.47/0.99  
% 2.47/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.47/0.99  
% 2.47/0.99  fof(f4,axiom,(
% 2.47/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.99  
% 2.47/0.99  fof(f13,plain,(
% 2.47/0.99    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.47/0.99    inference(ennf_transformation,[],[f4])).
% 2.47/0.99  
% 2.47/0.99  fof(f31,plain,(
% 2.47/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.47/0.99    inference(cnf_transformation,[],[f13])).
% 2.47/0.99  
% 2.47/0.99  fof(f5,axiom,(
% 2.47/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.99  
% 2.47/0.99  fof(f14,plain,(
% 2.47/0.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.47/0.99    inference(ennf_transformation,[],[f5])).
% 2.47/0.99  
% 2.47/0.99  fof(f32,plain,(
% 2.47/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.47/0.99    inference(cnf_transformation,[],[f14])).
% 2.47/0.99  
% 2.47/0.99  fof(f1,axiom,(
% 2.47/0.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.99  
% 2.47/0.99  fof(f28,plain,(
% 2.47/0.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.47/0.99    inference(cnf_transformation,[],[f1])).
% 2.47/0.99  
% 2.47/0.99  fof(f2,axiom,(
% 2.47/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.99  
% 2.47/0.99  fof(f29,plain,(
% 2.47/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.47/0.99    inference(cnf_transformation,[],[f2])).
% 2.47/0.99  
% 2.47/0.99  fof(f46,plain,(
% 2.47/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 2.47/0.99    inference(definition_unfolding,[],[f28,f29])).
% 2.47/0.99  
% 2.47/0.99  fof(f8,axiom,(
% 2.47/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 2.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.99  
% 2.47/0.99  fof(f16,plain,(
% 2.47/0.99    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.47/0.99    inference(ennf_transformation,[],[f8])).
% 2.47/0.99  
% 2.47/0.99  fof(f17,plain,(
% 2.47/0.99    ! [X0] : (! [X1] : (! [X2] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.47/0.99    inference(flattening,[],[f16])).
% 2.47/0.99  
% 2.47/0.99  fof(f35,plain,(
% 2.47/0.99    ( ! [X2,X0,X1] : (v4_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v4_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.47/0.99    inference(cnf_transformation,[],[f17])).
% 2.47/0.99  
% 2.47/0.99  fof(f11,conjecture,(
% 2.47/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 2.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.99  
% 2.47/0.99  fof(f12,negated_conjecture,(
% 2.47/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 2.47/0.99    inference(negated_conjecture,[],[f11])).
% 2.47/0.99  
% 2.47/0.99  fof(f22,plain,(
% 2.47/0.99    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.47/0.99    inference(ennf_transformation,[],[f12])).
% 2.47/0.99  
% 2.47/0.99  fof(f23,plain,(
% 2.47/0.99    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.47/0.99    inference(flattening,[],[f22])).
% 2.47/0.99  
% 2.47/0.99  fof(f26,plain,(
% 2.47/0.99    ( ! [X0,X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) & v2_compts_1(sK2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.47/0.99    introduced(choice_axiom,[])).
% 2.47/0.99  
% 2.47/0.99  fof(f25,plain,(
% 2.47/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(sK1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.47/0.99    introduced(choice_axiom,[])).
% 2.47/0.99  
% 2.47/0.99  fof(f24,plain,(
% 2.47/0.99    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v2_compts_1(X2,X0) & v2_compts_1(X1,X0) & v8_pre_topc(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v2_compts_1(X2,sK0) & v2_compts_1(X1,sK0) & v8_pre_topc(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.47/0.99    introduced(choice_axiom,[])).
% 2.47/0.99  
% 2.47/0.99  fof(f27,plain,(
% 2.47/0.99    ((~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v2_compts_1(sK2,sK0) & v2_compts_1(sK1,sK0) & v8_pre_topc(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.47/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26,f25,f24])).
% 2.47/0.99  
% 2.47/0.99  fof(f39,plain,(
% 2.47/0.99    l1_pre_topc(sK0)),
% 2.47/0.99    inference(cnf_transformation,[],[f27])).
% 2.47/0.99  
% 2.47/0.99  fof(f38,plain,(
% 2.47/0.99    v2_pre_topc(sK0)),
% 2.47/0.99    inference(cnf_transformation,[],[f27])).
% 2.47/0.99  
% 2.47/0.99  fof(f41,plain,(
% 2.47/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.47/0.99    inference(cnf_transformation,[],[f27])).
% 2.47/0.99  
% 2.47/0.99  fof(f9,axiom,(
% 2.47/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v4_pre_topc(X1,X0))))),
% 2.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.99  
% 2.47/0.99  fof(f18,plain,(
% 2.47/0.99    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | (~v2_compts_1(X1,X0) | ~v8_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.47/0.99    inference(ennf_transformation,[],[f9])).
% 2.47/0.99  
% 2.47/0.99  fof(f19,plain,(
% 2.47/0.99    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.47/0.99    inference(flattening,[],[f18])).
% 2.47/0.99  
% 2.47/0.99  fof(f36,plain,(
% 2.47/0.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.47/0.99    inference(cnf_transformation,[],[f19])).
% 2.47/0.99  
% 2.47/0.99  fof(f42,plain,(
% 2.47/0.99    v8_pre_topc(sK0)),
% 2.47/0.99    inference(cnf_transformation,[],[f27])).
% 2.47/0.99  
% 2.47/0.99  fof(f6,axiom,(
% 2.47/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 2.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.99  
% 2.47/0.99  fof(f15,plain,(
% 2.47/0.99    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.47/0.99    inference(ennf_transformation,[],[f6])).
% 2.47/0.99  
% 2.47/0.99  fof(f33,plain,(
% 2.47/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.47/0.99    inference(cnf_transformation,[],[f15])).
% 2.47/0.99  
% 2.47/0.99  fof(f47,plain,(
% 2.47/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.47/0.99    inference(definition_unfolding,[],[f33,f29])).
% 2.47/0.99  
% 2.47/0.99  fof(f10,axiom,(
% 2.47/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 2.47/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.99  
% 2.47/0.99  fof(f20,plain,(
% 2.47/0.99    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) | (~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.47/0.99    inference(ennf_transformation,[],[f10])).
% 2.47/0.99  
% 2.47/0.99  fof(f21,plain,(
% 2.47/0.99    ! [X0] : (! [X1] : (! [X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.47/0.99    inference(flattening,[],[f20])).
% 2.47/0.99  
% 2.47/0.99  fof(f37,plain,(
% 2.47/0.99    ( ! [X2,X0,X1] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.47/0.99    inference(cnf_transformation,[],[f21])).
% 2.47/0.99  
% 2.47/0.99  fof(f45,plain,(
% 2.47/0.99    ~v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 2.47/0.99    inference(cnf_transformation,[],[f27])).
% 2.47/0.99  
% 2.47/0.99  fof(f44,plain,(
% 2.47/0.99    v2_compts_1(sK2,sK0)),
% 2.47/0.99    inference(cnf_transformation,[],[f27])).
% 2.47/0.99  
% 2.47/0.99  fof(f43,plain,(
% 2.47/0.99    v2_compts_1(sK1,sK0)),
% 2.47/0.99    inference(cnf_transformation,[],[f27])).
% 2.47/0.99  
% 2.47/0.99  fof(f40,plain,(
% 2.47/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.47/0.99    inference(cnf_transformation,[],[f27])).
% 2.47/0.99  
% 2.47/0.99  cnf(c_2,plain,
% 2.47/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.47/0.99      | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
% 2.47/0.99      inference(cnf_transformation,[],[f31]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_442,plain,
% 2.47/0.99      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(X0_47))
% 2.47/0.99      | m1_subset_1(k7_subset_1(X0_47,X0_45,X1_45),k1_zfmisc_1(X0_47)) ),
% 2.47/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_821,plain,
% 2.47/0.99      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0_45),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.47/0.99      inference(instantiation,[status(thm)],[c_442]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_4072,plain,
% 2.47/0.99      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.47/0.99      inference(instantiation,[status(thm)],[c_821]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_452,plain,
% 2.47/0.99      ( ~ m1_subset_1(X0_45,X0_48)
% 2.47/0.99      | m1_subset_1(X1_45,X0_48)
% 2.47/0.99      | X1_45 != X0_45 ),
% 2.47/0.99      theory(equality) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_915,plain,
% 2.47/0.99      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | X1_45 != X0_45 ),
% 2.47/0.99      inference(instantiation,[status(thm)],[c_452]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_1025,plain,
% 2.47/0.99      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0_45 ),
% 2.47/0.99      inference(instantiation,[status(thm)],[c_915]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_2321,plain,
% 2.47/0.99      ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k7_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(sK1,sK2)) ),
% 2.47/0.99      inference(instantiation,[status(thm)],[c_1025]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_3,plain,
% 2.47/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.47/0.99      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 2.47/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_441,plain,
% 2.47/0.99      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(X0_47))
% 2.47/0.99      | k7_subset_1(X0_47,X0_45,X1_45) = k4_xboole_0(X0_45,X1_45) ),
% 2.47/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_846,plain,
% 2.47/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | k7_subset_1(u1_struct_0(sK0),sK1,X0_45) = k4_xboole_0(sK1,X0_45) ),
% 2.47/0.99      inference(instantiation,[status(thm)],[c_441]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_1076,plain,
% 2.47/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | k7_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(sK1,X0_45)) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0_45)) ),
% 2.47/0.99      inference(instantiation,[status(thm)],[c_846]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_1677,plain,
% 2.47/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | k7_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 2.47/0.99      inference(instantiation,[status(thm)],[c_1076]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_448,plain,
% 2.47/0.99      ( X0_45 != X1_45 | X2_45 != X1_45 | X2_45 = X0_45 ),
% 2.47/0.99      theory(equality) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_941,plain,
% 2.47/0.99      ( X0_45 != X1_45
% 2.47/0.99      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X1_45
% 2.47/0.99      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = X0_45 ),
% 2.47/0.99      inference(instantiation,[status(thm)],[c_448]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_1269,plain,
% 2.47/0.99      ( X0_45 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
% 2.47/0.99      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = X0_45
% 2.47/0.99      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 2.47/0.99      inference(instantiation,[status(thm)],[c_941]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_1676,plain,
% 2.47/0.99      ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(sK1,sK2))
% 2.47/0.99      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
% 2.47/0.99      | k7_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 2.47/0.99      inference(instantiation,[status(thm)],[c_1269]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_0,plain,
% 2.47/0.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 2.47/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_444,plain,
% 2.47/0.99      ( r1_tarski(k4_xboole_0(X0_45,k4_xboole_0(X0_45,X1_45)),X0_45) ),
% 2.47/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_1658,plain,
% 2.47/0.99      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1) ),
% 2.47/0.99      inference(instantiation,[status(thm)],[c_444]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_451,plain,
% 2.47/0.99      ( ~ r1_tarski(X0_45,X1_45)
% 2.47/0.99      | r1_tarski(X2_45,X1_45)
% 2.47/0.99      | X2_45 != X0_45 ),
% 2.47/0.99      theory(equality) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_865,plain,
% 2.47/0.99      ( r1_tarski(X0_45,X1_45)
% 2.47/0.99      | ~ r1_tarski(k4_xboole_0(X1_45,k4_xboole_0(X1_45,X2_45)),X1_45)
% 2.47/0.99      | X0_45 != k4_xboole_0(X1_45,k4_xboole_0(X1_45,X2_45)) ),
% 2.47/0.99      inference(instantiation,[status(thm)],[c_451]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_1266,plain,
% 2.47/0.99      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
% 2.47/0.99      | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)
% 2.47/0.99      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 2.47/0.99      inference(instantiation,[status(thm)],[c_865]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_1028,plain,
% 2.47/0.99      ( X0_45 != k9_subset_1(u1_struct_0(sK0),sK1,sK2)
% 2.47/0.99      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = X0_45
% 2.47/0.99      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
% 2.47/0.99      inference(instantiation,[status(thm)],[c_941]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_1174,plain,
% 2.47/0.99      ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,sK2)
% 2.47/0.99      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
% 2.47/0.99      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
% 2.47/0.99      inference(instantiation,[status(thm)],[c_1028]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_446,plain,( X0_45 = X0_45 ),theory(equality) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_1029,plain,
% 2.47/0.99      ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
% 2.47/0.99      inference(instantiation,[status(thm)],[c_446]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_6,plain,
% 2.47/0.99      ( ~ v4_pre_topc(X0,X1)
% 2.47/0.99      | ~ v4_pre_topc(X2,X1)
% 2.47/0.99      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
% 2.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.47/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.47/0.99      | ~ v2_pre_topc(X1)
% 2.47/0.99      | ~ l1_pre_topc(X1) ),
% 2.47/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_15,negated_conjecture,
% 2.47/0.99      ( l1_pre_topc(sK0) ),
% 2.47/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_254,plain,
% 2.47/0.99      ( ~ v4_pre_topc(X0,X1)
% 2.47/0.99      | ~ v4_pre_topc(X2,X1)
% 2.47/0.99      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,X0),X1)
% 2.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.47/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.47/0.99      | ~ v2_pre_topc(X1)
% 2.47/0.99      | sK0 != X1 ),
% 2.47/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_15]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_255,plain,
% 2.47/0.99      ( ~ v4_pre_topc(X0,sK0)
% 2.47/0.99      | ~ v4_pre_topc(X1,sK0)
% 2.47/0.99      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
% 2.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | ~ v2_pre_topc(sK0) ),
% 2.47/0.99      inference(unflattening,[status(thm)],[c_254]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_16,negated_conjecture,
% 2.47/0.99      ( v2_pre_topc(sK0) ),
% 2.47/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_259,plain,
% 2.47/0.99      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
% 2.47/0.99      | ~ v4_pre_topc(X1,sK0)
% 2.47/0.99      | ~ v4_pre_topc(X0,sK0) ),
% 2.47/0.99      inference(global_propositional_subsumption,
% 2.47/0.99                [status(thm)],
% 2.47/0.99                [c_255,c_16]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_260,plain,
% 2.47/0.99      ( ~ v4_pre_topc(X0,sK0)
% 2.47/0.99      | ~ v4_pre_topc(X1,sK0)
% 2.47/0.99      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X0),sK0)
% 2.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.47/0.99      inference(renaming,[status(thm)],[c_259]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_431,plain,
% 2.47/0.99      ( ~ v4_pre_topc(X0_45,sK0)
% 2.47/0.99      | ~ v4_pre_topc(X1_45,sK0)
% 2.47/0.99      | v4_pre_topc(k9_subset_1(u1_struct_0(sK0),X1_45,X0_45),sK0)
% 2.47/0.99      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.47/0.99      inference(subtyping,[status(esa)],[c_260]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_950,plain,
% 2.47/0.99      ( v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
% 2.47/0.99      | ~ v4_pre_topc(sK2,sK0)
% 2.47/0.99      | ~ v4_pre_topc(sK1,sK0)
% 2.47/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.47/0.99      inference(instantiation,[status(thm)],[c_431]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_13,negated_conjecture,
% 2.47/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.47/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_435,negated_conjecture,
% 2.47/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.47/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_714,plain,
% 2.47/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.47/0.99      inference(predicate_to_equality,[status(thm)],[c_435]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_7,plain,
% 2.47/0.99      ( ~ v2_compts_1(X0,X1)
% 2.47/0.99      | v4_pre_topc(X0,X1)
% 2.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.47/0.99      | ~ v8_pre_topc(X1)
% 2.47/0.99      | ~ v2_pre_topc(X1)
% 2.47/0.99      | ~ l1_pre_topc(X1) ),
% 2.47/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_12,negated_conjecture,
% 2.47/0.99      ( v8_pre_topc(sK0) ),
% 2.47/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_169,plain,
% 2.47/0.99      ( ~ v2_compts_1(X0,X1)
% 2.47/0.99      | v4_pre_topc(X0,X1)
% 2.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.47/0.99      | ~ v2_pre_topc(X1)
% 2.47/0.99      | ~ l1_pre_topc(X1)
% 2.47/0.99      | sK0 != X1 ),
% 2.47/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_12]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_170,plain,
% 2.47/0.99      ( ~ v2_compts_1(X0,sK0)
% 2.47/0.99      | v4_pre_topc(X0,sK0)
% 2.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | ~ v2_pre_topc(sK0)
% 2.47/0.99      | ~ l1_pre_topc(sK0) ),
% 2.47/0.99      inference(unflattening,[status(thm)],[c_169]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_174,plain,
% 2.47/0.99      ( ~ v2_compts_1(X0,sK0)
% 2.47/0.99      | v4_pre_topc(X0,sK0)
% 2.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.47/0.99      inference(global_propositional_subsumption,
% 2.47/0.99                [status(thm)],
% 2.47/0.99                [c_170,c_16,c_15]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_433,plain,
% 2.47/0.99      ( ~ v2_compts_1(X0_45,sK0)
% 2.47/0.99      | v4_pre_topc(X0_45,sK0)
% 2.47/0.99      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.47/0.99      inference(subtyping,[status(esa)],[c_174]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_716,plain,
% 2.47/0.99      ( v2_compts_1(X0_45,sK0) != iProver_top
% 2.47/0.99      | v4_pre_topc(X0_45,sK0) = iProver_top
% 2.47/0.99      | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.47/0.99      inference(predicate_to_equality,[status(thm)],[c_433]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_928,plain,
% 2.47/0.99      ( v2_compts_1(sK2,sK0) != iProver_top
% 2.47/0.99      | v4_pre_topc(sK2,sK0) = iProver_top ),
% 2.47/0.99      inference(superposition,[status(thm)],[c_714,c_716]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_938,plain,
% 2.47/0.99      ( ~ v2_compts_1(sK2,sK0) | v4_pre_topc(sK2,sK0) ),
% 2.47/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_928]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_4,plain,
% 2.47/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.47/0.99      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 2.47/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_440,plain,
% 2.47/0.99      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(X0_47))
% 2.47/0.99      | k4_xboole_0(X1_45,k4_xboole_0(X1_45,X0_45)) = k9_subset_1(X0_47,X1_45,X0_45) ),
% 2.47/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_851,plain,
% 2.47/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | k4_xboole_0(X0_45,k4_xboole_0(X0_45,sK2)) = k9_subset_1(u1_struct_0(sK0),X0_45,sK2) ),
% 2.47/0.99      inference(instantiation,[status(thm)],[c_440]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_853,plain,
% 2.47/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k9_subset_1(u1_struct_0(sK0),sK1,sK2) ),
% 2.47/0.99      inference(instantiation,[status(thm)],[c_851]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_8,plain,
% 2.47/0.99      ( ~ v2_compts_1(X0,X1)
% 2.47/0.99      | v2_compts_1(X2,X1)
% 2.47/0.99      | ~ v4_pre_topc(X2,X1)
% 2.47/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.47/0.99      | ~ r1_tarski(X2,X0)
% 2.47/0.99      | ~ v2_pre_topc(X1)
% 2.47/0.99      | ~ l1_pre_topc(X1) ),
% 2.47/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_228,plain,
% 2.47/0.99      ( ~ v2_compts_1(X0,X1)
% 2.47/0.99      | v2_compts_1(X2,X1)
% 2.47/0.99      | ~ v4_pre_topc(X2,X1)
% 2.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.47/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.47/0.99      | ~ r1_tarski(X2,X0)
% 2.47/0.99      | ~ v2_pre_topc(X1)
% 2.47/0.99      | sK0 != X1 ),
% 2.47/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_15]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_229,plain,
% 2.47/0.99      ( ~ v2_compts_1(X0,sK0)
% 2.47/0.99      | v2_compts_1(X1,sK0)
% 2.47/0.99      | ~ v4_pre_topc(X1,sK0)
% 2.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | ~ r1_tarski(X1,X0)
% 2.47/0.99      | ~ v2_pre_topc(sK0) ),
% 2.47/0.99      inference(unflattening,[status(thm)],[c_228]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_231,plain,
% 2.47/0.99      ( ~ r1_tarski(X1,X0)
% 2.47/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | ~ v4_pre_topc(X1,sK0)
% 2.47/0.99      | v2_compts_1(X1,sK0)
% 2.47/0.99      | ~ v2_compts_1(X0,sK0) ),
% 2.47/0.99      inference(global_propositional_subsumption,
% 2.47/0.99                [status(thm)],
% 2.47/0.99                [c_229,c_16]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_232,plain,
% 2.47/0.99      ( ~ v2_compts_1(X0,sK0)
% 2.47/0.99      | v2_compts_1(X1,sK0)
% 2.47/0.99      | ~ v4_pre_topc(X1,sK0)
% 2.47/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | ~ r1_tarski(X1,X0) ),
% 2.47/0.99      inference(renaming,[status(thm)],[c_231]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_432,plain,
% 2.47/0.99      ( ~ v2_compts_1(X0_45,sK0)
% 2.47/0.99      | v2_compts_1(X1_45,sK0)
% 2.47/0.99      | ~ v4_pre_topc(X1_45,sK0)
% 2.47/0.99      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | ~ r1_tarski(X1_45,X0_45) ),
% 2.47/0.99      inference(subtyping,[status(esa)],[c_232]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_811,plain,
% 2.47/0.99      ( ~ v2_compts_1(X0_45,sK0)
% 2.47/0.99      | v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
% 2.47/0.99      | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
% 2.47/0.99      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),X0_45) ),
% 2.47/0.99      inference(instantiation,[status(thm)],[c_432]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_813,plain,
% 2.47/0.99      ( v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
% 2.47/0.99      | ~ v2_compts_1(sK1,sK0)
% 2.47/0.99      | ~ v4_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
% 2.47/0.99      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.47/0.99      | ~ r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) ),
% 2.47/0.99      inference(instantiation,[status(thm)],[c_811]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_487,plain,
% 2.47/0.99      ( ~ v2_compts_1(sK1,sK0)
% 2.47/0.99      | v4_pre_topc(sK1,sK0)
% 2.47/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.47/0.99      inference(instantiation,[status(thm)],[c_433]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_9,negated_conjecture,
% 2.47/0.99      ( ~ v2_compts_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 2.47/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_10,negated_conjecture,
% 2.47/0.99      ( v2_compts_1(sK2,sK0) ),
% 2.47/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_11,negated_conjecture,
% 2.47/0.99      ( v2_compts_1(sK1,sK0) ),
% 2.47/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(c_14,negated_conjecture,
% 2.47/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.47/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.47/0.99  
% 2.47/0.99  cnf(contradiction,plain,
% 2.47/0.99      ( $false ),
% 2.47/0.99      inference(minisat,
% 2.47/0.99                [status(thm)],
% 2.47/0.99                [c_4072,c_2321,c_1677,c_1676,c_1658,c_1266,c_1174,c_1029,
% 2.47/0.99                 c_950,c_938,c_853,c_813,c_487,c_9,c_10,c_11,c_13,c_14]) ).
% 2.47/0.99  
% 2.47/0.99  
% 2.47/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.47/0.99  
% 2.47/0.99  ------                               Statistics
% 2.47/0.99  
% 2.47/0.99  ------ General
% 2.47/0.99  
% 2.47/0.99  abstr_ref_over_cycles:                  0
% 2.47/0.99  abstr_ref_under_cycles:                 0
% 2.47/0.99  gc_basic_clause_elim:                   0
% 2.47/0.99  forced_gc_time:                         0
% 2.47/0.99  parsing_time:                           0.008
% 2.47/0.99  unif_index_cands_time:                  0.
% 2.47/0.99  unif_index_add_time:                    0.
% 2.47/0.99  orderings_time:                         0.
% 2.47/0.99  out_proof_time:                         0.009
% 2.47/0.99  total_time:                             0.16
% 2.47/0.99  num_of_symbols:                         53
% 2.47/0.99  num_of_terms:                           4719
% 2.47/0.99  
% 2.47/0.99  ------ Preprocessing
% 2.47/0.99  
% 2.47/0.99  num_of_splits:                          0
% 2.47/0.99  num_of_split_atoms:                     0
% 2.47/0.99  num_of_reused_defs:                     0
% 2.47/0.99  num_eq_ax_congr_red:                    28
% 2.47/0.99  num_of_sem_filtered_clauses:            1
% 2.47/0.99  num_of_subtypes:                        5
% 2.47/0.99  monotx_restored_types:                  0
% 2.47/0.99  sat_num_of_epr_types:                   0
% 2.47/0.99  sat_num_of_non_cyclic_types:            0
% 2.47/0.99  sat_guarded_non_collapsed_types:        0
% 2.47/0.99  num_pure_diseq_elim:                    0
% 2.47/0.99  simp_replaced_by:                       0
% 2.47/0.99  res_preprocessed:                       82
% 2.47/0.99  prep_upred:                             0
% 2.47/0.99  prep_unflattend:                        9
% 2.47/0.99  smt_new_axioms:                         0
% 2.47/0.99  pred_elim_cands:                        4
% 2.47/0.99  pred_elim:                              3
% 2.47/0.99  pred_elim_cl:                           3
% 2.47/0.99  pred_elim_cycles:                       6
% 2.47/0.99  merged_defs:                            0
% 2.47/0.99  merged_defs_ncl:                        0
% 2.47/0.99  bin_hyper_res:                          0
% 2.47/0.99  prep_cycles:                            4
% 2.47/0.99  pred_elim_time:                         0.004
% 2.47/0.99  splitting_time:                         0.
% 2.47/0.99  sem_filter_time:                        0.
% 2.47/0.99  monotx_time:                            0.
% 2.47/0.99  subtype_inf_time:                       0.
% 2.47/0.99  
% 2.47/0.99  ------ Problem properties
% 2.47/0.99  
% 2.47/0.99  clauses:                                14
% 2.47/0.99  conjectures:                            5
% 2.47/0.99  epr:                                    2
% 2.47/0.99  horn:                                   14
% 2.47/0.99  ground:                                 5
% 2.47/0.99  unary:                                  8
% 2.47/0.99  binary:                                 3
% 2.47/0.99  lits:                                   28
% 2.47/0.99  lits_eq:                                4
% 2.47/0.99  fd_pure:                                0
% 2.47/0.99  fd_pseudo:                              0
% 2.47/0.99  fd_cond:                                0
% 2.47/0.99  fd_pseudo_cond:                         0
% 2.47/0.99  ac_symbols:                             0
% 2.47/0.99  
% 2.47/0.99  ------ Propositional Solver
% 2.47/0.99  
% 2.47/0.99  prop_solver_calls:                      29
% 2.47/0.99  prop_fast_solver_calls:                 515
% 2.47/0.99  smt_solver_calls:                       0
% 2.47/0.99  smt_fast_solver_calls:                  0
% 2.47/0.99  prop_num_of_clauses:                    1368
% 2.47/0.99  prop_preprocess_simplified:             4306
% 2.47/0.99  prop_fo_subsumed:                       10
% 2.47/0.99  prop_solver_time:                       0.
% 2.47/0.99  smt_solver_time:                        0.
% 2.47/0.99  smt_fast_solver_time:                   0.
% 2.47/0.99  prop_fast_solver_time:                  0.
% 2.47/0.99  prop_unsat_core_time:                   0.
% 2.47/0.99  
% 2.47/0.99  ------ QBF
% 2.47/0.99  
% 2.47/0.99  qbf_q_res:                              0
% 2.47/0.99  qbf_num_tautologies:                    0
% 2.47/0.99  qbf_prep_cycles:                        0
% 2.47/0.99  
% 2.47/0.99  ------ BMC1
% 2.47/0.99  
% 2.47/0.99  bmc1_current_bound:                     -1
% 2.47/0.99  bmc1_last_solved_bound:                 -1
% 2.47/0.99  bmc1_unsat_core_size:                   -1
% 2.47/0.99  bmc1_unsat_core_parents_size:           -1
% 2.47/0.99  bmc1_merge_next_fun:                    0
% 2.47/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.47/0.99  
% 2.47/0.99  ------ Instantiation
% 2.47/0.99  
% 2.47/0.99  inst_num_of_clauses:                    505
% 2.47/0.99  inst_num_in_passive:                    209
% 2.47/0.99  inst_num_in_active:                     231
% 2.47/0.99  inst_num_in_unprocessed:                64
% 2.47/0.99  inst_num_of_loops:                      242
% 2.47/0.99  inst_num_of_learning_restarts:          0
% 2.47/0.99  inst_num_moves_active_passive:          7
% 2.47/0.99  inst_lit_activity:                      0
% 2.47/0.99  inst_lit_activity_moves:                0
% 2.47/0.99  inst_num_tautologies:                   0
% 2.47/0.99  inst_num_prop_implied:                  0
% 2.47/0.99  inst_num_existing_simplified:           0
% 2.47/0.99  inst_num_eq_res_simplified:             0
% 2.47/0.99  inst_num_child_elim:                    0
% 2.47/0.99  inst_num_of_dismatching_blockings:      346
% 2.47/0.99  inst_num_of_non_proper_insts:           556
% 2.47/0.99  inst_num_of_duplicates:                 0
% 2.47/0.99  inst_inst_num_from_inst_to_res:         0
% 2.47/0.99  inst_dismatching_checking_time:         0.
% 2.47/0.99  
% 2.47/0.99  ------ Resolution
% 2.47/0.99  
% 2.47/0.99  res_num_of_clauses:                     0
% 2.47/0.99  res_num_in_passive:                     0
% 2.47/0.99  res_num_in_active:                      0
% 2.47/0.99  res_num_of_loops:                       86
% 2.47/0.99  res_forward_subset_subsumed:            59
% 2.47/0.99  res_backward_subset_subsumed:           0
% 2.47/0.99  res_forward_subsumed:                   0
% 2.47/0.99  res_backward_subsumed:                  0
% 2.47/0.99  res_forward_subsumption_resolution:     0
% 2.47/0.99  res_backward_subsumption_resolution:    0
% 2.47/0.99  res_clause_to_clause_subsumption:       227
% 2.47/0.99  res_orphan_elimination:                 0
% 2.47/0.99  res_tautology_del:                      129
% 2.47/0.99  res_num_eq_res_simplified:              0
% 2.47/0.99  res_num_sel_changes:                    0
% 2.47/0.99  res_moves_from_active_to_pass:          0
% 2.47/0.99  
% 2.47/0.99  ------ Superposition
% 2.47/0.99  
% 2.47/0.99  sup_time_total:                         0.
% 2.47/0.99  sup_time_generating:                    0.
% 2.47/0.99  sup_time_sim_full:                      0.
% 2.47/0.99  sup_time_sim_immed:                     0.
% 2.47/0.99  
% 2.47/0.99  sup_num_of_clauses:                     116
% 2.47/0.99  sup_num_in_active:                      47
% 2.47/0.99  sup_num_in_passive:                     69
% 2.47/0.99  sup_num_of_loops:                       48
% 2.47/0.99  sup_fw_superposition:                   100
% 2.47/0.99  sup_bw_superposition:                   58
% 2.47/0.99  sup_immediate_simplified:               52
% 2.47/0.99  sup_given_eliminated:                   0
% 2.47/0.99  comparisons_done:                       0
% 2.47/0.99  comparisons_avoided:                    0
% 2.47/0.99  
% 2.47/0.99  ------ Simplifications
% 2.47/0.99  
% 2.47/0.99  
% 2.47/0.99  sim_fw_subset_subsumed:                 4
% 2.47/0.99  sim_bw_subset_subsumed:                 2
% 2.47/0.99  sim_fw_subsumed:                        1
% 2.47/0.99  sim_bw_subsumed:                        10
% 2.47/0.99  sim_fw_subsumption_res:                 0
% 2.47/0.99  sim_bw_subsumption_res:                 0
% 2.47/0.99  sim_tautology_del:                      0
% 2.47/0.99  sim_eq_tautology_del:                   1
% 2.47/0.99  sim_eq_res_simp:                        0
% 2.47/0.99  sim_fw_demodulated:                     27
% 2.47/0.99  sim_bw_demodulated:                     2
% 2.47/0.99  sim_light_normalised:                   12
% 2.47/0.99  sim_joinable_taut:                      0
% 2.47/0.99  sim_joinable_simp:                      0
% 2.47/0.99  sim_ac_normalised:                      0
% 2.47/0.99  sim_smt_subsumption:                    0
% 2.47/0.99  
%------------------------------------------------------------------------------
