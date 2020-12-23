%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:54 EST 2020

% Result     : CounterSatisfiable 1.72s
% Output     : Saturation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 568 expanded)
%              Number of clauses        :   70 ( 219 expanded)
%              Number of leaves         :   20 ( 117 expanded)
%              Depth                    :   14
%              Number of atoms          :  304 (1615 expanded)
%              Number of equality atoms :  143 ( 648 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f41,f46])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f40,f46])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f45,f56])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k2_struct_0(X0) = X1
                & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                & k2_struct_0(X0) != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ~ ( k2_struct_0(X0) = X1
                  & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
              & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                  & k2_struct_0(X0) != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( k2_struct_0(X0) = X1
              & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
              & k2_struct_0(X0) != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ( k2_struct_0(X0) = X1
              & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
              & k2_struct_0(X0) != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ( k2_struct_0(X0) = sK2
            & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK2) )
          | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK2)
            & k2_struct_0(X0) != sK2 ) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( k2_struct_0(X0) = X1
                & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
              | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                & k2_struct_0(X0) != X1 ) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ( ( k2_struct_0(sK1) = X1
              & k1_xboole_0 != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X1) )
            | ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X1)
              & k2_struct_0(sK1) != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ( ( k2_struct_0(sK1) = sK2
        & k1_xboole_0 != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2) )
      | ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2)
        & k2_struct_0(sK1) != sK2 ) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f31,f30])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,
    ( k2_struct_0(sK1) = sK2
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK1) != sK2 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_205,plain,
    ( ~ l1_struct_0(X0)
    | l1_struct_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_202,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_199,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_406,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_7,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_691,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_688,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_220,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_10])).

cnf(c_221,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_220])).

cnf(c_235,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r2_hidden(X1,X2)
    | X0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_221])).

cnf(c_236,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r2_hidden(X1,X0) ),
    inference(unflattening,[status(thm)],[c_235])).

cnf(c_686,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_236])).

cnf(c_1053,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_688,c_686])).

cnf(c_1120,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_691,c_1053])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_123,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_124,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_123])).

cnf(c_157,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_124])).

cnf(c_687,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_157])).

cnf(c_1298,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) = k7_subset_1(X1,k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1120,c_687])).

cnf(c_1687,plain,
    ( k7_subset_1(X0,k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_1298])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1693,plain,
    ( k7_subset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1687,c_8])).

cnf(c_1689,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = k7_subset_1(X2,k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_1298,c_1298])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_121,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_122,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_121])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_266,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_122,c_19])).

cnf(c_267,plain,
    ( r1_tarski(sK2,X0)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_266])).

cnf(c_685,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X0)
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_267])).

cnf(c_850,plain,
    ( r1_tarski(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_685])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_690,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1324,plain,
    ( r2_hidden(X0,u1_struct_0(sK1)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_850,c_690])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_692,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1581,plain,
    ( r1_tarski(X0,u1_struct_0(sK1)) = iProver_top
    | r2_hidden(sK0(X0,u1_struct_0(sK1)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1324,c_692])).

cnf(c_1296,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_688,c_687])).

cnf(c_1378,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_1296])).

cnf(c_1379,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1378,c_8])).

cnf(c_1297,plain,
    ( k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0))) = k7_subset_1(u1_struct_0(sK1),sK2,X0) ),
    inference(superposition,[status(thm)],[c_850,c_687])).

cnf(c_1519,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,X0) = k7_subset_1(sK2,sK2,X0) ),
    inference(demodulation,[status(thm)],[c_1297,c_1296])).

cnf(c_1304,plain,
    ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1296,c_687])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_689,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1231,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1120,c_689])).

cnf(c_1230,plain,
    ( u1_struct_0(sK1) = sK2
    | r1_tarski(u1_struct_0(sK1),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_850,c_689])).

cnf(c_15,negated_conjecture,
    ( k2_struct_0(sK1) = sK2
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_20,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_250,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_251,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_250])).

cnf(c_293,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)) = X0
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_251])).

cnf(c_294,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_293])).

cnf(c_802,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k1_xboole_0) = sK2
    | k2_struct_0(sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_15,c_294])).

cnf(c_278,plain,
    ( ~ r1_tarski(X0,X1)
    | X2 != X0
    | k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X2)) = X2
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X1) ),
    inference(resolution_lifted,[status(thm)],[c_124,c_251])).

cnf(c_279,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)) = X0
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_278])).

cnf(c_684,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)) = X0
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X1)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_279])).

cnf(c_946,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)) = X0
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_684])).

cnf(c_1127,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1120,c_946])).

cnf(c_1183,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2) = k1_xboole_0
    | k2_struct_0(sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_802,c_1127])).

cnf(c_1097,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),u1_struct_0(sK1))) = u1_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_688,c_946])).

cnf(c_18,negated_conjecture,
    ( k2_struct_0(sK1) != sK2
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f52])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:55:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.72/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/0.99  
% 1.72/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.72/0.99  
% 1.72/0.99  ------  iProver source info
% 1.72/0.99  
% 1.72/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.72/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.72/0.99  git: non_committed_changes: false
% 1.72/0.99  git: last_make_outside_of_git: false
% 1.72/0.99  
% 1.72/0.99  ------ 
% 1.72/0.99  
% 1.72/0.99  ------ Input Options
% 1.72/0.99  
% 1.72/0.99  --out_options                           all
% 1.72/0.99  --tptp_safe_out                         true
% 1.72/0.99  --problem_path                          ""
% 1.72/0.99  --include_path                          ""
% 1.72/0.99  --clausifier                            res/vclausify_rel
% 1.72/0.99  --clausifier_options                    --mode clausify
% 1.72/0.99  --stdin                                 false
% 1.72/0.99  --stats_out                             all
% 1.72/0.99  
% 1.72/0.99  ------ General Options
% 1.72/0.99  
% 1.72/0.99  --fof                                   false
% 1.72/0.99  --time_out_real                         305.
% 1.72/0.99  --time_out_virtual                      -1.
% 1.72/0.99  --symbol_type_check                     false
% 1.72/0.99  --clausify_out                          false
% 1.72/0.99  --sig_cnt_out                           false
% 1.72/0.99  --trig_cnt_out                          false
% 1.72/0.99  --trig_cnt_out_tolerance                1.
% 1.72/0.99  --trig_cnt_out_sk_spl                   false
% 1.72/0.99  --abstr_cl_out                          false
% 1.72/0.99  
% 1.72/0.99  ------ Global Options
% 1.72/0.99  
% 1.72/0.99  --schedule                              default
% 1.72/0.99  --add_important_lit                     false
% 1.72/0.99  --prop_solver_per_cl                    1000
% 1.72/0.99  --min_unsat_core                        false
% 1.72/0.99  --soft_assumptions                      false
% 1.72/0.99  --soft_lemma_size                       3
% 1.72/0.99  --prop_impl_unit_size                   0
% 1.72/0.99  --prop_impl_unit                        []
% 1.72/0.99  --share_sel_clauses                     true
% 1.72/0.99  --reset_solvers                         false
% 1.72/0.99  --bc_imp_inh                            [conj_cone]
% 1.72/0.99  --conj_cone_tolerance                   3.
% 1.72/0.99  --extra_neg_conj                        none
% 1.72/0.99  --large_theory_mode                     true
% 1.72/0.99  --prolific_symb_bound                   200
% 1.72/0.99  --lt_threshold                          2000
% 1.72/0.99  --clause_weak_htbl                      true
% 1.72/0.99  --gc_record_bc_elim                     false
% 1.72/0.99  
% 1.72/0.99  ------ Preprocessing Options
% 1.72/0.99  
% 1.72/0.99  --preprocessing_flag                    true
% 1.72/0.99  --time_out_prep_mult                    0.1
% 1.72/0.99  --splitting_mode                        input
% 1.72/0.99  --splitting_grd                         true
% 1.72/0.99  --splitting_cvd                         false
% 1.72/0.99  --splitting_cvd_svl                     false
% 1.72/0.99  --splitting_nvd                         32
% 1.72/0.99  --sub_typing                            true
% 1.72/0.99  --prep_gs_sim                           true
% 1.72/0.99  --prep_unflatten                        true
% 1.72/0.99  --prep_res_sim                          true
% 1.72/0.99  --prep_upred                            true
% 1.72/0.99  --prep_sem_filter                       exhaustive
% 1.72/0.99  --prep_sem_filter_out                   false
% 1.72/0.99  --pred_elim                             true
% 1.72/0.99  --res_sim_input                         true
% 1.72/0.99  --eq_ax_congr_red                       true
% 1.72/0.99  --pure_diseq_elim                       true
% 1.72/0.99  --brand_transform                       false
% 1.72/0.99  --non_eq_to_eq                          false
% 1.72/0.99  --prep_def_merge                        true
% 1.72/0.99  --prep_def_merge_prop_impl              false
% 1.72/0.99  --prep_def_merge_mbd                    true
% 1.72/0.99  --prep_def_merge_tr_red                 false
% 1.72/0.99  --prep_def_merge_tr_cl                  false
% 1.72/0.99  --smt_preprocessing                     true
% 1.72/0.99  --smt_ac_axioms                         fast
% 1.72/0.99  --preprocessed_out                      false
% 1.72/0.99  --preprocessed_stats                    false
% 1.72/0.99  
% 1.72/0.99  ------ Abstraction refinement Options
% 1.72/0.99  
% 1.72/0.99  --abstr_ref                             []
% 1.72/0.99  --abstr_ref_prep                        false
% 1.72/0.99  --abstr_ref_until_sat                   false
% 1.72/0.99  --abstr_ref_sig_restrict                funpre
% 1.72/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.72/0.99  --abstr_ref_under                       []
% 1.72/0.99  
% 1.72/0.99  ------ SAT Options
% 1.72/0.99  
% 1.72/0.99  --sat_mode                              false
% 1.72/0.99  --sat_fm_restart_options                ""
% 1.72/0.99  --sat_gr_def                            false
% 1.72/0.99  --sat_epr_types                         true
% 1.72/0.99  --sat_non_cyclic_types                  false
% 1.72/0.99  --sat_finite_models                     false
% 1.72/0.99  --sat_fm_lemmas                         false
% 1.72/0.99  --sat_fm_prep                           false
% 1.72/0.99  --sat_fm_uc_incr                        true
% 1.72/0.99  --sat_out_model                         small
% 1.72/0.99  --sat_out_clauses                       false
% 1.72/0.99  
% 1.72/0.99  ------ QBF Options
% 1.72/0.99  
% 1.72/0.99  --qbf_mode                              false
% 1.72/0.99  --qbf_elim_univ                         false
% 1.72/0.99  --qbf_dom_inst                          none
% 1.72/0.99  --qbf_dom_pre_inst                      false
% 1.72/0.99  --qbf_sk_in                             false
% 1.72/0.99  --qbf_pred_elim                         true
% 1.72/0.99  --qbf_split                             512
% 1.72/0.99  
% 1.72/0.99  ------ BMC1 Options
% 1.72/0.99  
% 1.72/0.99  --bmc1_incremental                      false
% 1.72/0.99  --bmc1_axioms                           reachable_all
% 1.72/0.99  --bmc1_min_bound                        0
% 1.72/0.99  --bmc1_max_bound                        -1
% 1.72/0.99  --bmc1_max_bound_default                -1
% 1.72/0.99  --bmc1_symbol_reachability              true
% 1.72/0.99  --bmc1_property_lemmas                  false
% 1.72/0.99  --bmc1_k_induction                      false
% 1.72/0.99  --bmc1_non_equiv_states                 false
% 1.72/0.99  --bmc1_deadlock                         false
% 1.72/0.99  --bmc1_ucm                              false
% 1.72/0.99  --bmc1_add_unsat_core                   none
% 1.72/0.99  --bmc1_unsat_core_children              false
% 1.72/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.72/0.99  --bmc1_out_stat                         full
% 1.72/0.99  --bmc1_ground_init                      false
% 1.72/0.99  --bmc1_pre_inst_next_state              false
% 1.72/0.99  --bmc1_pre_inst_state                   false
% 1.72/0.99  --bmc1_pre_inst_reach_state             false
% 1.72/0.99  --bmc1_out_unsat_core                   false
% 1.72/0.99  --bmc1_aig_witness_out                  false
% 1.72/0.99  --bmc1_verbose                          false
% 1.72/0.99  --bmc1_dump_clauses_tptp                false
% 1.72/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.72/0.99  --bmc1_dump_file                        -
% 1.72/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.72/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.72/0.99  --bmc1_ucm_extend_mode                  1
% 1.72/0.99  --bmc1_ucm_init_mode                    2
% 1.72/0.99  --bmc1_ucm_cone_mode                    none
% 1.72/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.72/0.99  --bmc1_ucm_relax_model                  4
% 1.72/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.72/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.72/0.99  --bmc1_ucm_layered_model                none
% 1.72/0.99  --bmc1_ucm_max_lemma_size               10
% 1.72/0.99  
% 1.72/0.99  ------ AIG Options
% 1.72/0.99  
% 1.72/0.99  --aig_mode                              false
% 1.72/0.99  
% 1.72/0.99  ------ Instantiation Options
% 1.72/0.99  
% 1.72/0.99  --instantiation_flag                    true
% 1.72/0.99  --inst_sos_flag                         false
% 1.72/0.99  --inst_sos_phase                        true
% 1.72/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.72/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.72/0.99  --inst_lit_sel_side                     num_symb
% 1.72/0.99  --inst_solver_per_active                1400
% 1.72/0.99  --inst_solver_calls_frac                1.
% 1.72/0.99  --inst_passive_queue_type               priority_queues
% 1.72/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.72/0.99  --inst_passive_queues_freq              [25;2]
% 1.72/0.99  --inst_dismatching                      true
% 1.72/0.99  --inst_eager_unprocessed_to_passive     true
% 1.72/0.99  --inst_prop_sim_given                   true
% 1.72/0.99  --inst_prop_sim_new                     false
% 1.72/0.99  --inst_subs_new                         false
% 1.72/0.99  --inst_eq_res_simp                      false
% 1.72/0.99  --inst_subs_given                       false
% 1.72/0.99  --inst_orphan_elimination               true
% 1.72/0.99  --inst_learning_loop_flag               true
% 1.72/0.99  --inst_learning_start                   3000
% 1.72/0.99  --inst_learning_factor                  2
% 1.72/0.99  --inst_start_prop_sim_after_learn       3
% 1.72/0.99  --inst_sel_renew                        solver
% 1.72/0.99  --inst_lit_activity_flag                true
% 1.72/0.99  --inst_restr_to_given                   false
% 1.72/0.99  --inst_activity_threshold               500
% 1.72/0.99  --inst_out_proof                        true
% 1.72/0.99  
% 1.72/0.99  ------ Resolution Options
% 1.72/0.99  
% 1.72/0.99  --resolution_flag                       true
% 1.72/0.99  --res_lit_sel                           adaptive
% 1.72/0.99  --res_lit_sel_side                      none
% 1.72/0.99  --res_ordering                          kbo
% 1.72/0.99  --res_to_prop_solver                    active
% 1.72/0.99  --res_prop_simpl_new                    false
% 1.72/0.99  --res_prop_simpl_given                  true
% 1.72/0.99  --res_passive_queue_type                priority_queues
% 1.72/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.72/0.99  --res_passive_queues_freq               [15;5]
% 1.72/0.99  --res_forward_subs                      full
% 1.72/0.99  --res_backward_subs                     full
% 1.72/0.99  --res_forward_subs_resolution           true
% 1.72/0.99  --res_backward_subs_resolution          true
% 1.72/0.99  --res_orphan_elimination                true
% 1.72/0.99  --res_time_limit                        2.
% 1.72/0.99  --res_out_proof                         true
% 1.72/0.99  
% 1.72/0.99  ------ Superposition Options
% 1.72/0.99  
% 1.72/0.99  --superposition_flag                    true
% 1.72/0.99  --sup_passive_queue_type                priority_queues
% 1.72/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.72/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.72/0.99  --demod_completeness_check              fast
% 1.72/0.99  --demod_use_ground                      true
% 1.72/0.99  --sup_to_prop_solver                    passive
% 1.72/0.99  --sup_prop_simpl_new                    true
% 1.72/0.99  --sup_prop_simpl_given                  true
% 1.72/0.99  --sup_fun_splitting                     false
% 1.72/0.99  --sup_smt_interval                      50000
% 1.72/0.99  
% 1.72/0.99  ------ Superposition Simplification Setup
% 1.72/0.99  
% 1.72/0.99  --sup_indices_passive                   []
% 1.72/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.72/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/0.99  --sup_full_bw                           [BwDemod]
% 1.72/0.99  --sup_immed_triv                        [TrivRules]
% 1.72/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.72/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/0.99  --sup_immed_bw_main                     []
% 1.72/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.72/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/0.99  
% 1.72/0.99  ------ Combination Options
% 1.72/0.99  
% 1.72/0.99  --comb_res_mult                         3
% 1.72/0.99  --comb_sup_mult                         2
% 1.72/0.99  --comb_inst_mult                        10
% 1.72/0.99  
% 1.72/0.99  ------ Debug Options
% 1.72/0.99  
% 1.72/0.99  --dbg_backtrace                         false
% 1.72/0.99  --dbg_dump_prop_clauses                 false
% 1.72/0.99  --dbg_dump_prop_clauses_file            -
% 1.72/0.99  --dbg_out_stat                          false
% 1.72/0.99  ------ Parsing...
% 1.72/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.72/0.99  
% 1.72/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.72/0.99  
% 1.72/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.72/0.99  
% 1.72/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.72/0.99  ------ Proving...
% 1.72/0.99  ------ Problem Properties 
% 1.72/0.99  
% 1.72/0.99  
% 1.72/0.99  clauses                                 14
% 1.72/0.99  conjectures                             2
% 1.72/0.99  EPR                                     4
% 1.72/0.99  Horn                                    12
% 1.72/0.99  unary                                   4
% 1.72/0.99  binary                                  7
% 1.72/0.99  lits                                    27
% 1.72/0.99  lits eq                                 12
% 1.72/0.99  fd_pure                                 0
% 1.72/0.99  fd_pseudo                               0
% 1.72/0.99  fd_cond                                 0
% 1.72/0.99  fd_pseudo_cond                          1
% 1.72/0.99  AC symbols                              0
% 1.72/0.99  
% 1.72/0.99  ------ Schedule dynamic 5 is on 
% 1.72/0.99  
% 1.72/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.72/0.99  
% 1.72/0.99  
% 1.72/0.99  ------ 
% 1.72/0.99  Current options:
% 1.72/0.99  ------ 
% 1.72/0.99  
% 1.72/0.99  ------ Input Options
% 1.72/0.99  
% 1.72/0.99  --out_options                           all
% 1.72/0.99  --tptp_safe_out                         true
% 1.72/0.99  --problem_path                          ""
% 1.72/0.99  --include_path                          ""
% 1.72/0.99  --clausifier                            res/vclausify_rel
% 1.72/0.99  --clausifier_options                    --mode clausify
% 1.72/0.99  --stdin                                 false
% 1.72/0.99  --stats_out                             all
% 1.72/0.99  
% 1.72/0.99  ------ General Options
% 1.72/0.99  
% 1.72/0.99  --fof                                   false
% 1.72/0.99  --time_out_real                         305.
% 1.72/0.99  --time_out_virtual                      -1.
% 1.72/0.99  --symbol_type_check                     false
% 1.72/0.99  --clausify_out                          false
% 1.72/0.99  --sig_cnt_out                           false
% 1.72/0.99  --trig_cnt_out                          false
% 1.72/0.99  --trig_cnt_out_tolerance                1.
% 1.72/0.99  --trig_cnt_out_sk_spl                   false
% 1.72/0.99  --abstr_cl_out                          false
% 1.72/0.99  
% 1.72/0.99  ------ Global Options
% 1.72/0.99  
% 1.72/0.99  --schedule                              default
% 1.72/0.99  --add_important_lit                     false
% 1.72/0.99  --prop_solver_per_cl                    1000
% 1.72/0.99  --min_unsat_core                        false
% 1.72/0.99  --soft_assumptions                      false
% 1.72/0.99  --soft_lemma_size                       3
% 1.72/0.99  --prop_impl_unit_size                   0
% 1.72/0.99  --prop_impl_unit                        []
% 1.72/0.99  --share_sel_clauses                     true
% 1.72/0.99  --reset_solvers                         false
% 1.72/0.99  --bc_imp_inh                            [conj_cone]
% 1.72/0.99  --conj_cone_tolerance                   3.
% 1.72/0.99  --extra_neg_conj                        none
% 1.72/0.99  --large_theory_mode                     true
% 1.72/0.99  --prolific_symb_bound                   200
% 1.72/0.99  --lt_threshold                          2000
% 1.72/0.99  --clause_weak_htbl                      true
% 1.72/0.99  --gc_record_bc_elim                     false
% 1.72/0.99  
% 1.72/0.99  ------ Preprocessing Options
% 1.72/0.99  
% 1.72/0.99  --preprocessing_flag                    true
% 1.72/0.99  --time_out_prep_mult                    0.1
% 1.72/0.99  --splitting_mode                        input
% 1.72/0.99  --splitting_grd                         true
% 1.72/0.99  --splitting_cvd                         false
% 1.72/0.99  --splitting_cvd_svl                     false
% 1.72/0.99  --splitting_nvd                         32
% 1.72/0.99  --sub_typing                            true
% 1.72/0.99  --prep_gs_sim                           true
% 1.72/0.99  --prep_unflatten                        true
% 1.72/0.99  --prep_res_sim                          true
% 1.72/0.99  --prep_upred                            true
% 1.72/0.99  --prep_sem_filter                       exhaustive
% 1.72/0.99  --prep_sem_filter_out                   false
% 1.72/0.99  --pred_elim                             true
% 1.72/0.99  --res_sim_input                         true
% 1.72/0.99  --eq_ax_congr_red                       true
% 1.72/0.99  --pure_diseq_elim                       true
% 1.72/0.99  --brand_transform                       false
% 1.72/0.99  --non_eq_to_eq                          false
% 1.72/0.99  --prep_def_merge                        true
% 1.72/0.99  --prep_def_merge_prop_impl              false
% 1.72/0.99  --prep_def_merge_mbd                    true
% 1.72/0.99  --prep_def_merge_tr_red                 false
% 1.72/0.99  --prep_def_merge_tr_cl                  false
% 1.72/0.99  --smt_preprocessing                     true
% 1.72/0.99  --smt_ac_axioms                         fast
% 1.72/0.99  --preprocessed_out                      false
% 1.72/0.99  --preprocessed_stats                    false
% 1.72/0.99  
% 1.72/0.99  ------ Abstraction refinement Options
% 1.72/0.99  
% 1.72/0.99  --abstr_ref                             []
% 1.72/0.99  --abstr_ref_prep                        false
% 1.72/0.99  --abstr_ref_until_sat                   false
% 1.72/0.99  --abstr_ref_sig_restrict                funpre
% 1.72/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.72/0.99  --abstr_ref_under                       []
% 1.72/0.99  
% 1.72/0.99  ------ SAT Options
% 1.72/0.99  
% 1.72/0.99  --sat_mode                              false
% 1.72/0.99  --sat_fm_restart_options                ""
% 1.72/0.99  --sat_gr_def                            false
% 1.72/0.99  --sat_epr_types                         true
% 1.72/0.99  --sat_non_cyclic_types                  false
% 1.72/0.99  --sat_finite_models                     false
% 1.72/0.99  --sat_fm_lemmas                         false
% 1.72/0.99  --sat_fm_prep                           false
% 1.72/0.99  --sat_fm_uc_incr                        true
% 1.72/0.99  --sat_out_model                         small
% 1.72/0.99  --sat_out_clauses                       false
% 1.72/0.99  
% 1.72/0.99  ------ QBF Options
% 1.72/0.99  
% 1.72/0.99  --qbf_mode                              false
% 1.72/0.99  --qbf_elim_univ                         false
% 1.72/0.99  --qbf_dom_inst                          none
% 1.72/0.99  --qbf_dom_pre_inst                      false
% 1.72/0.99  --qbf_sk_in                             false
% 1.72/0.99  --qbf_pred_elim                         true
% 1.72/0.99  --qbf_split                             512
% 1.72/0.99  
% 1.72/0.99  ------ BMC1 Options
% 1.72/0.99  
% 1.72/0.99  --bmc1_incremental                      false
% 1.72/0.99  --bmc1_axioms                           reachable_all
% 1.72/0.99  --bmc1_min_bound                        0
% 1.72/0.99  --bmc1_max_bound                        -1
% 1.72/0.99  --bmc1_max_bound_default                -1
% 1.72/0.99  --bmc1_symbol_reachability              true
% 1.72/0.99  --bmc1_property_lemmas                  false
% 1.72/0.99  --bmc1_k_induction                      false
% 1.72/0.99  --bmc1_non_equiv_states                 false
% 1.72/0.99  --bmc1_deadlock                         false
% 1.72/0.99  --bmc1_ucm                              false
% 1.72/0.99  --bmc1_add_unsat_core                   none
% 1.72/0.99  --bmc1_unsat_core_children              false
% 1.72/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.72/0.99  --bmc1_out_stat                         full
% 1.72/0.99  --bmc1_ground_init                      false
% 1.72/0.99  --bmc1_pre_inst_next_state              false
% 1.72/0.99  --bmc1_pre_inst_state                   false
% 1.72/0.99  --bmc1_pre_inst_reach_state             false
% 1.72/0.99  --bmc1_out_unsat_core                   false
% 1.72/0.99  --bmc1_aig_witness_out                  false
% 1.72/0.99  --bmc1_verbose                          false
% 1.72/0.99  --bmc1_dump_clauses_tptp                false
% 1.72/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.72/0.99  --bmc1_dump_file                        -
% 1.72/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.72/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.72/0.99  --bmc1_ucm_extend_mode                  1
% 1.72/0.99  --bmc1_ucm_init_mode                    2
% 1.72/0.99  --bmc1_ucm_cone_mode                    none
% 1.72/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.72/0.99  --bmc1_ucm_relax_model                  4
% 1.72/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.72/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.72/0.99  --bmc1_ucm_layered_model                none
% 1.72/0.99  --bmc1_ucm_max_lemma_size               10
% 1.72/0.99  
% 1.72/0.99  ------ AIG Options
% 1.72/0.99  
% 1.72/0.99  --aig_mode                              false
% 1.72/0.99  
% 1.72/0.99  ------ Instantiation Options
% 1.72/0.99  
% 1.72/0.99  --instantiation_flag                    true
% 1.72/0.99  --inst_sos_flag                         false
% 1.72/0.99  --inst_sos_phase                        true
% 1.72/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.72/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.72/0.99  --inst_lit_sel_side                     none
% 1.72/0.99  --inst_solver_per_active                1400
% 1.72/0.99  --inst_solver_calls_frac                1.
% 1.72/0.99  --inst_passive_queue_type               priority_queues
% 1.72/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.72/0.99  --inst_passive_queues_freq              [25;2]
% 1.72/0.99  --inst_dismatching                      true
% 1.72/0.99  --inst_eager_unprocessed_to_passive     true
% 1.72/0.99  --inst_prop_sim_given                   true
% 1.72/0.99  --inst_prop_sim_new                     false
% 1.72/0.99  --inst_subs_new                         false
% 1.72/0.99  --inst_eq_res_simp                      false
% 1.72/0.99  --inst_subs_given                       false
% 1.72/0.99  --inst_orphan_elimination               true
% 1.72/0.99  --inst_learning_loop_flag               true
% 1.72/0.99  --inst_learning_start                   3000
% 1.72/0.99  --inst_learning_factor                  2
% 1.72/0.99  --inst_start_prop_sim_after_learn       3
% 1.72/0.99  --inst_sel_renew                        solver
% 1.72/0.99  --inst_lit_activity_flag                true
% 1.72/0.99  --inst_restr_to_given                   false
% 1.72/0.99  --inst_activity_threshold               500
% 1.72/0.99  --inst_out_proof                        true
% 1.72/0.99  
% 1.72/0.99  ------ Resolution Options
% 1.72/0.99  
% 1.72/0.99  --resolution_flag                       false
% 1.72/0.99  --res_lit_sel                           adaptive
% 1.72/0.99  --res_lit_sel_side                      none
% 1.72/0.99  --res_ordering                          kbo
% 1.72/0.99  --res_to_prop_solver                    active
% 1.72/0.99  --res_prop_simpl_new                    false
% 1.72/0.99  --res_prop_simpl_given                  true
% 1.72/0.99  --res_passive_queue_type                priority_queues
% 1.72/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.72/0.99  --res_passive_queues_freq               [15;5]
% 1.72/0.99  --res_forward_subs                      full
% 1.72/0.99  --res_backward_subs                     full
% 1.72/0.99  --res_forward_subs_resolution           true
% 1.72/0.99  --res_backward_subs_resolution          true
% 1.72/0.99  --res_orphan_elimination                true
% 1.72/0.99  --res_time_limit                        2.
% 1.72/0.99  --res_out_proof                         true
% 1.72/0.99  
% 1.72/0.99  ------ Superposition Options
% 1.72/0.99  
% 1.72/0.99  --superposition_flag                    true
% 1.72/0.99  --sup_passive_queue_type                priority_queues
% 1.72/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.72/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.72/0.99  --demod_completeness_check              fast
% 1.72/0.99  --demod_use_ground                      true
% 1.72/0.99  --sup_to_prop_solver                    passive
% 1.72/0.99  --sup_prop_simpl_new                    true
% 1.72/0.99  --sup_prop_simpl_given                  true
% 1.72/0.99  --sup_fun_splitting                     false
% 1.72/0.99  --sup_smt_interval                      50000
% 1.72/0.99  
% 1.72/0.99  ------ Superposition Simplification Setup
% 1.72/0.99  
% 1.72/0.99  --sup_indices_passive                   []
% 1.72/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.72/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.72/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/0.99  --sup_full_bw                           [BwDemod]
% 1.72/0.99  --sup_immed_triv                        [TrivRules]
% 1.72/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.72/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/0.99  --sup_immed_bw_main                     []
% 1.72/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.72/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.72/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.72/0.99  
% 1.72/0.99  ------ Combination Options
% 1.72/0.99  
% 1.72/0.99  --comb_res_mult                         3
% 1.72/0.99  --comb_sup_mult                         2
% 1.72/0.99  --comb_inst_mult                        10
% 1.72/0.99  
% 1.72/0.99  ------ Debug Options
% 1.72/0.99  
% 1.72/0.99  --dbg_backtrace                         false
% 1.72/0.99  --dbg_dump_prop_clauses                 false
% 1.72/0.99  --dbg_dump_prop_clauses_file            -
% 1.72/0.99  --dbg_out_stat                          false
% 1.72/0.99  
% 1.72/0.99  
% 1.72/0.99  
% 1.72/0.99  
% 1.72/0.99  ------ Proving...
% 1.72/0.99  
% 1.72/0.99  
% 1.72/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 1.72/0.99  
% 1.72/0.99  % SZS output start Saturation for theBenchmark.p
% 1.72/0.99  
% 1.72/0.99  fof(f5,axiom,(
% 1.72/0.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 1.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/0.99  
% 1.72/0.99  fof(f41,plain,(
% 1.72/0.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 1.72/0.99    inference(cnf_transformation,[],[f5])).
% 1.72/0.99  
% 1.72/0.99  fof(f10,axiom,(
% 1.72/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/0.99  
% 1.72/0.99  fof(f46,plain,(
% 1.72/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.72/0.99    inference(cnf_transformation,[],[f10])).
% 1.72/0.99  
% 1.72/0.99  fof(f57,plain,(
% 1.72/0.99    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 1.72/0.99    inference(definition_unfolding,[],[f41,f46])).
% 1.72/0.99  
% 1.72/0.99  fof(f2,axiom,(
% 1.72/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/0.99  
% 1.72/0.99  fof(f17,plain,(
% 1.72/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.72/0.99    inference(ennf_transformation,[],[f2])).
% 1.72/0.99  
% 1.72/0.99  fof(f23,plain,(
% 1.72/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.72/0.99    inference(nnf_transformation,[],[f17])).
% 1.72/0.99  
% 1.72/0.99  fof(f24,plain,(
% 1.72/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.72/0.99    inference(rectify,[],[f23])).
% 1.72/0.99  
% 1.72/0.99  fof(f25,plain,(
% 1.72/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.72/0.99    introduced(choice_axiom,[])).
% 1.72/0.99  
% 1.72/0.99  fof(f26,plain,(
% 1.72/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.72/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 1.72/0.99  
% 1.72/0.99  fof(f35,plain,(
% 1.72/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f26])).
% 1.72/0.99  
% 1.72/0.99  fof(f3,axiom,(
% 1.72/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/0.99  
% 1.72/0.99  fof(f27,plain,(
% 1.72/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.72/0.99    inference(nnf_transformation,[],[f3])).
% 1.72/0.99  
% 1.72/0.99  fof(f28,plain,(
% 1.72/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.72/0.99    inference(flattening,[],[f27])).
% 1.72/0.99  
% 1.72/0.99  fof(f37,plain,(
% 1.72/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.72/0.99    inference(cnf_transformation,[],[f28])).
% 1.72/0.99  
% 1.72/0.99  fof(f60,plain,(
% 1.72/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.72/0.99    inference(equality_resolution,[],[f37])).
% 1.72/0.99  
% 1.72/0.99  fof(f1,axiom,(
% 1.72/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/0.99  
% 1.72/0.99  fof(f15,plain,(
% 1.72/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.72/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 1.72/0.99  
% 1.72/0.99  fof(f16,plain,(
% 1.72/0.99    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.72/0.99    inference(ennf_transformation,[],[f15])).
% 1.72/0.99  
% 1.72/0.99  fof(f33,plain,(
% 1.72/0.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f16])).
% 1.72/0.99  
% 1.72/0.99  fof(f7,axiom,(
% 1.72/0.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/0.99  
% 1.72/0.99  fof(f43,plain,(
% 1.72/0.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f7])).
% 1.72/0.99  
% 1.72/0.99  fof(f8,axiom,(
% 1.72/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/0.99  
% 1.72/0.99  fof(f18,plain,(
% 1.72/0.99    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.72/0.99    inference(ennf_transformation,[],[f8])).
% 1.72/0.99  
% 1.72/0.99  fof(f19,plain,(
% 1.72/0.99    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.72/0.99    inference(flattening,[],[f18])).
% 1.72/0.99  
% 1.72/0.99  fof(f44,plain,(
% 1.72/0.99    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f19])).
% 1.72/0.99  
% 1.72/0.99  fof(f9,axiom,(
% 1.72/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/0.99  
% 1.72/0.99  fof(f20,plain,(
% 1.72/0.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.72/0.99    inference(ennf_transformation,[],[f9])).
% 1.72/0.99  
% 1.72/0.99  fof(f45,plain,(
% 1.72/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.72/0.99    inference(cnf_transformation,[],[f20])).
% 1.72/0.99  
% 1.72/0.99  fof(f4,axiom,(
% 1.72/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/0.99  
% 1.72/0.99  fof(f40,plain,(
% 1.72/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.72/0.99    inference(cnf_transformation,[],[f4])).
% 1.72/0.99  
% 1.72/0.99  fof(f56,plain,(
% 1.72/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.72/0.99    inference(definition_unfolding,[],[f40,f46])).
% 1.72/0.99  
% 1.72/0.99  fof(f58,plain,(
% 1.72/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.72/0.99    inference(definition_unfolding,[],[f45,f56])).
% 1.72/0.99  
% 1.72/0.99  fof(f11,axiom,(
% 1.72/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/0.99  
% 1.72/0.99  fof(f29,plain,(
% 1.72/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.72/0.99    inference(nnf_transformation,[],[f11])).
% 1.72/0.99  
% 1.72/0.99  fof(f48,plain,(
% 1.72/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f29])).
% 1.72/0.99  
% 1.72/0.99  fof(f6,axiom,(
% 1.72/0.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/0.99  
% 1.72/0.99  fof(f42,plain,(
% 1.72/0.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.72/0.99    inference(cnf_transformation,[],[f6])).
% 1.72/0.99  
% 1.72/0.99  fof(f47,plain,(
% 1.72/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.72/0.99    inference(cnf_transformation,[],[f29])).
% 1.72/0.99  
% 1.72/0.99  fof(f13,conjecture,(
% 1.72/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1))))),
% 1.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/0.99  
% 1.72/0.99  fof(f14,negated_conjecture,(
% 1.72/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1))))),
% 1.72/0.99    inference(negated_conjecture,[],[f13])).
% 1.72/0.99  
% 1.72/0.99  fof(f22,plain,(
% 1.72/0.99    ? [X0] : (? [X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_struct_0(X0))),
% 1.72/0.99    inference(ennf_transformation,[],[f14])).
% 1.72/0.99  
% 1.72/0.99  fof(f31,plain,(
% 1.72/0.99    ( ! [X0] : (? [X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (((k2_struct_0(X0) = sK2 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK2)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK2) & k2_struct_0(X0) != sK2)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.72/0.99    introduced(choice_axiom,[])).
% 1.72/0.99  
% 1.72/0.99  fof(f30,plain,(
% 1.72/0.99    ? [X0] : (? [X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_struct_0(X0)) => (? [X1] : (((k2_struct_0(sK1) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X1) & k2_struct_0(sK1) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_struct_0(sK1))),
% 1.72/0.99    introduced(choice_axiom,[])).
% 1.72/0.99  
% 1.72/0.99  fof(f32,plain,(
% 1.72/0.99    (((k2_struct_0(sK1) = sK2 & k1_xboole_0 != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2) & k2_struct_0(sK1) != sK2)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_struct_0(sK1)),
% 1.72/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f31,f30])).
% 1.72/0.99  
% 1.72/0.99  fof(f51,plain,(
% 1.72/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.72/0.99    inference(cnf_transformation,[],[f32])).
% 1.72/0.99  
% 1.72/0.99  fof(f34,plain,(
% 1.72/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f26])).
% 1.72/0.99  
% 1.72/0.99  fof(f36,plain,(
% 1.72/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f26])).
% 1.72/0.99  
% 1.72/0.99  fof(f39,plain,(
% 1.72/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f28])).
% 1.72/0.99  
% 1.72/0.99  fof(f55,plain,(
% 1.72/0.99    k2_struct_0(sK1) = sK2 | k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2)),
% 1.72/0.99    inference(cnf_transformation,[],[f32])).
% 1.72/0.99  
% 1.72/0.99  fof(f12,axiom,(
% 1.72/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))),
% 1.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.72/0.99  
% 1.72/0.99  fof(f21,plain,(
% 1.72/0.99    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 1.72/0.99    inference(ennf_transformation,[],[f12])).
% 1.72/0.99  
% 1.72/0.99  fof(f49,plain,(
% 1.72/0.99    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 1.72/0.99    inference(cnf_transformation,[],[f21])).
% 1.72/0.99  
% 1.72/0.99  fof(f50,plain,(
% 1.72/0.99    l1_struct_0(sK1)),
% 1.72/0.99    inference(cnf_transformation,[],[f32])).
% 1.72/0.99  
% 1.72/0.99  fof(f52,plain,(
% 1.72/0.99    k1_xboole_0 != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2) | k2_struct_0(sK1) != sK2),
% 1.72/0.99    inference(cnf_transformation,[],[f32])).
% 1.72/0.99  
% 1.72/0.99  cnf(c_205,plain,
% 1.72/0.99      ( ~ l1_struct_0(X0) | l1_struct_0(X1) | X1 != X0 ),
% 1.72/0.99      theory(equality) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_202,plain,
% 1.72/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.72/0.99      theory(equality) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_199,plain,
% 1.72/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X0,X2) | X2 != X1 ),
% 1.72/0.99      theory(equality) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_406,plain,( X0_2 = X0_2 ),theory(equality) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_7,plain,
% 1.72/0.99      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 1.72/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_2,plain,
% 1.72/0.99      ( r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0) ),
% 1.72/0.99      inference(cnf_transformation,[],[f35]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_691,plain,
% 1.72/0.99      ( r1_tarski(X0,X1) = iProver_top
% 1.72/0.99      | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_6,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f60]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_688,plain,
% 1.72/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_0,plain,
% 1.72/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.72/0.99      inference(cnf_transformation,[],[f33]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_9,plain,
% 1.72/0.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 1.72/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_10,plain,
% 1.72/0.99      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 1.72/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_220,plain,
% 1.72/0.99      ( ~ r1_tarski(X0,X1) | v1_xboole_0(X0) | X0 != X2 | k1_xboole_0 != X1 ),
% 1.72/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_10]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_221,plain,
% 1.72/0.99      ( ~ r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0) ),
% 1.72/0.99      inference(unflattening,[status(thm)],[c_220]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_235,plain,
% 1.72/0.99      ( ~ r1_tarski(X0,k1_xboole_0) | ~ r2_hidden(X1,X2) | X0 != X2 ),
% 1.72/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_221]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_236,plain,
% 1.72/0.99      ( ~ r1_tarski(X0,k1_xboole_0) | ~ r2_hidden(X1,X0) ),
% 1.72/0.99      inference(unflattening,[status(thm)],[c_235]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_686,plain,
% 1.72/0.99      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 1.72/0.99      | r2_hidden(X1,X0) != iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_236]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1053,plain,
% 1.72/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.72/0.99      inference(superposition,[status(thm)],[c_688,c_686]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1120,plain,
% 1.72/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 1.72/0.99      inference(superposition,[status(thm)],[c_691,c_1053]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_11,plain,
% 1.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.72/0.99      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 1.72/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_12,plain,
% 1.72/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.72/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_123,plain,
% 1.72/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.72/0.99      inference(prop_impl,[status(thm)],[c_12]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_124,plain,
% 1.72/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.72/0.99      inference(renaming,[status(thm)],[c_123]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_157,plain,
% 1.72/0.99      ( ~ r1_tarski(X0,X1)
% 1.72/0.99      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 1.72/0.99      inference(bin_hyper_res,[status(thm)],[c_11,c_124]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_687,plain,
% 1.72/0.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 1.72/0.99      | r1_tarski(X0,X2) != iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_157]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1298,plain,
% 1.72/0.99      ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) = k7_subset_1(X1,k1_xboole_0,X0) ),
% 1.72/0.99      inference(superposition,[status(thm)],[c_1120,c_687]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1687,plain,
% 1.72/0.99      ( k7_subset_1(X0,k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 1.72/0.99      inference(superposition,[status(thm)],[c_7,c_1298]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_8,plain,
% 1.72/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 1.72/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1693,plain,
% 1.72/0.99      ( k7_subset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 1.72/0.99      inference(demodulation,[status(thm)],[c_1687,c_8]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1689,plain,
% 1.72/0.99      ( k7_subset_1(X0,k1_xboole_0,X1) = k7_subset_1(X2,k1_xboole_0,X1) ),
% 1.72/0.99      inference(superposition,[status(thm)],[c_1298,c_1298]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_13,plain,
% 1.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.72/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_121,plain,
% 1.72/0.99      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.72/0.99      inference(prop_impl,[status(thm)],[c_13]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_122,plain,
% 1.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.72/0.99      inference(renaming,[status(thm)],[c_121]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_19,negated_conjecture,
% 1.72/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.72/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_266,plain,
% 1.72/0.99      ( r1_tarski(X0,X1)
% 1.72/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X1)
% 1.72/0.99      | sK2 != X0 ),
% 1.72/0.99      inference(resolution_lifted,[status(thm)],[c_122,c_19]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_267,plain,
% 1.72/0.99      ( r1_tarski(sK2,X0) | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X0) ),
% 1.72/0.99      inference(unflattening,[status(thm)],[c_266]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_685,plain,
% 1.72/0.99      ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X0)
% 1.72/0.99      | r1_tarski(sK2,X0) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_267]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_850,plain,
% 1.72/0.99      ( r1_tarski(sK2,u1_struct_0(sK1)) = iProver_top ),
% 1.72/0.99      inference(equality_resolution,[status(thm)],[c_685]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_3,plain,
% 1.72/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 1.72/0.99      inference(cnf_transformation,[],[f34]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_690,plain,
% 1.72/0.99      ( r1_tarski(X0,X1) != iProver_top
% 1.72/0.99      | r2_hidden(X2,X0) != iProver_top
% 1.72/0.99      | r2_hidden(X2,X1) = iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1324,plain,
% 1.72/0.99      ( r2_hidden(X0,u1_struct_0(sK1)) = iProver_top
% 1.72/0.99      | r2_hidden(X0,sK2) != iProver_top ),
% 1.72/0.99      inference(superposition,[status(thm)],[c_850,c_690]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1,plain,
% 1.72/0.99      ( r1_tarski(X0,X1) | ~ r2_hidden(sK0(X0,X1),X1) ),
% 1.72/0.99      inference(cnf_transformation,[],[f36]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_692,plain,
% 1.72/0.99      ( r1_tarski(X0,X1) = iProver_top
% 1.72/0.99      | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1581,plain,
% 1.72/0.99      ( r1_tarski(X0,u1_struct_0(sK1)) = iProver_top
% 1.72/0.99      | r2_hidden(sK0(X0,u1_struct_0(sK1)),sK2) != iProver_top ),
% 1.72/0.99      inference(superposition,[status(thm)],[c_1324,c_692]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1296,plain,
% 1.72/0.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
% 1.72/0.99      inference(superposition,[status(thm)],[c_688,c_687]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1378,plain,
% 1.72/0.99      ( k7_subset_1(X0,X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
% 1.72/0.99      inference(superposition,[status(thm)],[c_7,c_1296]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1379,plain,
% 1.72/0.99      ( k7_subset_1(X0,X0,k1_xboole_0) = X0 ),
% 1.72/0.99      inference(light_normalisation,[status(thm)],[c_1378,c_8]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1297,plain,
% 1.72/0.99      ( k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0))) = k7_subset_1(u1_struct_0(sK1),sK2,X0) ),
% 1.72/0.99      inference(superposition,[status(thm)],[c_850,c_687]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1519,plain,
% 1.72/0.99      ( k7_subset_1(u1_struct_0(sK1),sK2,X0) = k7_subset_1(sK2,sK2,X0) ),
% 1.72/0.99      inference(demodulation,[status(thm)],[c_1297,c_1296]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1304,plain,
% 1.72/0.99      ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
% 1.72/0.99      | r1_tarski(X0,X2) != iProver_top ),
% 1.72/0.99      inference(demodulation,[status(thm)],[c_1296,c_687]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_4,plain,
% 1.72/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.72/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_689,plain,
% 1.72/0.99      ( X0 = X1
% 1.72/0.99      | r1_tarski(X0,X1) != iProver_top
% 1.72/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1231,plain,
% 1.72/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 1.72/0.99      inference(superposition,[status(thm)],[c_1120,c_689]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1230,plain,
% 1.72/0.99      ( u1_struct_0(sK1) = sK2
% 1.72/0.99      | r1_tarski(u1_struct_0(sK1),sK2) != iProver_top ),
% 1.72/0.99      inference(superposition,[status(thm)],[c_850,c_689]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_15,negated_conjecture,
% 1.72/0.99      ( k2_struct_0(sK1) = sK2
% 1.72/0.99      | k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2) ),
% 1.72/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_14,plain,
% 1.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.72/0.99      | ~ l1_struct_0(X1)
% 1.72/0.99      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0 ),
% 1.72/0.99      inference(cnf_transformation,[],[f49]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_20,negated_conjecture,
% 1.72/0.99      ( l1_struct_0(sK1) ),
% 1.72/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_250,plain,
% 1.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.72/0.99      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0
% 1.72/0.99      | sK1 != X1 ),
% 1.72/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_251,plain,
% 1.72/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.72/0.99      | k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)) = X0 ),
% 1.72/0.99      inference(unflattening,[status(thm)],[c_250]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_293,plain,
% 1.72/0.99      ( k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)) = X0
% 1.72/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1))
% 1.72/0.99      | sK2 != X0 ),
% 1.72/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_251]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_294,plain,
% 1.72/0.99      ( k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2)) = sK2 ),
% 1.72/0.99      inference(unflattening,[status(thm)],[c_293]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_802,plain,
% 1.72/0.99      ( k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k1_xboole_0) = sK2
% 1.72/0.99      | k2_struct_0(sK1) = sK2 ),
% 1.72/0.99      inference(superposition,[status(thm)],[c_15,c_294]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_278,plain,
% 1.72/0.99      ( ~ r1_tarski(X0,X1)
% 1.72/0.99      | X2 != X0
% 1.72/0.99      | k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X2)) = X2
% 1.72/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X1) ),
% 1.72/0.99      inference(resolution_lifted,[status(thm)],[c_124,c_251]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_279,plain,
% 1.72/0.99      ( ~ r1_tarski(X0,X1)
% 1.72/0.99      | k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)) = X0
% 1.72/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X1) ),
% 1.72/0.99      inference(unflattening,[status(thm)],[c_278]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_684,plain,
% 1.72/0.99      ( k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)) = X0
% 1.72/0.99      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X1)
% 1.72/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 1.72/0.99      inference(predicate_to_equality,[status(thm)],[c_279]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_946,plain,
% 1.72/0.99      ( k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),X0)) = X0
% 1.72/0.99      | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
% 1.72/0.99      inference(equality_resolution,[status(thm)],[c_684]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1127,plain,
% 1.72/0.99      ( k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k1_xboole_0)) = k1_xboole_0 ),
% 1.72/0.99      inference(superposition,[status(thm)],[c_1120,c_946]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1183,plain,
% 1.72/0.99      ( k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2) = k1_xboole_0
% 1.72/0.99      | k2_struct_0(sK1) = sK2 ),
% 1.72/0.99      inference(superposition,[status(thm)],[c_802,c_1127]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_1097,plain,
% 1.72/0.99      ( k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),u1_struct_0(sK1))) = u1_struct_0(sK1) ),
% 1.72/0.99      inference(superposition,[status(thm)],[c_688,c_946]) ).
% 1.72/0.99  
% 1.72/0.99  cnf(c_18,negated_conjecture,
% 1.72/0.99      ( k2_struct_0(sK1) != sK2
% 1.72/0.99      | k1_xboole_0 != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2) ),
% 1.72/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.72/0.99  
% 1.72/0.99  
% 1.72/0.99  % SZS output end Saturation for theBenchmark.p
% 1.72/0.99  
% 1.72/0.99  ------                               Statistics
% 1.72/0.99  
% 1.72/0.99  ------ General
% 1.72/0.99  
% 1.72/0.99  abstr_ref_over_cycles:                  0
% 1.72/0.99  abstr_ref_under_cycles:                 0
% 1.72/0.99  gc_basic_clause_elim:                   0
% 1.72/0.99  forced_gc_time:                         0
% 1.72/0.99  parsing_time:                           0.008
% 1.72/0.99  unif_index_cands_time:                  0.
% 1.72/0.99  unif_index_add_time:                    0.
% 1.72/0.99  orderings_time:                         0.
% 1.72/0.99  out_proof_time:                         0.
% 1.72/0.99  total_time:                             0.091
% 1.72/0.99  num_of_symbols:                         48
% 1.72/0.99  num_of_terms:                           1490
% 1.72/0.99  
% 1.72/0.99  ------ Preprocessing
% 1.72/0.99  
% 1.72/0.99  num_of_splits:                          0
% 1.72/0.99  num_of_split_atoms:                     0
% 1.72/0.99  num_of_reused_defs:                     0
% 1.72/0.99  num_eq_ax_congr_red:                    19
% 1.72/0.99  num_of_sem_filtered_clauses:            1
% 1.72/0.99  num_of_subtypes:                        0
% 1.72/0.99  monotx_restored_types:                  0
% 1.72/0.99  sat_num_of_epr_types:                   0
% 1.72/0.99  sat_num_of_non_cyclic_types:            0
% 1.72/0.99  sat_guarded_non_collapsed_types:        0
% 1.72/0.99  num_pure_diseq_elim:                    0
% 1.72/0.99  simp_replaced_by:                       0
% 1.72/0.99  res_preprocessed:                       83
% 1.72/0.99  prep_upred:                             0
% 1.72/0.99  prep_unflattend:                        7
% 1.72/0.99  smt_new_axioms:                         0
% 1.72/0.99  pred_elim_cands:                        2
% 1.72/0.99  pred_elim:                              4
% 1.72/0.99  pred_elim_cl:                           4
% 1.72/0.99  pred_elim_cycles:                       6
% 1.72/0.99  merged_defs:                            10
% 1.72/0.99  merged_defs_ncl:                        0
% 1.72/0.99  bin_hyper_res:                          11
% 1.72/0.99  prep_cycles:                            4
% 1.72/0.99  pred_elim_time:                         0.001
% 1.72/0.99  splitting_time:                         0.
% 1.72/0.99  sem_filter_time:                        0.
% 1.72/0.99  monotx_time:                            0.
% 1.72/0.99  subtype_inf_time:                       0.
% 1.72/0.99  
% 1.72/0.99  ------ Problem properties
% 1.72/0.99  
% 1.72/0.99  clauses:                                14
% 1.72/0.99  conjectures:                            2
% 1.72/0.99  epr:                                    4
% 1.72/0.99  horn:                                   12
% 1.72/0.99  ground:                                 3
% 1.72/0.99  unary:                                  4
% 1.72/0.99  binary:                                 7
% 1.72/0.99  lits:                                   27
% 1.72/0.99  lits_eq:                                12
% 1.72/0.99  fd_pure:                                0
% 1.72/0.99  fd_pseudo:                              0
% 1.72/0.99  fd_cond:                                0
% 1.72/0.99  fd_pseudo_cond:                         1
% 1.72/0.99  ac_symbols:                             0
% 1.72/0.99  
% 1.72/0.99  ------ Propositional Solver
% 1.72/0.99  
% 1.72/0.99  prop_solver_calls:                      28
% 1.72/0.99  prop_fast_solver_calls:                 408
% 1.72/0.99  smt_solver_calls:                       0
% 1.72/0.99  smt_fast_solver_calls:                  0
% 1.72/0.99  prop_num_of_clauses:                    619
% 1.72/0.99  prop_preprocess_simplified:             2603
% 1.72/0.99  prop_fo_subsumed:                       0
% 1.72/0.99  prop_solver_time:                       0.
% 1.72/0.99  smt_solver_time:                        0.
% 1.72/0.99  smt_fast_solver_time:                   0.
% 1.72/0.99  prop_fast_solver_time:                  0.
% 1.72/0.99  prop_unsat_core_time:                   0.
% 1.72/0.99  
% 1.72/0.99  ------ QBF
% 1.72/0.99  
% 1.72/0.99  qbf_q_res:                              0
% 1.72/0.99  qbf_num_tautologies:                    0
% 1.72/0.99  qbf_prep_cycles:                        0
% 1.72/0.99  
% 1.72/0.99  ------ BMC1
% 1.72/0.99  
% 1.72/0.99  bmc1_current_bound:                     -1
% 1.72/0.99  bmc1_last_solved_bound:                 -1
% 1.72/0.99  bmc1_unsat_core_size:                   -1
% 1.72/0.99  bmc1_unsat_core_parents_size:           -1
% 1.72/0.99  bmc1_merge_next_fun:                    0
% 1.72/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.72/0.99  
% 1.72/0.99  ------ Instantiation
% 1.72/0.99  
% 1.72/0.99  inst_num_of_clauses:                    215
% 1.72/0.99  inst_num_in_passive:                    42
% 1.72/0.99  inst_num_in_active:                     122
% 1.72/0.99  inst_num_in_unprocessed:                51
% 1.72/0.99  inst_num_of_loops:                      170
% 1.72/0.99  inst_num_of_learning_restarts:          0
% 1.72/0.99  inst_num_moves_active_passive:          44
% 1.72/0.99  inst_lit_activity:                      0
% 1.72/0.99  inst_lit_activity_moves:                0
% 1.72/0.99  inst_num_tautologies:                   0
% 1.72/0.99  inst_num_prop_implied:                  0
% 1.72/0.99  inst_num_existing_simplified:           0
% 1.72/0.99  inst_num_eq_res_simplified:             0
% 1.72/0.99  inst_num_child_elim:                    0
% 1.72/0.99  inst_num_of_dismatching_blockings:      43
% 1.72/0.99  inst_num_of_non_proper_insts:           207
% 1.72/0.99  inst_num_of_duplicates:                 0
% 1.72/0.99  inst_inst_num_from_inst_to_res:         0
% 1.72/0.99  inst_dismatching_checking_time:         0.
% 1.72/0.99  
% 1.72/0.99  ------ Resolution
% 1.72/0.99  
% 1.72/0.99  res_num_of_clauses:                     0
% 1.72/0.99  res_num_in_passive:                     0
% 1.72/0.99  res_num_in_active:                      0
% 1.72/0.99  res_num_of_loops:                       87
% 1.72/0.99  res_forward_subset_subsumed:            41
% 1.72/0.99  res_backward_subset_subsumed:           0
% 1.72/0.99  res_forward_subsumed:                   0
% 1.72/0.99  res_backward_subsumed:                  0
% 1.72/0.99  res_forward_subsumption_resolution:     0
% 1.72/0.99  res_backward_subsumption_resolution:    0
% 1.72/0.99  res_clause_to_clause_subsumption:       87
% 1.72/0.99  res_orphan_elimination:                 0
% 1.72/0.99  res_tautology_del:                      37
% 1.72/0.99  res_num_eq_res_simplified:              0
% 1.72/0.99  res_num_sel_changes:                    0
% 1.72/0.99  res_moves_from_active_to_pass:          0
% 1.72/0.99  
% 1.72/0.99  ------ Superposition
% 1.72/0.99  
% 1.72/0.99  sup_time_total:                         0.
% 1.72/0.99  sup_time_generating:                    0.
% 1.72/0.99  sup_time_sim_full:                      0.
% 1.72/0.99  sup_time_sim_immed:                     0.
% 1.72/0.99  
% 1.72/0.99  sup_num_of_clauses:                     34
% 1.72/0.99  sup_num_in_active:                      32
% 1.72/0.99  sup_num_in_passive:                     2
% 1.72/0.99  sup_num_of_loops:                       33
% 1.72/0.99  sup_fw_superposition:                   36
% 1.72/0.99  sup_bw_superposition:                   20
% 1.72/0.99  sup_immediate_simplified:               5
% 1.72/0.99  sup_given_eliminated:                   1
% 1.72/0.99  comparisons_done:                       0
% 1.72/0.99  comparisons_avoided:                    3
% 1.72/0.99  
% 1.72/0.99  ------ Simplifications
% 1.72/0.99  
% 1.72/0.99  
% 1.72/0.99  sim_fw_subset_subsumed:                 1
% 1.72/0.99  sim_bw_subset_subsumed:                 0
% 1.72/0.99  sim_fw_subsumed:                        1
% 1.72/0.99  sim_bw_subsumed:                        0
% 1.72/0.99  sim_fw_subsumption_res:                 0
% 1.72/0.99  sim_bw_subsumption_res:                 0
% 1.72/0.99  sim_tautology_del:                      2
% 1.72/0.99  sim_eq_tautology_del:                   3
% 1.72/0.99  sim_eq_res_simp:                        0
% 1.72/0.99  sim_fw_demodulated:                     3
% 1.72/0.99  sim_bw_demodulated:                     2
% 1.72/0.99  sim_light_normalised:                   1
% 1.72/0.99  sim_joinable_taut:                      0
% 1.72/0.99  sim_joinable_simp:                      0
% 1.72/0.99  sim_ac_normalised:                      0
% 1.72/0.99  sim_smt_subsumption:                    0
% 1.72/0.99  
%------------------------------------------------------------------------------
