%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:01 EST 2020

% Result     : CounterSatisfiable 2.25s
% Output     : Saturation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 616 expanded)
%              Number of clauses        :   50 ( 179 expanded)
%              Number of leaves         :   16 ( 168 expanded)
%              Depth                    :   11
%              Number of atoms          :  172 (1330 expanded)
%              Number of equality atoms :  122 ( 908 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f30,f26])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f28,f42])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f27,f42])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

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

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( k2_struct_0(X0) = X1
              & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
              & k2_struct_0(X0) != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ( k2_struct_0(X0) = X1
              & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
              & k2_struct_0(X0) != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ( k2_struct_0(X0) = sK1
            & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1) )
          | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1)
            & k2_struct_0(X0) != sK1 ) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( k2_struct_0(X0) = X1
                & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
              | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                & k2_struct_0(X0) != X1 ) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ( ( k2_struct_0(sK0) = X1
              & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) )
            | ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1)
              & k2_struct_0(sK0) != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ( ( k2_struct_0(sK0) = sK1
        & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )
      | ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
        & k2_struct_0(sK0) != sK1 ) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f25])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k1_enumset1(X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f29,f41])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f24,f41])).

fof(f40,plain,
    ( k2_struct_0(sK0) = sK1
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k2_struct_0(sK0) != sK1 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_109,plain,
    ( ~ l1_struct_0(X0)
    | l1_struct_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_202,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_2,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_406,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_415,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_406,c_1])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_404,plain,
    ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_904,plain,
    ( k9_subset_1(X0,X1,k3_subset_1(X0,X0)) = k7_subset_1(X0,X1,X0)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_415,c_404])).

cnf(c_1966,plain,
    ( k9_subset_1(X0,X0,k3_subset_1(X0,X0)) = k7_subset_1(X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_415,c_904])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_402,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1965,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) = k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_402,c_904])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_403,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1964,plain,
    ( k9_subset_1(X0,k1_xboole_0,k3_subset_1(X0,X0)) = k7_subset_1(X0,k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_403,c_904])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k1_setfam_1(k1_enumset1(X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_405,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_888,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_subset_1(X1,X0,X1) ),
    inference(superposition,[status(thm)],[c_415,c_405])).

cnf(c_0,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1560,plain,
    ( k9_subset_1(X0,X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_888,c_0])).

cnf(c_902,plain,
    ( k9_subset_1(X0,X1,k3_subset_1(X0,k1_xboole_0)) = k7_subset_1(X0,X1,k1_xboole_0)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_403,c_404])).

cnf(c_915,plain,
    ( k9_subset_1(X0,X1,X0) = k7_subset_1(X0,X1,k1_xboole_0)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_902,c_1])).

cnf(c_1433,plain,
    ( k9_subset_1(X0,X0,X0) = k7_subset_1(X0,X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_415,c_915])).

cnf(c_1758,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_1560,c_1433])).

cnf(c_1432,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_402,c_915])).

cnf(c_1563,plain,
    ( k1_setfam_1(k1_enumset1(sK1,sK1,u1_struct_0(sK0))) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_888,c_1432])).

cnf(c_1431,plain,
    ( k9_subset_1(X0,k1_xboole_0,X0) = k7_subset_1(X0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_403,c_915])).

cnf(c_1562,plain,
    ( k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = k7_subset_1(X0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_888,c_1431])).

cnf(c_887,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,sK1)) = k9_subset_1(u1_struct_0(sK0),X0,sK1) ),
    inference(superposition,[status(thm)],[c_402,c_405])).

cnf(c_1554,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(sK1,X0,sK1) ),
    inference(demodulation,[status(thm)],[c_888,c_887])).

cnf(c_886,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0)) = k9_subset_1(X1,X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_403,c_405])).

cnf(c_1310,plain,
    ( k9_subset_1(X0,X1,k1_xboole_0) = k9_subset_1(X2,X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_886,c_886])).

cnf(c_1309,plain,
    ( k9_subset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_886,c_0])).

cnf(c_7,negated_conjecture,
    ( k2_struct_0(sK0) = sK1
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_12,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_117,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_12])).

cnf(c_118,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_117])).

cnf(c_401,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_118])).

cnf(c_497,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_402,c_401])).

cnf(c_603,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) = sK1
    | k2_struct_0(sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_7,c_497])).

cnf(c_654,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_403,c_401])).

cnf(c_1050,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_xboole_0
    | k2_struct_0(sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_603,c_654])).

cnf(c_903,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),X0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_402,c_404])).

cnf(c_990,plain,
    ( k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_415,c_903])).

cnf(c_989,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),sK1,sK1) ),
    inference(superposition,[status(thm)],[c_402,c_903])).

cnf(c_988,plain,
    ( k9_subset_1(u1_struct_0(sK0),k1_xboole_0,k3_subset_1(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) ),
    inference(superposition,[status(thm)],[c_403,c_903])).

cnf(c_718,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_415,c_401])).

cnf(c_10,negated_conjecture,
    ( k2_struct_0(sK0) != sK1
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:22:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.25/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/0.99  
% 2.25/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.25/0.99  
% 2.25/0.99  ------  iProver source info
% 2.25/0.99  
% 2.25/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.25/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.25/0.99  git: non_committed_changes: false
% 2.25/0.99  git: last_make_outside_of_git: false
% 2.25/0.99  
% 2.25/0.99  ------ 
% 2.25/0.99  
% 2.25/0.99  ------ Input Options
% 2.25/0.99  
% 2.25/0.99  --out_options                           all
% 2.25/0.99  --tptp_safe_out                         true
% 2.25/0.99  --problem_path                          ""
% 2.25/0.99  --include_path                          ""
% 2.25/0.99  --clausifier                            res/vclausify_rel
% 2.25/0.99  --clausifier_options                    --mode clausify
% 2.25/0.99  --stdin                                 false
% 2.25/0.99  --stats_out                             all
% 2.25/0.99  
% 2.25/0.99  ------ General Options
% 2.25/0.99  
% 2.25/0.99  --fof                                   false
% 2.25/0.99  --time_out_real                         305.
% 2.25/0.99  --time_out_virtual                      -1.
% 2.25/0.99  --symbol_type_check                     false
% 2.25/0.99  --clausify_out                          false
% 2.25/0.99  --sig_cnt_out                           false
% 2.25/0.99  --trig_cnt_out                          false
% 2.25/0.99  --trig_cnt_out_tolerance                1.
% 2.25/0.99  --trig_cnt_out_sk_spl                   false
% 2.25/0.99  --abstr_cl_out                          false
% 2.25/0.99  
% 2.25/0.99  ------ Global Options
% 2.25/0.99  
% 2.25/0.99  --schedule                              default
% 2.25/0.99  --add_important_lit                     false
% 2.25/0.99  --prop_solver_per_cl                    1000
% 2.25/0.99  --min_unsat_core                        false
% 2.25/0.99  --soft_assumptions                      false
% 2.25/0.99  --soft_lemma_size                       3
% 2.25/0.99  --prop_impl_unit_size                   0
% 2.25/0.99  --prop_impl_unit                        []
% 2.25/0.99  --share_sel_clauses                     true
% 2.25/0.99  --reset_solvers                         false
% 2.25/0.99  --bc_imp_inh                            [conj_cone]
% 2.25/0.99  --conj_cone_tolerance                   3.
% 2.25/0.99  --extra_neg_conj                        none
% 2.25/0.99  --large_theory_mode                     true
% 2.25/0.99  --prolific_symb_bound                   200
% 2.25/0.99  --lt_threshold                          2000
% 2.25/0.99  --clause_weak_htbl                      true
% 2.25/0.99  --gc_record_bc_elim                     false
% 2.25/0.99  
% 2.25/0.99  ------ Preprocessing Options
% 2.25/0.99  
% 2.25/0.99  --preprocessing_flag                    true
% 2.25/0.99  --time_out_prep_mult                    0.1
% 2.25/0.99  --splitting_mode                        input
% 2.25/0.99  --splitting_grd                         true
% 2.25/0.99  --splitting_cvd                         false
% 2.25/0.99  --splitting_cvd_svl                     false
% 2.25/0.99  --splitting_nvd                         32
% 2.25/0.99  --sub_typing                            true
% 2.25/0.99  --prep_gs_sim                           true
% 2.25/0.99  --prep_unflatten                        true
% 2.25/0.99  --prep_res_sim                          true
% 2.25/0.99  --prep_upred                            true
% 2.25/0.99  --prep_sem_filter                       exhaustive
% 2.25/0.99  --prep_sem_filter_out                   false
% 2.25/0.99  --pred_elim                             true
% 2.25/0.99  --res_sim_input                         true
% 2.25/0.99  --eq_ax_congr_red                       true
% 2.25/0.99  --pure_diseq_elim                       true
% 2.25/0.99  --brand_transform                       false
% 2.25/0.99  --non_eq_to_eq                          false
% 2.25/0.99  --prep_def_merge                        true
% 2.25/0.99  --prep_def_merge_prop_impl              false
% 2.25/0.99  --prep_def_merge_mbd                    true
% 2.25/0.99  --prep_def_merge_tr_red                 false
% 2.25/0.99  --prep_def_merge_tr_cl                  false
% 2.25/0.99  --smt_preprocessing                     true
% 2.25/0.99  --smt_ac_axioms                         fast
% 2.25/0.99  --preprocessed_out                      false
% 2.25/0.99  --preprocessed_stats                    false
% 2.25/0.99  
% 2.25/0.99  ------ Abstraction refinement Options
% 2.25/0.99  
% 2.25/0.99  --abstr_ref                             []
% 2.25/0.99  --abstr_ref_prep                        false
% 2.25/0.99  --abstr_ref_until_sat                   false
% 2.25/0.99  --abstr_ref_sig_restrict                funpre
% 2.25/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.25/0.99  --abstr_ref_under                       []
% 2.25/0.99  
% 2.25/0.99  ------ SAT Options
% 2.25/0.99  
% 2.25/0.99  --sat_mode                              false
% 2.25/0.99  --sat_fm_restart_options                ""
% 2.25/0.99  --sat_gr_def                            false
% 2.25/0.99  --sat_epr_types                         true
% 2.25/0.99  --sat_non_cyclic_types                  false
% 2.25/0.99  --sat_finite_models                     false
% 2.25/0.99  --sat_fm_lemmas                         false
% 2.25/0.99  --sat_fm_prep                           false
% 2.25/0.99  --sat_fm_uc_incr                        true
% 2.25/0.99  --sat_out_model                         small
% 2.25/0.99  --sat_out_clauses                       false
% 2.25/0.99  
% 2.25/0.99  ------ QBF Options
% 2.25/0.99  
% 2.25/0.99  --qbf_mode                              false
% 2.25/0.99  --qbf_elim_univ                         false
% 2.25/0.99  --qbf_dom_inst                          none
% 2.25/0.99  --qbf_dom_pre_inst                      false
% 2.25/0.99  --qbf_sk_in                             false
% 2.25/0.99  --qbf_pred_elim                         true
% 2.25/0.99  --qbf_split                             512
% 2.25/0.99  
% 2.25/0.99  ------ BMC1 Options
% 2.25/0.99  
% 2.25/0.99  --bmc1_incremental                      false
% 2.25/0.99  --bmc1_axioms                           reachable_all
% 2.25/0.99  --bmc1_min_bound                        0
% 2.25/0.99  --bmc1_max_bound                        -1
% 2.25/0.99  --bmc1_max_bound_default                -1
% 2.25/0.99  --bmc1_symbol_reachability              true
% 2.25/0.99  --bmc1_property_lemmas                  false
% 2.25/0.99  --bmc1_k_induction                      false
% 2.25/0.99  --bmc1_non_equiv_states                 false
% 2.25/0.99  --bmc1_deadlock                         false
% 2.25/0.99  --bmc1_ucm                              false
% 2.25/0.99  --bmc1_add_unsat_core                   none
% 2.25/0.99  --bmc1_unsat_core_children              false
% 2.25/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.25/0.99  --bmc1_out_stat                         full
% 2.25/0.99  --bmc1_ground_init                      false
% 2.25/0.99  --bmc1_pre_inst_next_state              false
% 2.25/0.99  --bmc1_pre_inst_state                   false
% 2.25/0.99  --bmc1_pre_inst_reach_state             false
% 2.25/0.99  --bmc1_out_unsat_core                   false
% 2.25/0.99  --bmc1_aig_witness_out                  false
% 2.25/0.99  --bmc1_verbose                          false
% 2.25/0.99  --bmc1_dump_clauses_tptp                false
% 2.25/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.25/0.99  --bmc1_dump_file                        -
% 2.25/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.25/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.25/0.99  --bmc1_ucm_extend_mode                  1
% 2.25/0.99  --bmc1_ucm_init_mode                    2
% 2.25/0.99  --bmc1_ucm_cone_mode                    none
% 2.25/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.25/0.99  --bmc1_ucm_relax_model                  4
% 2.25/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.25/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.25/0.99  --bmc1_ucm_layered_model                none
% 2.25/0.99  --bmc1_ucm_max_lemma_size               10
% 2.25/0.99  
% 2.25/0.99  ------ AIG Options
% 2.25/0.99  
% 2.25/0.99  --aig_mode                              false
% 2.25/0.99  
% 2.25/0.99  ------ Instantiation Options
% 2.25/0.99  
% 2.25/0.99  --instantiation_flag                    true
% 2.25/0.99  --inst_sos_flag                         false
% 2.25/0.99  --inst_sos_phase                        true
% 2.25/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.25/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.25/0.99  --inst_lit_sel_side                     num_symb
% 2.25/0.99  --inst_solver_per_active                1400
% 2.25/0.99  --inst_solver_calls_frac                1.
% 2.25/0.99  --inst_passive_queue_type               priority_queues
% 2.25/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.25/0.99  --inst_passive_queues_freq              [25;2]
% 2.25/0.99  --inst_dismatching                      true
% 2.25/0.99  --inst_eager_unprocessed_to_passive     true
% 2.25/0.99  --inst_prop_sim_given                   true
% 2.25/0.99  --inst_prop_sim_new                     false
% 2.25/0.99  --inst_subs_new                         false
% 2.25/0.99  --inst_eq_res_simp                      false
% 2.25/0.99  --inst_subs_given                       false
% 2.25/0.99  --inst_orphan_elimination               true
% 2.25/0.99  --inst_learning_loop_flag               true
% 2.25/0.99  --inst_learning_start                   3000
% 2.25/0.99  --inst_learning_factor                  2
% 2.25/0.99  --inst_start_prop_sim_after_learn       3
% 2.25/0.99  --inst_sel_renew                        solver
% 2.25/0.99  --inst_lit_activity_flag                true
% 2.25/0.99  --inst_restr_to_given                   false
% 2.25/0.99  --inst_activity_threshold               500
% 2.25/0.99  --inst_out_proof                        true
% 2.25/0.99  
% 2.25/0.99  ------ Resolution Options
% 2.25/0.99  
% 2.25/0.99  --resolution_flag                       true
% 2.25/0.99  --res_lit_sel                           adaptive
% 2.25/0.99  --res_lit_sel_side                      none
% 2.25/0.99  --res_ordering                          kbo
% 2.25/0.99  --res_to_prop_solver                    active
% 2.25/0.99  --res_prop_simpl_new                    false
% 2.25/0.99  --res_prop_simpl_given                  true
% 2.25/0.99  --res_passive_queue_type                priority_queues
% 2.25/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.25/0.99  --res_passive_queues_freq               [15;5]
% 2.25/0.99  --res_forward_subs                      full
% 2.25/0.99  --res_backward_subs                     full
% 2.25/0.99  --res_forward_subs_resolution           true
% 2.25/0.99  --res_backward_subs_resolution          true
% 2.25/0.99  --res_orphan_elimination                true
% 2.25/0.99  --res_time_limit                        2.
% 2.25/0.99  --res_out_proof                         true
% 2.25/0.99  
% 2.25/0.99  ------ Superposition Options
% 2.25/0.99  
% 2.25/0.99  --superposition_flag                    true
% 2.25/0.99  --sup_passive_queue_type                priority_queues
% 2.25/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.25/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.25/0.99  --demod_completeness_check              fast
% 2.25/0.99  --demod_use_ground                      true
% 2.25/0.99  --sup_to_prop_solver                    passive
% 2.25/0.99  --sup_prop_simpl_new                    true
% 2.25/0.99  --sup_prop_simpl_given                  true
% 2.25/0.99  --sup_fun_splitting                     false
% 2.25/0.99  --sup_smt_interval                      50000
% 2.25/0.99  
% 2.25/0.99  ------ Superposition Simplification Setup
% 2.25/0.99  
% 2.25/0.99  --sup_indices_passive                   []
% 2.25/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.25/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.99  --sup_full_bw                           [BwDemod]
% 2.25/0.99  --sup_immed_triv                        [TrivRules]
% 2.25/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.25/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.99  --sup_immed_bw_main                     []
% 2.25/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.25/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.25/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.25/0.99  
% 2.25/0.99  ------ Combination Options
% 2.25/0.99  
% 2.25/0.99  --comb_res_mult                         3
% 2.25/0.99  --comb_sup_mult                         2
% 2.25/0.99  --comb_inst_mult                        10
% 2.25/0.99  
% 2.25/0.99  ------ Debug Options
% 2.25/0.99  
% 2.25/0.99  --dbg_backtrace                         false
% 2.25/0.99  --dbg_dump_prop_clauses                 false
% 2.25/0.99  --dbg_dump_prop_clauses_file            -
% 2.25/0.99  --dbg_out_stat                          false
% 2.25/0.99  ------ Parsing...
% 2.25/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.25/0.99  
% 2.25/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.25/0.99  
% 2.25/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.25/0.99  
% 2.25/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.25/0.99  ------ Proving...
% 2.25/0.99  ------ Problem Properties 
% 2.25/0.99  
% 2.25/0.99  
% 2.25/0.99  clauses                                 10
% 2.25/0.99  conjectures                             3
% 2.25/0.99  EPR                                     0
% 2.25/0.99  Horn                                    9
% 2.25/0.99  unary                                   5
% 2.25/0.99  binary                                  4
% 2.25/0.99  lits                                    16
% 2.25/0.99  lits eq                                 9
% 2.25/0.99  fd_pure                                 0
% 2.25/0.99  fd_pseudo                               0
% 2.25/0.99  fd_cond                                 0
% 2.25/0.99  fd_pseudo_cond                          0
% 2.25/0.99  AC symbols                              0
% 2.25/0.99  
% 2.25/0.99  ------ Schedule dynamic 5 is on 
% 2.25/0.99  
% 2.25/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.25/0.99  
% 2.25/0.99  
% 2.25/0.99  ------ 
% 2.25/0.99  Current options:
% 2.25/0.99  ------ 
% 2.25/0.99  
% 2.25/0.99  ------ Input Options
% 2.25/0.99  
% 2.25/0.99  --out_options                           all
% 2.25/0.99  --tptp_safe_out                         true
% 2.25/0.99  --problem_path                          ""
% 2.25/0.99  --include_path                          ""
% 2.25/0.99  --clausifier                            res/vclausify_rel
% 2.25/0.99  --clausifier_options                    --mode clausify
% 2.25/0.99  --stdin                                 false
% 2.25/0.99  --stats_out                             all
% 2.25/0.99  
% 2.25/0.99  ------ General Options
% 2.25/0.99  
% 2.25/0.99  --fof                                   false
% 2.25/0.99  --time_out_real                         305.
% 2.25/0.99  --time_out_virtual                      -1.
% 2.25/0.99  --symbol_type_check                     false
% 2.25/0.99  --clausify_out                          false
% 2.25/0.99  --sig_cnt_out                           false
% 2.25/0.99  --trig_cnt_out                          false
% 2.25/0.99  --trig_cnt_out_tolerance                1.
% 2.25/0.99  --trig_cnt_out_sk_spl                   false
% 2.25/0.99  --abstr_cl_out                          false
% 2.25/0.99  
% 2.25/0.99  ------ Global Options
% 2.25/0.99  
% 2.25/0.99  --schedule                              default
% 2.25/0.99  --add_important_lit                     false
% 2.25/0.99  --prop_solver_per_cl                    1000
% 2.25/0.99  --min_unsat_core                        false
% 2.25/0.99  --soft_assumptions                      false
% 2.25/0.99  --soft_lemma_size                       3
% 2.25/0.99  --prop_impl_unit_size                   0
% 2.25/0.99  --prop_impl_unit                        []
% 2.25/0.99  --share_sel_clauses                     true
% 2.25/0.99  --reset_solvers                         false
% 2.25/0.99  --bc_imp_inh                            [conj_cone]
% 2.25/0.99  --conj_cone_tolerance                   3.
% 2.25/0.99  --extra_neg_conj                        none
% 2.25/0.99  --large_theory_mode                     true
% 2.25/0.99  --prolific_symb_bound                   200
% 2.25/0.99  --lt_threshold                          2000
% 2.25/0.99  --clause_weak_htbl                      true
% 2.25/0.99  --gc_record_bc_elim                     false
% 2.25/0.99  
% 2.25/0.99  ------ Preprocessing Options
% 2.25/0.99  
% 2.25/0.99  --preprocessing_flag                    true
% 2.25/0.99  --time_out_prep_mult                    0.1
% 2.25/0.99  --splitting_mode                        input
% 2.25/0.99  --splitting_grd                         true
% 2.25/0.99  --splitting_cvd                         false
% 2.25/0.99  --splitting_cvd_svl                     false
% 2.25/0.99  --splitting_nvd                         32
% 2.25/0.99  --sub_typing                            true
% 2.25/0.99  --prep_gs_sim                           true
% 2.25/0.99  --prep_unflatten                        true
% 2.25/0.99  --prep_res_sim                          true
% 2.25/0.99  --prep_upred                            true
% 2.25/0.99  --prep_sem_filter                       exhaustive
% 2.25/0.99  --prep_sem_filter_out                   false
% 2.25/0.99  --pred_elim                             true
% 2.25/0.99  --res_sim_input                         true
% 2.25/0.99  --eq_ax_congr_red                       true
% 2.25/0.99  --pure_diseq_elim                       true
% 2.25/0.99  --brand_transform                       false
% 2.25/0.99  --non_eq_to_eq                          false
% 2.25/0.99  --prep_def_merge                        true
% 2.25/0.99  --prep_def_merge_prop_impl              false
% 2.25/0.99  --prep_def_merge_mbd                    true
% 2.25/0.99  --prep_def_merge_tr_red                 false
% 2.25/0.99  --prep_def_merge_tr_cl                  false
% 2.25/0.99  --smt_preprocessing                     true
% 2.25/0.99  --smt_ac_axioms                         fast
% 2.25/0.99  --preprocessed_out                      false
% 2.25/0.99  --preprocessed_stats                    false
% 2.25/0.99  
% 2.25/0.99  ------ Abstraction refinement Options
% 2.25/0.99  
% 2.25/0.99  --abstr_ref                             []
% 2.25/0.99  --abstr_ref_prep                        false
% 2.25/0.99  --abstr_ref_until_sat                   false
% 2.25/0.99  --abstr_ref_sig_restrict                funpre
% 2.25/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.25/0.99  --abstr_ref_under                       []
% 2.25/0.99  
% 2.25/0.99  ------ SAT Options
% 2.25/0.99  
% 2.25/0.99  --sat_mode                              false
% 2.25/0.99  --sat_fm_restart_options                ""
% 2.25/0.99  --sat_gr_def                            false
% 2.25/0.99  --sat_epr_types                         true
% 2.25/0.99  --sat_non_cyclic_types                  false
% 2.25/0.99  --sat_finite_models                     false
% 2.25/0.99  --sat_fm_lemmas                         false
% 2.25/0.99  --sat_fm_prep                           false
% 2.25/0.99  --sat_fm_uc_incr                        true
% 2.25/0.99  --sat_out_model                         small
% 2.25/0.99  --sat_out_clauses                       false
% 2.25/0.99  
% 2.25/0.99  ------ QBF Options
% 2.25/0.99  
% 2.25/0.99  --qbf_mode                              false
% 2.25/0.99  --qbf_elim_univ                         false
% 2.25/0.99  --qbf_dom_inst                          none
% 2.25/0.99  --qbf_dom_pre_inst                      false
% 2.25/0.99  --qbf_sk_in                             false
% 2.25/0.99  --qbf_pred_elim                         true
% 2.25/0.99  --qbf_split                             512
% 2.25/0.99  
% 2.25/0.99  ------ BMC1 Options
% 2.25/0.99  
% 2.25/0.99  --bmc1_incremental                      false
% 2.25/0.99  --bmc1_axioms                           reachable_all
% 2.25/0.99  --bmc1_min_bound                        0
% 2.25/0.99  --bmc1_max_bound                        -1
% 2.25/0.99  --bmc1_max_bound_default                -1
% 2.25/0.99  --bmc1_symbol_reachability              true
% 2.25/0.99  --bmc1_property_lemmas                  false
% 2.25/0.99  --bmc1_k_induction                      false
% 2.25/0.99  --bmc1_non_equiv_states                 false
% 2.25/0.99  --bmc1_deadlock                         false
% 2.25/0.99  --bmc1_ucm                              false
% 2.25/0.99  --bmc1_add_unsat_core                   none
% 2.25/0.99  --bmc1_unsat_core_children              false
% 2.25/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.25/0.99  --bmc1_out_stat                         full
% 2.25/0.99  --bmc1_ground_init                      false
% 2.25/0.99  --bmc1_pre_inst_next_state              false
% 2.25/0.99  --bmc1_pre_inst_state                   false
% 2.25/0.99  --bmc1_pre_inst_reach_state             false
% 2.25/0.99  --bmc1_out_unsat_core                   false
% 2.25/0.99  --bmc1_aig_witness_out                  false
% 2.25/0.99  --bmc1_verbose                          false
% 2.25/0.99  --bmc1_dump_clauses_tptp                false
% 2.25/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.25/0.99  --bmc1_dump_file                        -
% 2.25/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.25/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.25/0.99  --bmc1_ucm_extend_mode                  1
% 2.25/0.99  --bmc1_ucm_init_mode                    2
% 2.25/0.99  --bmc1_ucm_cone_mode                    none
% 2.25/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.25/0.99  --bmc1_ucm_relax_model                  4
% 2.25/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.25/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.25/0.99  --bmc1_ucm_layered_model                none
% 2.25/0.99  --bmc1_ucm_max_lemma_size               10
% 2.25/0.99  
% 2.25/0.99  ------ AIG Options
% 2.25/0.99  
% 2.25/0.99  --aig_mode                              false
% 2.25/0.99  
% 2.25/0.99  ------ Instantiation Options
% 2.25/0.99  
% 2.25/0.99  --instantiation_flag                    true
% 2.25/0.99  --inst_sos_flag                         false
% 2.25/0.99  --inst_sos_phase                        true
% 2.25/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.25/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.25/0.99  --inst_lit_sel_side                     none
% 2.25/0.99  --inst_solver_per_active                1400
% 2.25/0.99  --inst_solver_calls_frac                1.
% 2.25/0.99  --inst_passive_queue_type               priority_queues
% 2.25/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.25/0.99  --inst_passive_queues_freq              [25;2]
% 2.25/0.99  --inst_dismatching                      true
% 2.25/0.99  --inst_eager_unprocessed_to_passive     true
% 2.25/0.99  --inst_prop_sim_given                   true
% 2.25/0.99  --inst_prop_sim_new                     false
% 2.25/0.99  --inst_subs_new                         false
% 2.25/0.99  --inst_eq_res_simp                      false
% 2.25/0.99  --inst_subs_given                       false
% 2.25/0.99  --inst_orphan_elimination               true
% 2.25/0.99  --inst_learning_loop_flag               true
% 2.25/0.99  --inst_learning_start                   3000
% 2.25/0.99  --inst_learning_factor                  2
% 2.25/0.99  --inst_start_prop_sim_after_learn       3
% 2.25/0.99  --inst_sel_renew                        solver
% 2.25/0.99  --inst_lit_activity_flag                true
% 2.25/0.99  --inst_restr_to_given                   false
% 2.25/0.99  --inst_activity_threshold               500
% 2.25/0.99  --inst_out_proof                        true
% 2.25/0.99  
% 2.25/0.99  ------ Resolution Options
% 2.25/0.99  
% 2.25/0.99  --resolution_flag                       false
% 2.25/0.99  --res_lit_sel                           adaptive
% 2.25/0.99  --res_lit_sel_side                      none
% 2.25/0.99  --res_ordering                          kbo
% 2.25/0.99  --res_to_prop_solver                    active
% 2.25/0.99  --res_prop_simpl_new                    false
% 2.25/0.99  --res_prop_simpl_given                  true
% 2.25/0.99  --res_passive_queue_type                priority_queues
% 2.25/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.25/0.99  --res_passive_queues_freq               [15;5]
% 2.25/0.99  --res_forward_subs                      full
% 2.25/0.99  --res_backward_subs                     full
% 2.25/0.99  --res_forward_subs_resolution           true
% 2.25/0.99  --res_backward_subs_resolution          true
% 2.25/0.99  --res_orphan_elimination                true
% 2.25/0.99  --res_time_limit                        2.
% 2.25/0.99  --res_out_proof                         true
% 2.25/0.99  
% 2.25/0.99  ------ Superposition Options
% 2.25/0.99  
% 2.25/0.99  --superposition_flag                    true
% 2.25/0.99  --sup_passive_queue_type                priority_queues
% 2.25/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.25/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.25/0.99  --demod_completeness_check              fast
% 2.25/0.99  --demod_use_ground                      true
% 2.25/0.99  --sup_to_prop_solver                    passive
% 2.25/0.99  --sup_prop_simpl_new                    true
% 2.25/0.99  --sup_prop_simpl_given                  true
% 2.25/0.99  --sup_fun_splitting                     false
% 2.25/0.99  --sup_smt_interval                      50000
% 2.25/0.99  
% 2.25/0.99  ------ Superposition Simplification Setup
% 2.25/0.99  
% 2.25/0.99  --sup_indices_passive                   []
% 2.25/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.25/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.99  --sup_full_bw                           [BwDemod]
% 2.25/0.99  --sup_immed_triv                        [TrivRules]
% 2.25/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.25/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.99  --sup_immed_bw_main                     []
% 2.25/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.25/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.25/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.25/0.99  
% 2.25/0.99  ------ Combination Options
% 2.25/0.99  
% 2.25/0.99  --comb_res_mult                         3
% 2.25/0.99  --comb_sup_mult                         2
% 2.25/0.99  --comb_inst_mult                        10
% 2.25/0.99  
% 2.25/0.99  ------ Debug Options
% 2.25/0.99  
% 2.25/0.99  --dbg_backtrace                         false
% 2.25/0.99  --dbg_dump_prop_clauses                 false
% 2.25/0.99  --dbg_dump_prop_clauses_file            -
% 2.25/0.99  --dbg_out_stat                          false
% 2.25/0.99  
% 2.25/0.99  
% 2.25/0.99  
% 2.25/0.99  
% 2.25/0.99  ------ Proving...
% 2.25/0.99  
% 2.25/0.99  
% 2.25/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 2.25/0.99  
% 2.25/0.99  % SZS output start Saturation for theBenchmark.p
% 2.25/0.99  
% 2.25/0.99  fof(f5,axiom,(
% 2.25/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f28,plain,(
% 2.25/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.25/0.99    inference(cnf_transformation,[],[f5])).
% 2.25/0.99  
% 2.25/0.99  fof(f7,axiom,(
% 2.25/0.99    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f30,plain,(
% 2.25/0.99    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 2.25/0.99    inference(cnf_transformation,[],[f7])).
% 2.25/0.99  
% 2.25/0.99  fof(f3,axiom,(
% 2.25/0.99    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f26,plain,(
% 2.25/0.99    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 2.25/0.99    inference(cnf_transformation,[],[f3])).
% 2.25/0.99  
% 2.25/0.99  fof(f42,plain,(
% 2.25/0.99    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 2.25/0.99    inference(definition_unfolding,[],[f30,f26])).
% 2.25/0.99  
% 2.25/0.99  fof(f45,plain,(
% 2.25/0.99    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 2.25/0.99    inference(definition_unfolding,[],[f28,f42])).
% 2.25/0.99  
% 2.25/0.99  fof(f4,axiom,(
% 2.25/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f27,plain,(
% 2.25/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.25/0.99    inference(cnf_transformation,[],[f4])).
% 2.25/0.99  
% 2.25/0.99  fof(f44,plain,(
% 2.25/0.99    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 2.25/0.99    inference(definition_unfolding,[],[f27,f42])).
% 2.25/0.99  
% 2.25/0.99  fof(f8,axiom,(
% 2.25/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)))),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f18,plain,(
% 2.25/0.99    ! [X0,X1] : (! [X2] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.25/0.99    inference(ennf_transformation,[],[f8])).
% 2.25/0.99  
% 2.25/0.99  fof(f31,plain,(
% 2.25/0.99    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.25/0.99    inference(cnf_transformation,[],[f18])).
% 2.25/0.99  
% 2.25/0.99  fof(f13,conjecture,(
% 2.25/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1))))),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f14,negated_conjecture,(
% 2.25/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1))))),
% 2.25/0.99    inference(negated_conjecture,[],[f13])).
% 2.25/0.99  
% 2.25/0.99  fof(f20,plain,(
% 2.25/0.99    ? [X0] : (? [X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_struct_0(X0))),
% 2.25/0.99    inference(ennf_transformation,[],[f14])).
% 2.25/0.99  
% 2.25/0.99  fof(f22,plain,(
% 2.25/0.99    ( ! [X0] : (? [X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (((k2_struct_0(X0) = sK1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1) & k2_struct_0(X0) != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.25/0.99    introduced(choice_axiom,[])).
% 2.25/0.99  
% 2.25/0.99  fof(f21,plain,(
% 2.25/0.99    ? [X0] : (? [X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_struct_0(X0)) => (? [X1] : (((k2_struct_0(sK0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) & k2_struct_0(sK0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_struct_0(sK0))),
% 2.25/0.99    introduced(choice_axiom,[])).
% 2.25/0.99  
% 2.25/0.99  fof(f23,plain,(
% 2.25/0.99    (((k2_struct_0(sK0) = sK1 & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) & k2_struct_0(sK0) != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_struct_0(sK0)),
% 2.25/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).
% 2.25/0.99  
% 2.25/0.99  fof(f36,plain,(
% 2.25/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.25/0.99    inference(cnf_transformation,[],[f23])).
% 2.25/0.99  
% 2.25/0.99  fof(f9,axiom,(
% 2.25/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f32,plain,(
% 2.25/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.25/0.99    inference(cnf_transformation,[],[f9])).
% 2.25/0.99  
% 2.25/0.99  fof(f6,axiom,(
% 2.25/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f17,plain,(
% 2.25/0.99    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.25/0.99    inference(ennf_transformation,[],[f6])).
% 2.25/0.99  
% 2.25/0.99  fof(f29,plain,(
% 2.25/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.25/0.99    inference(cnf_transformation,[],[f17])).
% 2.25/0.99  
% 2.25/0.99  fof(f10,axiom,(
% 2.25/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f33,plain,(
% 2.25/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.25/0.99    inference(cnf_transformation,[],[f10])).
% 2.25/0.99  
% 2.25/0.99  fof(f2,axiom,(
% 2.25/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f25,plain,(
% 2.25/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.25/0.99    inference(cnf_transformation,[],[f2])).
% 2.25/0.99  
% 2.25/0.99  fof(f41,plain,(
% 2.25/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 2.25/0.99    inference(definition_unfolding,[],[f33,f25])).
% 2.25/0.99  
% 2.25/0.99  fof(f46,plain,(
% 2.25/0.99    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k1_enumset1(X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.25/0.99    inference(definition_unfolding,[],[f29,f41])).
% 2.25/0.99  
% 2.25/0.99  fof(f1,axiom,(
% 2.25/0.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f15,plain,(
% 2.25/0.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.25/0.99    inference(rectify,[],[f1])).
% 2.25/0.99  
% 2.25/0.99  fof(f24,plain,(
% 2.25/0.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.25/0.99    inference(cnf_transformation,[],[f15])).
% 2.25/0.99  
% 2.25/0.99  fof(f43,plain,(
% 2.25/0.99    ( ! [X0] : (k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0) )),
% 2.25/0.99    inference(definition_unfolding,[],[f24,f41])).
% 2.25/0.99  
% 2.25/0.99  fof(f40,plain,(
% 2.25/0.99    k2_struct_0(sK0) = sK1 | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 2.25/0.99    inference(cnf_transformation,[],[f23])).
% 2.25/0.99  
% 2.25/0.99  fof(f12,axiom,(
% 2.25/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/1.00  
% 2.25/1.00  fof(f19,plain,(
% 2.25/1.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 2.25/1.00    inference(ennf_transformation,[],[f12])).
% 2.25/1.00  
% 2.25/1.00  fof(f34,plain,(
% 2.25/1.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 2.25/1.00    inference(cnf_transformation,[],[f19])).
% 2.25/1.00  
% 2.25/1.00  fof(f35,plain,(
% 2.25/1.00    l1_struct_0(sK0)),
% 2.25/1.00    inference(cnf_transformation,[],[f23])).
% 2.25/1.00  
% 2.25/1.00  fof(f37,plain,(
% 2.25/1.00    k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | k2_struct_0(sK0) != sK1),
% 2.25/1.00    inference(cnf_transformation,[],[f23])).
% 2.25/1.00  
% 2.25/1.00  cnf(c_109,plain,
% 2.25/1.00      ( ~ l1_struct_0(X0) | l1_struct_0(X1) | X1 != X0 ),
% 2.25/1.00      theory(equality) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_202,plain,( X0_2 = X0_2 ),theory(equality) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_2,plain,
% 2.25/1.00      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
% 2.25/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_406,plain,
% 2.25/1.00      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.25/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_1,plain,
% 2.25/1.00      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 2.25/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_415,plain,
% 2.25/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.25/1.00      inference(light_normalisation,[status(thm)],[c_406,c_1]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_4,plain,
% 2.25/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.25/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.25/1.00      | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
% 2.25/1.00      inference(cnf_transformation,[],[f31]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_404,plain,
% 2.25/1.00      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
% 2.25/1.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 2.25/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.25/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_904,plain,
% 2.25/1.00      ( k9_subset_1(X0,X1,k3_subset_1(X0,X0)) = k7_subset_1(X0,X1,X0)
% 2.25/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.25/1.00      inference(superposition,[status(thm)],[c_415,c_404]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_1966,plain,
% 2.25/1.00      ( k9_subset_1(X0,X0,k3_subset_1(X0,X0)) = k7_subset_1(X0,X0,X0) ),
% 2.25/1.00      inference(superposition,[status(thm)],[c_415,c_904]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_11,negated_conjecture,
% 2.25/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.25/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_402,plain,
% 2.25/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.25/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_1965,plain,
% 2.25/1.00      ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) = k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
% 2.25/1.00      inference(superposition,[status(thm)],[c_402,c_904]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_5,plain,
% 2.25/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.25/1.00      inference(cnf_transformation,[],[f32]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_403,plain,
% 2.25/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.25/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_1964,plain,
% 2.25/1.00      ( k9_subset_1(X0,k1_xboole_0,k3_subset_1(X0,X0)) = k7_subset_1(X0,k1_xboole_0,X0) ),
% 2.25/1.00      inference(superposition,[status(thm)],[c_403,c_904]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_3,plain,
% 2.25/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.25/1.00      | k1_setfam_1(k1_enumset1(X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 2.25/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_405,plain,
% 2.25/1.00      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_subset_1(X2,X0,X1)
% 2.25/1.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 2.25/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_888,plain,
% 2.25/1.00      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_subset_1(X1,X0,X1) ),
% 2.25/1.00      inference(superposition,[status(thm)],[c_415,c_405]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_0,plain,
% 2.25/1.00      ( k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
% 2.25/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_1560,plain,
% 2.25/1.00      ( k9_subset_1(X0,X0,X0) = X0 ),
% 2.25/1.00      inference(superposition,[status(thm)],[c_888,c_0]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_902,plain,
% 2.25/1.00      ( k9_subset_1(X0,X1,k3_subset_1(X0,k1_xboole_0)) = k7_subset_1(X0,X1,k1_xboole_0)
% 2.25/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.25/1.00      inference(superposition,[status(thm)],[c_403,c_404]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_915,plain,
% 2.25/1.00      ( k9_subset_1(X0,X1,X0) = k7_subset_1(X0,X1,k1_xboole_0)
% 2.25/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.25/1.00      inference(light_normalisation,[status(thm)],[c_902,c_1]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_1433,plain,
% 2.25/1.00      ( k9_subset_1(X0,X0,X0) = k7_subset_1(X0,X0,k1_xboole_0) ),
% 2.25/1.00      inference(superposition,[status(thm)],[c_415,c_915]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_1758,plain,
% 2.25/1.00      ( k7_subset_1(X0,X0,k1_xboole_0) = X0 ),
% 2.25/1.00      inference(demodulation,[status(thm)],[c_1560,c_1433]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_1432,plain,
% 2.25/1.00      ( k9_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) ),
% 2.25/1.00      inference(superposition,[status(thm)],[c_402,c_915]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_1563,plain,
% 2.25/1.00      ( k1_setfam_1(k1_enumset1(sK1,sK1,u1_struct_0(sK0))) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) ),
% 2.25/1.00      inference(superposition,[status(thm)],[c_888,c_1432]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_1431,plain,
% 2.25/1.00      ( k9_subset_1(X0,k1_xboole_0,X0) = k7_subset_1(X0,k1_xboole_0,k1_xboole_0) ),
% 2.25/1.00      inference(superposition,[status(thm)],[c_403,c_915]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_1562,plain,
% 2.25/1.00      ( k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = k7_subset_1(X0,k1_xboole_0,k1_xboole_0) ),
% 2.25/1.00      inference(superposition,[status(thm)],[c_888,c_1431]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_887,plain,
% 2.25/1.00      ( k1_setfam_1(k1_enumset1(X0,X0,sK1)) = k9_subset_1(u1_struct_0(sK0),X0,sK1) ),
% 2.25/1.00      inference(superposition,[status(thm)],[c_402,c_405]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_1554,plain,
% 2.25/1.00      ( k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(sK1,X0,sK1) ),
% 2.25/1.00      inference(demodulation,[status(thm)],[c_888,c_887]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_886,plain,
% 2.25/1.00      ( k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0)) = k9_subset_1(X1,X0,k1_xboole_0) ),
% 2.25/1.00      inference(superposition,[status(thm)],[c_403,c_405]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_1310,plain,
% 2.25/1.00      ( k9_subset_1(X0,X1,k1_xboole_0) = k9_subset_1(X2,X1,k1_xboole_0) ),
% 2.25/1.00      inference(superposition,[status(thm)],[c_886,c_886]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_1309,plain,
% 2.25/1.00      ( k9_subset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.25/1.00      inference(superposition,[status(thm)],[c_886,c_0]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_7,negated_conjecture,
% 2.25/1.00      ( k2_struct_0(sK0) = sK1
% 2.25/1.00      | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
% 2.25/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_6,plain,
% 2.25/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.25/1.00      | ~ l1_struct_0(X1)
% 2.25/1.00      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0 ),
% 2.25/1.00      inference(cnf_transformation,[],[f34]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_12,negated_conjecture,
% 2.25/1.00      ( l1_struct_0(sK0) ),
% 2.25/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_117,plain,
% 2.25/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.25/1.00      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0
% 2.25/1.00      | sK0 != X1 ),
% 2.25/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_12]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_118,plain,
% 2.25/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.25/1.00      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 ),
% 2.25/1.00      inference(unflattening,[status(thm)],[c_117]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_401,plain,
% 2.25/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0
% 2.25/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.25/1.00      inference(predicate_to_equality,[status(thm)],[c_118]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_497,plain,
% 2.25/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1 ),
% 2.25/1.00      inference(superposition,[status(thm)],[c_402,c_401]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_603,plain,
% 2.25/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) = sK1
% 2.25/1.00      | k2_struct_0(sK0) = sK1 ),
% 2.25/1.00      inference(superposition,[status(thm)],[c_7,c_497]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_654,plain,
% 2.25/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)) = k1_xboole_0 ),
% 2.25/1.00      inference(superposition,[status(thm)],[c_403,c_401]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_1050,plain,
% 2.25/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_xboole_0
% 2.25/1.00      | k2_struct_0(sK0) = sK1 ),
% 2.25/1.00      inference(superposition,[status(thm)],[c_603,c_654]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_903,plain,
% 2.25/1.00      ( k9_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),X0,sK1)
% 2.25/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.25/1.00      inference(superposition,[status(thm)],[c_402,c_404]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_990,plain,
% 2.25/1.00      ( k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
% 2.25/1.00      inference(superposition,[status(thm)],[c_415,c_903]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_989,plain,
% 2.25/1.00      ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),sK1,sK1) ),
% 2.25/1.00      inference(superposition,[status(thm)],[c_402,c_903]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_988,plain,
% 2.25/1.00      ( k9_subset_1(u1_struct_0(sK0),k1_xboole_0,k3_subset_1(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) ),
% 2.25/1.00      inference(superposition,[status(thm)],[c_403,c_903]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_718,plain,
% 2.25/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) = u1_struct_0(sK0) ),
% 2.25/1.00      inference(superposition,[status(thm)],[c_415,c_401]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_10,negated_conjecture,
% 2.25/1.00      ( k2_struct_0(sK0) != sK1
% 2.25/1.00      | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
% 2.25/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.25/1.00  
% 2.25/1.00  
% 2.25/1.00  % SZS output end Saturation for theBenchmark.p
% 2.25/1.00  
% 2.25/1.00  ------                               Statistics
% 2.25/1.00  
% 2.25/1.00  ------ General
% 2.25/1.00  
% 2.25/1.00  abstr_ref_over_cycles:                  0
% 2.25/1.00  abstr_ref_under_cycles:                 0
% 2.25/1.00  gc_basic_clause_elim:                   0
% 2.25/1.00  forced_gc_time:                         0
% 2.25/1.00  parsing_time:                           0.009
% 2.25/1.00  unif_index_cands_time:                  0.
% 2.25/1.00  unif_index_add_time:                    0.
% 2.25/1.00  orderings_time:                         0.
% 2.25/1.00  out_proof_time:                         0.
% 2.25/1.00  total_time:                             0.114
% 2.25/1.00  num_of_symbols:                         44
% 2.25/1.00  num_of_terms:                           1964
% 2.25/1.00  
% 2.25/1.00  ------ Preprocessing
% 2.25/1.00  
% 2.25/1.00  num_of_splits:                          0
% 2.25/1.00  num_of_split_atoms:                     0
% 2.25/1.00  num_of_reused_defs:                     0
% 2.25/1.00  num_eq_ax_congr_red:                    18
% 2.25/1.00  num_of_sem_filtered_clauses:            1
% 2.25/1.00  num_of_subtypes:                        0
% 2.25/1.00  monotx_restored_types:                  0
% 2.25/1.00  sat_num_of_epr_types:                   0
% 2.25/1.00  sat_num_of_non_cyclic_types:            0
% 2.25/1.00  sat_guarded_non_collapsed_types:        0
% 2.25/1.00  num_pure_diseq_elim:                    0
% 2.25/1.00  simp_replaced_by:                       0
% 2.25/1.00  res_preprocessed:                       62
% 2.25/1.00  prep_upred:                             0
% 2.25/1.00  prep_unflattend:                        1
% 2.25/1.00  smt_new_axioms:                         0
% 2.25/1.00  pred_elim_cands:                        1
% 2.25/1.00  pred_elim:                              1
% 2.25/1.00  pred_elim_cl:                           1
% 2.25/1.00  pred_elim_cycles:                       3
% 2.25/1.00  merged_defs:                            8
% 2.25/1.00  merged_defs_ncl:                        0
% 2.25/1.00  bin_hyper_res:                          8
% 2.25/1.00  prep_cycles:                            4
% 2.25/1.00  pred_elim_time:                         0.001
% 2.25/1.00  splitting_time:                         0.
% 2.25/1.00  sem_filter_time:                        0.
% 2.25/1.00  monotx_time:                            0.
% 2.25/1.00  subtype_inf_time:                       0.
% 2.25/1.00  
% 2.25/1.00  ------ Problem properties
% 2.25/1.00  
% 2.25/1.00  clauses:                                10
% 2.25/1.00  conjectures:                            3
% 2.25/1.00  epr:                                    0
% 2.25/1.00  horn:                                   9
% 2.25/1.00  ground:                                 3
% 2.25/1.00  unary:                                  5
% 2.25/1.00  binary:                                 4
% 2.25/1.00  lits:                                   16
% 2.25/1.00  lits_eq:                                9
% 2.25/1.00  fd_pure:                                0
% 2.25/1.00  fd_pseudo:                              0
% 2.25/1.00  fd_cond:                                0
% 2.25/1.00  fd_pseudo_cond:                         0
% 2.25/1.00  ac_symbols:                             0
% 2.25/1.00  
% 2.25/1.00  ------ Propositional Solver
% 2.25/1.00  
% 2.25/1.00  prop_solver_calls:                      27
% 2.25/1.00  prop_fast_solver_calls:                 280
% 2.25/1.00  smt_solver_calls:                       0
% 2.25/1.00  smt_fast_solver_calls:                  0
% 2.25/1.00  prop_num_of_clauses:                    865
% 2.25/1.00  prop_preprocess_simplified:             2310
% 2.25/1.00  prop_fo_subsumed:                       0
% 2.25/1.00  prop_solver_time:                       0.
% 2.25/1.00  smt_solver_time:                        0.
% 2.25/1.00  smt_fast_solver_time:                   0.
% 2.25/1.00  prop_fast_solver_time:                  0.
% 2.25/1.00  prop_unsat_core_time:                   0.
% 2.25/1.00  
% 2.25/1.00  ------ QBF
% 2.25/1.00  
% 2.25/1.00  qbf_q_res:                              0
% 2.25/1.00  qbf_num_tautologies:                    0
% 2.25/1.00  qbf_prep_cycles:                        0
% 2.25/1.00  
% 2.25/1.00  ------ BMC1
% 2.25/1.00  
% 2.25/1.00  bmc1_current_bound:                     -1
% 2.25/1.00  bmc1_last_solved_bound:                 -1
% 2.25/1.00  bmc1_unsat_core_size:                   -1
% 2.25/1.00  bmc1_unsat_core_parents_size:           -1
% 2.25/1.00  bmc1_merge_next_fun:                    0
% 2.25/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.25/1.00  
% 2.25/1.00  ------ Instantiation
% 2.25/1.00  
% 2.25/1.00  inst_num_of_clauses:                    326
% 2.25/1.00  inst_num_in_passive:                    19
% 2.25/1.00  inst_num_in_active:                     175
% 2.25/1.00  inst_num_in_unprocessed:                132
% 2.25/1.00  inst_num_of_loops:                      190
% 2.25/1.00  inst_num_of_learning_restarts:          0
% 2.25/1.00  inst_num_moves_active_passive:          12
% 2.25/1.00  inst_lit_activity:                      0
% 2.25/1.00  inst_lit_activity_moves:                0
% 2.25/1.00  inst_num_tautologies:                   0
% 2.25/1.00  inst_num_prop_implied:                  0
% 2.25/1.00  inst_num_existing_simplified:           0
% 2.25/1.00  inst_num_eq_res_simplified:             0
% 2.25/1.00  inst_num_child_elim:                    0
% 2.25/1.00  inst_num_of_dismatching_blockings:      171
% 2.25/1.00  inst_num_of_non_proper_insts:           294
% 2.25/1.00  inst_num_of_duplicates:                 0
% 2.25/1.00  inst_inst_num_from_inst_to_res:         0
% 2.25/1.00  inst_dismatching_checking_time:         0.
% 2.25/1.00  
% 2.25/1.00  ------ Resolution
% 2.25/1.00  
% 2.25/1.00  res_num_of_clauses:                     0
% 2.25/1.00  res_num_in_passive:                     0
% 2.25/1.00  res_num_in_active:                      0
% 2.25/1.00  res_num_of_loops:                       66
% 2.25/1.00  res_forward_subset_subsumed:            46
% 2.25/1.00  res_backward_subset_subsumed:           0
% 2.25/1.00  res_forward_subsumed:                   0
% 2.25/1.00  res_backward_subsumed:                  0
% 2.25/1.00  res_forward_subsumption_resolution:     0
% 2.25/1.00  res_backward_subsumption_resolution:    0
% 2.25/1.00  res_clause_to_clause_subsumption:       91
% 2.25/1.00  res_orphan_elimination:                 0
% 2.25/1.00  res_tautology_del:                      38
% 2.25/1.00  res_num_eq_res_simplified:              0
% 2.25/1.00  res_num_sel_changes:                    0
% 2.25/1.00  res_moves_from_active_to_pass:          0
% 2.25/1.00  
% 2.25/1.00  ------ Superposition
% 2.25/1.00  
% 2.25/1.00  sup_time_total:                         0.
% 2.25/1.00  sup_time_generating:                    0.
% 2.25/1.00  sup_time_sim_full:                      0.
% 2.25/1.00  sup_time_sim_immed:                     0.
% 2.25/1.00  
% 2.25/1.00  sup_num_of_clauses:                     36
% 2.25/1.00  sup_num_in_active:                      35
% 2.25/1.00  sup_num_in_passive:                     1
% 2.25/1.00  sup_num_of_loops:                       37
% 2.25/1.00  sup_fw_superposition:                   41
% 2.25/1.00  sup_bw_superposition:                   26
% 2.25/1.00  sup_immediate_simplified:               7
% 2.25/1.00  sup_given_eliminated:                   0
% 2.25/1.00  comparisons_done:                       0
% 2.25/1.00  comparisons_avoided:                    3
% 2.25/1.00  
% 2.25/1.00  ------ Simplifications
% 2.25/1.00  
% 2.25/1.00  
% 2.25/1.00  sim_fw_subset_subsumed:                 0
% 2.25/1.00  sim_bw_subset_subsumed:                 0
% 2.25/1.00  sim_fw_subsumed:                        5
% 2.25/1.00  sim_bw_subsumed:                        0
% 2.25/1.00  sim_fw_subsumption_res:                 0
% 2.25/1.00  sim_bw_subsumption_res:                 0
% 2.25/1.00  sim_tautology_del:                      1
% 2.25/1.00  sim_eq_tautology_del:                   1
% 2.25/1.00  sim_eq_res_simp:                        0
% 2.25/1.00  sim_fw_demodulated:                     1
% 2.25/1.00  sim_bw_demodulated:                     2
% 2.25/1.00  sim_light_normalised:                   3
% 2.25/1.00  sim_joinable_taut:                      0
% 2.25/1.00  sim_joinable_simp:                      0
% 2.25/1.00  sim_ac_normalised:                      0
% 2.25/1.00  sim_smt_subsumption:                    0
% 2.25/1.00  
%------------------------------------------------------------------------------
