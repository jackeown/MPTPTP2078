%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:09 EST 2020

% Result     : CounterSatisfiable 1.53s
% Output     : Saturation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  261 (17706 expanded)
%              Number of clauses        :  204 (5095 expanded)
%              Number of leaves         :   20 (4794 expanded)
%              Depth                    :   24
%              Number of atoms          :  350 (31433 expanded)
%              Number of equality atoms :  272 (20509 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f39,f34])).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) ),
    inference(definition_unfolding,[],[f38,f34,f34,f52])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f41,f52])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f37,f34])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f45,f34])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f15])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f16,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_xboole_0(X1,X2)
                  & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
               => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_xboole_0(X1,X2)
                    & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
                 => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f20,plain,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( r1_xboole_0(X1,X2)
                & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
             => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(flattening,[],[f27])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != sK2
        & r1_xboole_0(X1,sK2)
        & k4_subset_1(u1_struct_0(X0),X1,sK2) = k2_struct_0(X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
            & r1_xboole_0(X1,X2)
            & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
   => ( ? [X2] :
          ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != X2
          & r1_xboole_0(sK1,X2)
          & k4_subset_1(u1_struct_0(sK0),sK1,X2) = k2_struct_0(sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2
    & r1_xboole_0(sK1,sK2)
    & k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f30,f29])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f44,f52])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_108,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_196,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_6,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_5,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_359,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_5,c_7])).

cnf(c_1391,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_3,c_359])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_340,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4,c_3])).

cnf(c_1409,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1391,c_3,c_340])).

cnf(c_1418,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_1409])).

cnf(c_2013,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1418,c_340])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1389,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(X1,k3_tarski(k2_tarski(X0,X1)))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_359])).

cnf(c_9,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_324,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_335,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_324,c_8])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_322,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1140,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_335,c_322])).

cnf(c_3537,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(X1,k3_tarski(k2_tarski(X0,X1)))) = k7_subset_1(X0,X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1389,c_1140])).

cnf(c_1977,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_1140])).

cnf(c_3554,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_3537,c_1977])).

cnf(c_7251,plain,
    ( k7_subset_1(X0,X0,X0) = k7_subset_1(k1_xboole_0,k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2013,c_3554])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_132,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_xboole_0(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_12,c_2])).

cnf(c_319,plain,
    ( k3_xboole_0(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_132])).

cnf(c_1083,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_335,c_319])).

cnf(c_1984,plain,
    ( k7_subset_1(X0,X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1083,c_1140])).

cnf(c_649,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_1981,plain,
    ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_649,c_1140])).

cnf(c_1996,plain,
    ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1981,c_340])).

cnf(c_7279,plain,
    ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7251,c_1984,c_1996])).

cnf(c_1396,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_359,c_7])).

cnf(c_1398,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_1396,c_7])).

cnf(c_3162,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_1398])).

cnf(c_7255,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_3162,c_3554])).

cnf(c_7280,plain,
    ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7279,c_7255])).

cnf(c_1962,plain,
    ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_1140,c_7])).

cnf(c_10299,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7280,c_1962])).

cnf(c_10301,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_10299,c_340])).

cnf(c_11202,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_10301])).

cnf(c_3164,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_1398,c_1398])).

cnf(c_9927,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_6,c_3164])).

cnf(c_911,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k3_tarski(k2_tarski(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_649,c_7])).

cnf(c_914,plain,
    ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(demodulation,[status(thm)],[c_911,c_340])).

cnf(c_4499,plain,
    ( k3_tarski(k2_tarski(X0,X0)) = k3_tarski(k2_tarski(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_914,c_3162])).

cnf(c_4500,plain,
    ( k3_tarski(k2_tarski(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4499,c_914])).

cnf(c_9981,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_9927,c_4500])).

cnf(c_10106,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_9981])).

cnf(c_10697,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_10106])).

cnf(c_10714,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_10106,c_1398])).

cnf(c_3549,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X1,X0)),k3_tarski(k2_tarski(X0,X1)))) = k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1398,c_3537])).

cnf(c_7529,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),X0)) = k7_subset_1(k1_xboole_0,k1_xboole_0,k3_tarski(k2_tarski(X0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_2013,c_3549])).

cnf(c_7577,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7529,c_914,c_1083,c_1996])).

cnf(c_7541,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k7_subset_1(X1,X1,k3_tarski(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_6,c_3549])).

cnf(c_7548,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1))) = k7_subset_1(X1,X1,k3_tarski(k2_tarski(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_7541,c_1083,c_1140])).

cnf(c_7578,plain,
    ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7577,c_7548])).

cnf(c_1961,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k7_subset_1(X0,X0,X1) ),
    inference(demodulation,[status(thm)],[c_1140,c_359])).

cnf(c_4877,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1398,c_1961])).

cnf(c_10656,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7578,c_4877])).

cnf(c_9896,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X0)) ),
    inference(superposition,[status(thm)],[c_6,c_3164])).

cnf(c_10269,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_9896,c_9981])).

cnf(c_9915,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X0)) ),
    inference(superposition,[status(thm)],[c_6,c_3164])).

cnf(c_10231,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_9915,c_9981])).

cnf(c_7735,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1))) = k7_subset_1(X1,X1,k3_tarski(k2_tarski(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_7541,c_1083,c_1140])).

cnf(c_8033,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1))) = k7_subset_1(X1,X1,k3_tarski(k2_tarski(X1,X0))) ),
    inference(superposition,[status(thm)],[c_6,c_7735])).

cnf(c_8098,plain,
    ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0))) ),
    inference(superposition,[status(thm)],[c_8033,c_7735])).

cnf(c_10119,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1))))) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_9981,c_8098])).

cnf(c_10151,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10119,c_1398,c_7279])).

cnf(c_10117,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_9981])).

cnf(c_9987,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_9981,c_3164])).

cnf(c_7722,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7529,c_914,c_1083,c_1996])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_321,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_642,plain,
    ( k3_xboole_0(sK2,u1_struct_0(sK0)) = sK2 ),
    inference(superposition,[status(thm)],[c_321,c_319])).

cnf(c_918,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(sK2,sK2)) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK2)) ),
    inference(superposition,[status(thm)],[c_642,c_7])).

cnf(c_8373,plain,
    ( k3_tarski(k2_tarski(u1_struct_0(sK0),sK2)) = k5_xboole_0(u1_struct_0(sK0),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_7722,c_918])).

cnf(c_8393,plain,
    ( k3_tarski(k2_tarski(u1_struct_0(sK0),sK2)) = u1_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_8373,c_340])).

cnf(c_8834,plain,
    ( k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_6,c_8393])).

cnf(c_774,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_7])).

cnf(c_1314,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) ),
    inference(superposition,[status(thm)],[c_642,c_774])).

cnf(c_9118,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)) = u1_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_8834,c_1314])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X2,k5_xboole_0(X0,k3_xboole_0(X0,X2))) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_323,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_362,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_323,c_7])).

cnf(c_4334,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,X0) = k3_tarski(k2_tarski(sK2,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_321,c_362])).

cnf(c_4515,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) ),
    inference(superposition,[status(thm)],[c_335,c_4334])).

cnf(c_9117,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_8834,c_4515])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_320,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_643,plain,
    ( k3_xboole_0(sK1,u1_struct_0(sK0)) = sK1 ),
    inference(superposition,[status(thm)],[c_320,c_319])).

cnf(c_988,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(sK1,sK1)) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_643,c_7])).

cnf(c_8375,plain,
    ( k3_tarski(k2_tarski(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_7722,c_988])).

cnf(c_8388,plain,
    ( k3_tarski(k2_tarski(u1_struct_0(sK0),sK1)) = u1_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_8375,c_340])).

cnf(c_8623,plain,
    ( k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_6,c_8388])).

cnf(c_1315,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) ),
    inference(superposition,[status(thm)],[c_643,c_774])).

cnf(c_9100,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) = u1_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_8623,c_1315])).

cnf(c_4335,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_320,c_362])).

cnf(c_4557,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) ),
    inference(superposition,[status(thm)],[c_335,c_4335])).

cnf(c_9099,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_8623,c_4557])).

cnf(c_8838,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k3_xboole_0(u1_struct_0(sK0),sK2)) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_8393,c_1961])).

cnf(c_2247,plain,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k5_xboole_0(u1_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_642,c_1977])).

cnf(c_8855,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k3_xboole_0(u1_struct_0(sK0),sK2)) = k5_xboole_0(u1_struct_0(sK0),sK2) ),
    inference(light_normalisation,[status(thm)],[c_8838,c_2247])).

cnf(c_4336,plain,
    ( k4_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_335,c_362])).

cnf(c_7324,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK2)) ),
    inference(superposition,[status(thm)],[c_321,c_4336])).

cnf(c_8833,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = u1_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_8393,c_7324])).

cnf(c_3552,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(X0,k3_tarski(k2_tarski(X0,X1)))) = k7_subset_1(X1,X1,X0) ),
    inference(superposition,[status(thm)],[c_6,c_3537])).

cnf(c_3590,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k7_subset_1(X1,X1,X0) ),
    inference(superposition,[status(thm)],[c_3552,c_1977])).

cnf(c_8625,plain,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0)) = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_8388,c_3590])).

cnf(c_1983,plain,
    ( k7_subset_1(sK1,sK1,u1_struct_0(sK0)) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_643,c_1140])).

cnf(c_8374,plain,
    ( k7_subset_1(sK1,sK1,u1_struct_0(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7722,c_1983])).

cnf(c_8647,plain,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8625,c_8374])).

cnf(c_8627,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k3_xboole_0(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_8388,c_1961])).

cnf(c_2248,plain,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_643,c_1977])).

cnf(c_8644,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k3_xboole_0(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(light_normalisation,[status(thm)],[c_8627,c_2248])).

cnf(c_7325,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_320,c_4336])).

cnf(c_8622,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = u1_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_8388,c_7325])).

cnf(c_4555,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_tarski(k2_tarski(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_321,c_4335])).

cnf(c_15,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_14,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_126,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_14])).

cnf(c_127,plain,
    ( k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_126])).

cnf(c_1312,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k1_xboole_0)) = k3_tarski(k2_tarski(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_127,c_774])).

cnf(c_777,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k1_xboole_0)) = k3_tarski(k2_tarski(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_127,c_7])).

cnf(c_779,plain,
    ( k3_tarski(k2_tarski(sK2,sK1)) = k5_xboole_0(sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_777,c_340])).

cnf(c_990,plain,
    ( k3_tarski(k2_tarski(sK1,sK2)) = k5_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_6,c_779])).

cnf(c_1322,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k1_xboole_0)) = k5_xboole_0(sK2,sK1) ),
    inference(light_normalisation,[status(thm)],[c_1312,c_990])).

cnf(c_1323,plain,
    ( k5_xboole_0(sK1,sK2) = k5_xboole_0(sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_1322,c_340])).

cnf(c_1838,plain,
    ( k3_tarski(k2_tarski(sK1,sK2)) = k5_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_1323,c_990])).

cnf(c_4563,plain,
    ( k5_xboole_0(sK1,sK2) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_4555,c_15,c_1838])).

cnf(c_1393,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK2,sK1),sK2)) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_990,c_359])).

cnf(c_1403,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK2,sK1),sK2)) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1393,c_127])).

cnf(c_1404,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK2,sK1),sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_1403,c_340])).

cnf(c_1734,plain,
    ( k3_tarski(k2_tarski(sK2,k5_xboole_0(sK2,sK1))) = k5_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_1404,c_7])).

cnf(c_1888,plain,
    ( k3_tarski(k2_tarski(sK2,k5_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_1734,c_1323])).

cnf(c_4652,plain,
    ( k3_tarski(k2_tarski(sK2,k2_struct_0(sK0))) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_4563,c_1888])).

cnf(c_5302,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0))) = k7_subset_1(sK2,sK2,k2_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_4652,c_3537])).

cnf(c_5308,plain,
    ( k7_subset_1(sK2,sK2,k2_struct_0(sK0)) = k5_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(demodulation,[status(thm)],[c_5302,c_1083,c_1140])).

cnf(c_8381,plain,
    ( k7_subset_1(sK2,sK2,k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7722,c_5308])).

cnf(c_4648,plain,
    ( k3_tarski(k2_tarski(sK1,sK2)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_4563,c_1838])).

cnf(c_4769,plain,
    ( k3_tarski(k2_tarski(sK1,k2_struct_0(sK0))) = k3_tarski(k2_tarski(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_4648,c_3162])).

cnf(c_4773,plain,
    ( k3_tarski(k2_tarski(sK1,k2_struct_0(sK0))) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_4769,c_4648])).

cnf(c_5892,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0))) = k7_subset_1(sK1,sK1,k2_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_4773,c_3537])).

cnf(c_5898,plain,
    ( k7_subset_1(sK1,sK1,k2_struct_0(sK0)) = k5_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(demodulation,[status(thm)],[c_5892,c_1083,c_1140])).

cnf(c_8379,plain,
    ( k7_subset_1(sK1,sK1,k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7722,c_5898])).

cnf(c_1982,plain,
    ( k7_subset_1(sK2,sK2,u1_struct_0(sK0)) = k5_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_642,c_1140])).

cnf(c_8372,plain,
    ( k7_subset_1(sK2,sK2,u1_struct_0(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7722,c_1982])).

cnf(c_7326,plain,
    ( k4_subset_1(X0,X0,X0) = k3_tarski(k2_tarski(X0,X0)) ),
    inference(superposition,[status(thm)],[c_335,c_4336])).

cnf(c_7729,plain,
    ( k4_subset_1(X0,X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7326,c_4500])).

cnf(c_7581,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X1,X0)),k3_tarski(k2_tarski(X0,X1)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7578,c_3549])).

cnf(c_4556,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_320,c_4335])).

cnf(c_7416,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_4500,c_4556])).

cnf(c_4513,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_321,c_4334])).

cnf(c_7415,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_4500,c_4513])).

cnf(c_5894,plain,
    ( k3_tarski(k2_tarski(k2_struct_0(sK0),k2_struct_0(sK0))) = k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_4773,c_1398])).

cnf(c_5304,plain,
    ( k3_tarski(k2_tarski(k2_struct_0(sK0),k2_struct_0(sK0))) = k3_tarski(k2_tarski(k2_struct_0(sK0),sK2)) ),
    inference(superposition,[status(thm)],[c_4652,c_1398])).

cnf(c_6965,plain,
    ( k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)) = k3_tarski(k2_tarski(k2_struct_0(sK0),sK2)) ),
    inference(demodulation,[status(thm)],[c_5894,c_5304])).

cnf(c_6983,plain,
    ( k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)) = k3_tarski(k2_tarski(sK2,k2_struct_0(sK0))) ),
    inference(superposition,[status(thm)],[c_6,c_6965])).

cnf(c_7013,plain,
    ( k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_6983,c_4652])).

cnf(c_7153,plain,
    ( k3_tarski(k2_tarski(k2_struct_0(sK0),k2_struct_0(sK0))) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_7013,c_5894])).

cnf(c_7019,plain,
    ( k3_tarski(k2_tarski(k2_struct_0(sK0),sK2)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_7013,c_6965])).

cnf(c_4514,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k3_tarski(k2_tarski(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_320,c_4334])).

cnf(c_1839,plain,
    ( k3_tarski(k2_tarski(sK2,sK1)) = k5_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_1323,c_779])).

cnf(c_4519,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k5_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_4514,c_1839])).

cnf(c_6331,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_4519,c_4563])).

cnf(c_776,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) = k3_tarski(k2_tarski(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_3,c_7])).

cnf(c_782,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_776,c_340])).

cnf(c_5179,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_782,c_2013])).

cnf(c_4654,plain,
    ( k5_xboole_0(sK2,sK1) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_4563,c_1323])).

cnf(c_4653,plain,
    ( k3_tarski(k2_tarski(sK2,sK1)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_4563,c_1839])).

cnf(c_1732,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(sK2,k5_xboole_0(sK2,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_0,c_1404])).

cnf(c_2257,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1732,c_1323])).

cnf(c_4651,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(sK2,k2_struct_0(sK0))) = sK1 ),
    inference(demodulation,[status(thm)],[c_4563,c_2257])).

cnf(c_1837,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_1323,c_1404])).

cnf(c_4650,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(k2_struct_0(sK0),sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_4563,c_1837])).

cnf(c_3548,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k7_subset_1(sK2,sK2,sK1) ),
    inference(superposition,[status(thm)],[c_1839,c_3537])).

cnf(c_2245,plain,
    ( k7_subset_1(sK2,sK2,sK1) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_127,c_1977])).

cnf(c_2255,plain,
    ( k7_subset_1(sK2,sK2,sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_2245,c_340])).

cnf(c_3568,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3548,c_2255])).

cnf(c_4649,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(sK1,k2_struct_0(sK0))) = sK2 ),
    inference(demodulation,[status(thm)],[c_4563,c_3568])).

cnf(c_3739,plain,
    ( k7_subset_1(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2),sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_1977,c_3568])).

cnf(c_4647,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_4563,c_3739])).

cnf(c_1884,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1)) = k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_1839,c_359])).

cnf(c_4159,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1)) = sK2 ),
    inference(demodulation,[status(thm)],[c_1884,c_1140,c_2255])).

cnf(c_4646,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(k2_struct_0(sK0),sK1)) = sK2 ),
    inference(demodulation,[status(thm)],[c_4563,c_4159])).

cnf(c_2259,plain,
    ( k7_subset_1(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2),sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_1977,c_2257])).

cnf(c_4645,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_4563,c_2259])).

cnf(c_1394,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k5_xboole_0(X1,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_359])).

cnf(c_4299,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k7_subset_1(X1,X1,X0) ),
    inference(demodulation,[status(thm)],[c_1394,c_1140])).

cnf(c_1979,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3,c_1140])).

cnf(c_2002,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1979,c_340])).

cnf(c_1980,plain,
    ( k7_subset_1(sK1,sK1,sK2) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_127,c_1140])).

cnf(c_1999,plain,
    ( k7_subset_1(sK1,sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_1980,c_340])).

cnf(c_1139,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_320,c_322])).

cnf(c_1964,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
    inference(demodulation,[status(thm)],[c_1140,c_1139])).

cnf(c_1138,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_321,c_322])).

cnf(c_1963,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0) ),
    inference(demodulation,[status(thm)],[c_1140,c_1138])).

cnf(c_1142,plain,
    ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1140,c_322])).

cnf(c_13,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
    inference(cnf_transformation,[],[f51])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:01:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 1.53/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/1.01  
% 1.53/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.53/1.01  
% 1.53/1.01  ------  iProver source info
% 1.53/1.01  
% 1.53/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.53/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.53/1.01  git: non_committed_changes: false
% 1.53/1.01  git: last_make_outside_of_git: false
% 1.53/1.01  
% 1.53/1.01  ------ 
% 1.53/1.01  
% 1.53/1.01  ------ Input Options
% 1.53/1.01  
% 1.53/1.01  --out_options                           all
% 1.53/1.01  --tptp_safe_out                         true
% 1.53/1.01  --problem_path                          ""
% 1.53/1.01  --include_path                          ""
% 1.53/1.01  --clausifier                            res/vclausify_rel
% 1.53/1.01  --clausifier_options                    --mode clausify
% 1.53/1.01  --stdin                                 false
% 1.53/1.01  --stats_out                             all
% 1.53/1.01  
% 1.53/1.01  ------ General Options
% 1.53/1.01  
% 1.53/1.01  --fof                                   false
% 1.53/1.01  --time_out_real                         305.
% 1.53/1.01  --time_out_virtual                      -1.
% 1.53/1.01  --symbol_type_check                     false
% 1.53/1.01  --clausify_out                          false
% 1.53/1.01  --sig_cnt_out                           false
% 1.53/1.01  --trig_cnt_out                          false
% 1.53/1.01  --trig_cnt_out_tolerance                1.
% 1.53/1.01  --trig_cnt_out_sk_spl                   false
% 1.53/1.01  --abstr_cl_out                          false
% 1.53/1.01  
% 1.53/1.01  ------ Global Options
% 1.53/1.01  
% 1.53/1.01  --schedule                              default
% 1.53/1.01  --add_important_lit                     false
% 1.53/1.01  --prop_solver_per_cl                    1000
% 1.53/1.01  --min_unsat_core                        false
% 1.53/1.01  --soft_assumptions                      false
% 1.53/1.01  --soft_lemma_size                       3
% 1.53/1.01  --prop_impl_unit_size                   0
% 1.53/1.01  --prop_impl_unit                        []
% 1.53/1.01  --share_sel_clauses                     true
% 1.53/1.01  --reset_solvers                         false
% 1.53/1.01  --bc_imp_inh                            [conj_cone]
% 1.53/1.01  --conj_cone_tolerance                   3.
% 1.53/1.01  --extra_neg_conj                        none
% 1.53/1.01  --large_theory_mode                     true
% 1.53/1.01  --prolific_symb_bound                   200
% 1.53/1.01  --lt_threshold                          2000
% 1.53/1.01  --clause_weak_htbl                      true
% 1.53/1.01  --gc_record_bc_elim                     false
% 1.53/1.01  
% 1.53/1.01  ------ Preprocessing Options
% 1.53/1.01  
% 1.53/1.01  --preprocessing_flag                    true
% 1.53/1.01  --time_out_prep_mult                    0.1
% 1.53/1.01  --splitting_mode                        input
% 1.53/1.01  --splitting_grd                         true
% 1.53/1.01  --splitting_cvd                         false
% 1.53/1.01  --splitting_cvd_svl                     false
% 1.53/1.01  --splitting_nvd                         32
% 1.53/1.01  --sub_typing                            true
% 1.53/1.01  --prep_gs_sim                           true
% 1.53/1.01  --prep_unflatten                        true
% 1.53/1.01  --prep_res_sim                          true
% 1.53/1.01  --prep_upred                            true
% 1.53/1.01  --prep_sem_filter                       exhaustive
% 1.53/1.01  --prep_sem_filter_out                   false
% 1.53/1.01  --pred_elim                             true
% 1.53/1.01  --res_sim_input                         true
% 1.53/1.01  --eq_ax_congr_red                       true
% 1.53/1.01  --pure_diseq_elim                       true
% 1.53/1.01  --brand_transform                       false
% 1.53/1.01  --non_eq_to_eq                          false
% 1.53/1.01  --prep_def_merge                        true
% 1.53/1.01  --prep_def_merge_prop_impl              false
% 1.53/1.01  --prep_def_merge_mbd                    true
% 1.53/1.01  --prep_def_merge_tr_red                 false
% 1.53/1.01  --prep_def_merge_tr_cl                  false
% 1.53/1.01  --smt_preprocessing                     true
% 1.53/1.01  --smt_ac_axioms                         fast
% 1.53/1.01  --preprocessed_out                      false
% 1.53/1.01  --preprocessed_stats                    false
% 1.53/1.01  
% 1.53/1.01  ------ Abstraction refinement Options
% 1.53/1.01  
% 1.53/1.01  --abstr_ref                             []
% 1.53/1.01  --abstr_ref_prep                        false
% 1.53/1.01  --abstr_ref_until_sat                   false
% 1.53/1.01  --abstr_ref_sig_restrict                funpre
% 1.53/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.53/1.01  --abstr_ref_under                       []
% 1.53/1.01  
% 1.53/1.01  ------ SAT Options
% 1.53/1.01  
% 1.53/1.01  --sat_mode                              false
% 1.53/1.01  --sat_fm_restart_options                ""
% 1.53/1.01  --sat_gr_def                            false
% 1.53/1.01  --sat_epr_types                         true
% 1.53/1.01  --sat_non_cyclic_types                  false
% 1.53/1.01  --sat_finite_models                     false
% 1.53/1.01  --sat_fm_lemmas                         false
% 1.53/1.01  --sat_fm_prep                           false
% 1.53/1.01  --sat_fm_uc_incr                        true
% 1.53/1.01  --sat_out_model                         small
% 1.53/1.01  --sat_out_clauses                       false
% 1.53/1.01  
% 1.53/1.01  ------ QBF Options
% 1.53/1.01  
% 1.53/1.01  --qbf_mode                              false
% 1.53/1.01  --qbf_elim_univ                         false
% 1.53/1.01  --qbf_dom_inst                          none
% 1.53/1.01  --qbf_dom_pre_inst                      false
% 1.53/1.01  --qbf_sk_in                             false
% 1.53/1.01  --qbf_pred_elim                         true
% 1.53/1.01  --qbf_split                             512
% 1.53/1.01  
% 1.53/1.01  ------ BMC1 Options
% 1.53/1.01  
% 1.53/1.01  --bmc1_incremental                      false
% 1.53/1.01  --bmc1_axioms                           reachable_all
% 1.53/1.01  --bmc1_min_bound                        0
% 1.53/1.01  --bmc1_max_bound                        -1
% 1.53/1.01  --bmc1_max_bound_default                -1
% 1.53/1.01  --bmc1_symbol_reachability              true
% 1.53/1.01  --bmc1_property_lemmas                  false
% 1.53/1.01  --bmc1_k_induction                      false
% 1.53/1.01  --bmc1_non_equiv_states                 false
% 1.53/1.01  --bmc1_deadlock                         false
% 1.53/1.01  --bmc1_ucm                              false
% 1.53/1.01  --bmc1_add_unsat_core                   none
% 1.53/1.01  --bmc1_unsat_core_children              false
% 1.53/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.53/1.01  --bmc1_out_stat                         full
% 1.53/1.01  --bmc1_ground_init                      false
% 1.53/1.01  --bmc1_pre_inst_next_state              false
% 1.53/1.01  --bmc1_pre_inst_state                   false
% 1.53/1.01  --bmc1_pre_inst_reach_state             false
% 1.53/1.01  --bmc1_out_unsat_core                   false
% 1.53/1.01  --bmc1_aig_witness_out                  false
% 1.53/1.01  --bmc1_verbose                          false
% 1.53/1.01  --bmc1_dump_clauses_tptp                false
% 1.53/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.53/1.01  --bmc1_dump_file                        -
% 1.53/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.53/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.53/1.01  --bmc1_ucm_extend_mode                  1
% 1.53/1.01  --bmc1_ucm_init_mode                    2
% 1.53/1.01  --bmc1_ucm_cone_mode                    none
% 1.53/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.53/1.01  --bmc1_ucm_relax_model                  4
% 1.53/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.53/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.53/1.01  --bmc1_ucm_layered_model                none
% 1.53/1.01  --bmc1_ucm_max_lemma_size               10
% 1.53/1.01  
% 1.53/1.01  ------ AIG Options
% 1.53/1.01  
% 1.53/1.01  --aig_mode                              false
% 1.53/1.01  
% 1.53/1.01  ------ Instantiation Options
% 1.53/1.01  
% 1.53/1.01  --instantiation_flag                    true
% 1.53/1.01  --inst_sos_flag                         false
% 1.53/1.01  --inst_sos_phase                        true
% 1.53/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.53/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.53/1.01  --inst_lit_sel_side                     num_symb
% 1.53/1.01  --inst_solver_per_active                1400
% 1.53/1.01  --inst_solver_calls_frac                1.
% 1.53/1.01  --inst_passive_queue_type               priority_queues
% 1.53/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.53/1.01  --inst_passive_queues_freq              [25;2]
% 1.53/1.01  --inst_dismatching                      true
% 1.53/1.01  --inst_eager_unprocessed_to_passive     true
% 1.53/1.01  --inst_prop_sim_given                   true
% 1.53/1.01  --inst_prop_sim_new                     false
% 1.53/1.01  --inst_subs_new                         false
% 1.53/1.01  --inst_eq_res_simp                      false
% 1.53/1.01  --inst_subs_given                       false
% 1.53/1.01  --inst_orphan_elimination               true
% 1.53/1.01  --inst_learning_loop_flag               true
% 1.53/1.01  --inst_learning_start                   3000
% 1.53/1.01  --inst_learning_factor                  2
% 1.53/1.01  --inst_start_prop_sim_after_learn       3
% 1.53/1.01  --inst_sel_renew                        solver
% 1.53/1.01  --inst_lit_activity_flag                true
% 1.53/1.01  --inst_restr_to_given                   false
% 1.53/1.01  --inst_activity_threshold               500
% 1.53/1.01  --inst_out_proof                        true
% 1.53/1.01  
% 1.53/1.01  ------ Resolution Options
% 1.53/1.01  
% 1.53/1.01  --resolution_flag                       true
% 1.53/1.01  --res_lit_sel                           adaptive
% 1.53/1.01  --res_lit_sel_side                      none
% 1.53/1.01  --res_ordering                          kbo
% 1.53/1.01  --res_to_prop_solver                    active
% 1.53/1.01  --res_prop_simpl_new                    false
% 1.53/1.01  --res_prop_simpl_given                  true
% 1.53/1.01  --res_passive_queue_type                priority_queues
% 1.53/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.53/1.01  --res_passive_queues_freq               [15;5]
% 1.53/1.01  --res_forward_subs                      full
% 1.53/1.01  --res_backward_subs                     full
% 1.53/1.01  --res_forward_subs_resolution           true
% 1.53/1.01  --res_backward_subs_resolution          true
% 1.53/1.01  --res_orphan_elimination                true
% 1.53/1.01  --res_time_limit                        2.
% 1.53/1.01  --res_out_proof                         true
% 1.53/1.01  
% 1.53/1.01  ------ Superposition Options
% 1.53/1.01  
% 1.53/1.01  --superposition_flag                    true
% 1.53/1.01  --sup_passive_queue_type                priority_queues
% 1.53/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.53/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.53/1.01  --demod_completeness_check              fast
% 1.53/1.01  --demod_use_ground                      true
% 1.53/1.01  --sup_to_prop_solver                    passive
% 1.53/1.01  --sup_prop_simpl_new                    true
% 1.53/1.01  --sup_prop_simpl_given                  true
% 1.53/1.01  --sup_fun_splitting                     false
% 1.53/1.01  --sup_smt_interval                      50000
% 1.53/1.01  
% 1.53/1.01  ------ Superposition Simplification Setup
% 1.53/1.01  
% 1.53/1.01  --sup_indices_passive                   []
% 1.53/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.53/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/1.01  --sup_full_bw                           [BwDemod]
% 1.53/1.01  --sup_immed_triv                        [TrivRules]
% 1.53/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.53/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/1.01  --sup_immed_bw_main                     []
% 1.53/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.53/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.53/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.53/1.01  
% 1.53/1.01  ------ Combination Options
% 1.53/1.01  
% 1.53/1.01  --comb_res_mult                         3
% 1.53/1.01  --comb_sup_mult                         2
% 1.53/1.01  --comb_inst_mult                        10
% 1.53/1.01  
% 1.53/1.01  ------ Debug Options
% 1.53/1.01  
% 1.53/1.01  --dbg_backtrace                         false
% 1.53/1.01  --dbg_dump_prop_clauses                 false
% 1.53/1.01  --dbg_dump_prop_clauses_file            -
% 1.53/1.01  --dbg_out_stat                          false
% 1.53/1.01  ------ Parsing...
% 1.53/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.53/1.01  
% 1.53/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.53/1.01  
% 1.53/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.53/1.01  
% 1.53/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.53/1.01  ------ Proving...
% 1.53/1.01  ------ Problem Properties 
% 1.53/1.01  
% 1.53/1.01  
% 1.53/1.01  clauses                                 16
% 1.53/1.01  conjectures                             4
% 1.53/1.01  EPR                                     0
% 1.53/1.01  Horn                                    16
% 1.53/1.01  unary                                   13
% 1.53/1.01  binary                                  2
% 1.53/1.01  lits                                    20
% 1.53/1.01  lits eq                                 13
% 1.53/1.01  fd_pure                                 0
% 1.53/1.01  fd_pseudo                               0
% 1.53/1.01  fd_cond                                 0
% 1.53/1.01  fd_pseudo_cond                          0
% 1.53/1.01  AC symbols                              0
% 1.53/1.01  
% 1.53/1.01  ------ Schedule dynamic 5 is on 
% 1.53/1.01  
% 1.53/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.53/1.01  
% 1.53/1.01  
% 1.53/1.01  ------ 
% 1.53/1.01  Current options:
% 1.53/1.01  ------ 
% 1.53/1.01  
% 1.53/1.01  ------ Input Options
% 1.53/1.01  
% 1.53/1.01  --out_options                           all
% 1.53/1.01  --tptp_safe_out                         true
% 1.53/1.01  --problem_path                          ""
% 1.53/1.01  --include_path                          ""
% 1.53/1.01  --clausifier                            res/vclausify_rel
% 1.53/1.01  --clausifier_options                    --mode clausify
% 1.53/1.01  --stdin                                 false
% 1.53/1.01  --stats_out                             all
% 1.53/1.01  
% 1.53/1.01  ------ General Options
% 1.53/1.01  
% 1.53/1.01  --fof                                   false
% 1.53/1.01  --time_out_real                         305.
% 1.53/1.01  --time_out_virtual                      -1.
% 1.53/1.01  --symbol_type_check                     false
% 1.53/1.01  --clausify_out                          false
% 1.53/1.01  --sig_cnt_out                           false
% 1.53/1.01  --trig_cnt_out                          false
% 1.53/1.01  --trig_cnt_out_tolerance                1.
% 1.53/1.01  --trig_cnt_out_sk_spl                   false
% 1.53/1.01  --abstr_cl_out                          false
% 1.53/1.01  
% 1.53/1.01  ------ Global Options
% 1.53/1.01  
% 1.53/1.01  --schedule                              default
% 1.53/1.01  --add_important_lit                     false
% 1.53/1.01  --prop_solver_per_cl                    1000
% 1.53/1.01  --min_unsat_core                        false
% 1.53/1.01  --soft_assumptions                      false
% 1.53/1.01  --soft_lemma_size                       3
% 1.53/1.01  --prop_impl_unit_size                   0
% 1.53/1.01  --prop_impl_unit                        []
% 1.53/1.01  --share_sel_clauses                     true
% 1.53/1.01  --reset_solvers                         false
% 1.53/1.01  --bc_imp_inh                            [conj_cone]
% 1.53/1.01  --conj_cone_tolerance                   3.
% 1.53/1.01  --extra_neg_conj                        none
% 1.53/1.01  --large_theory_mode                     true
% 1.53/1.01  --prolific_symb_bound                   200
% 1.53/1.01  --lt_threshold                          2000
% 1.53/1.01  --clause_weak_htbl                      true
% 1.53/1.01  --gc_record_bc_elim                     false
% 1.53/1.01  
% 1.53/1.01  ------ Preprocessing Options
% 1.53/1.01  
% 1.53/1.01  --preprocessing_flag                    true
% 1.53/1.01  --time_out_prep_mult                    0.1
% 1.53/1.01  --splitting_mode                        input
% 1.53/1.01  --splitting_grd                         true
% 1.53/1.01  --splitting_cvd                         false
% 1.53/1.01  --splitting_cvd_svl                     false
% 1.53/1.01  --splitting_nvd                         32
% 1.53/1.01  --sub_typing                            true
% 1.53/1.01  --prep_gs_sim                           true
% 1.53/1.01  --prep_unflatten                        true
% 1.53/1.01  --prep_res_sim                          true
% 1.53/1.01  --prep_upred                            true
% 1.53/1.01  --prep_sem_filter                       exhaustive
% 1.53/1.01  --prep_sem_filter_out                   false
% 1.53/1.01  --pred_elim                             true
% 1.53/1.01  --res_sim_input                         true
% 1.53/1.01  --eq_ax_congr_red                       true
% 1.53/1.01  --pure_diseq_elim                       true
% 1.53/1.01  --brand_transform                       false
% 1.53/1.01  --non_eq_to_eq                          false
% 1.53/1.01  --prep_def_merge                        true
% 1.53/1.01  --prep_def_merge_prop_impl              false
% 1.53/1.01  --prep_def_merge_mbd                    true
% 1.53/1.01  --prep_def_merge_tr_red                 false
% 1.53/1.01  --prep_def_merge_tr_cl                  false
% 1.53/1.01  --smt_preprocessing                     true
% 1.53/1.01  --smt_ac_axioms                         fast
% 1.53/1.01  --preprocessed_out                      false
% 1.53/1.01  --preprocessed_stats                    false
% 1.53/1.01  
% 1.53/1.01  ------ Abstraction refinement Options
% 1.53/1.01  
% 1.53/1.01  --abstr_ref                             []
% 1.53/1.01  --abstr_ref_prep                        false
% 1.53/1.01  --abstr_ref_until_sat                   false
% 1.53/1.01  --abstr_ref_sig_restrict                funpre
% 1.53/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.53/1.01  --abstr_ref_under                       []
% 1.53/1.01  
% 1.53/1.01  ------ SAT Options
% 1.53/1.01  
% 1.53/1.01  --sat_mode                              false
% 1.53/1.01  --sat_fm_restart_options                ""
% 1.53/1.01  --sat_gr_def                            false
% 1.53/1.01  --sat_epr_types                         true
% 1.53/1.01  --sat_non_cyclic_types                  false
% 1.53/1.01  --sat_finite_models                     false
% 1.53/1.01  --sat_fm_lemmas                         false
% 1.53/1.01  --sat_fm_prep                           false
% 1.53/1.01  --sat_fm_uc_incr                        true
% 1.53/1.01  --sat_out_model                         small
% 1.53/1.01  --sat_out_clauses                       false
% 1.53/1.01  
% 1.53/1.01  ------ QBF Options
% 1.53/1.01  
% 1.53/1.01  --qbf_mode                              false
% 1.53/1.01  --qbf_elim_univ                         false
% 1.53/1.01  --qbf_dom_inst                          none
% 1.53/1.01  --qbf_dom_pre_inst                      false
% 1.53/1.01  --qbf_sk_in                             false
% 1.53/1.01  --qbf_pred_elim                         true
% 1.53/1.01  --qbf_split                             512
% 1.53/1.01  
% 1.53/1.01  ------ BMC1 Options
% 1.53/1.01  
% 1.53/1.01  --bmc1_incremental                      false
% 1.53/1.01  --bmc1_axioms                           reachable_all
% 1.53/1.01  --bmc1_min_bound                        0
% 1.53/1.01  --bmc1_max_bound                        -1
% 1.53/1.01  --bmc1_max_bound_default                -1
% 1.53/1.01  --bmc1_symbol_reachability              true
% 1.53/1.01  --bmc1_property_lemmas                  false
% 1.53/1.01  --bmc1_k_induction                      false
% 1.53/1.01  --bmc1_non_equiv_states                 false
% 1.53/1.01  --bmc1_deadlock                         false
% 1.53/1.01  --bmc1_ucm                              false
% 1.53/1.01  --bmc1_add_unsat_core                   none
% 1.53/1.01  --bmc1_unsat_core_children              false
% 1.53/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.53/1.01  --bmc1_out_stat                         full
% 1.53/1.01  --bmc1_ground_init                      false
% 1.53/1.01  --bmc1_pre_inst_next_state              false
% 1.53/1.01  --bmc1_pre_inst_state                   false
% 1.53/1.01  --bmc1_pre_inst_reach_state             false
% 1.53/1.01  --bmc1_out_unsat_core                   false
% 1.53/1.01  --bmc1_aig_witness_out                  false
% 1.53/1.01  --bmc1_verbose                          false
% 1.53/1.01  --bmc1_dump_clauses_tptp                false
% 1.53/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.53/1.01  --bmc1_dump_file                        -
% 1.53/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.53/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.53/1.01  --bmc1_ucm_extend_mode                  1
% 1.53/1.01  --bmc1_ucm_init_mode                    2
% 1.53/1.01  --bmc1_ucm_cone_mode                    none
% 1.53/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.53/1.01  --bmc1_ucm_relax_model                  4
% 1.53/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.53/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.53/1.01  --bmc1_ucm_layered_model                none
% 1.53/1.01  --bmc1_ucm_max_lemma_size               10
% 1.53/1.01  
% 1.53/1.01  ------ AIG Options
% 1.53/1.01  
% 1.53/1.01  --aig_mode                              false
% 1.53/1.01  
% 1.53/1.01  ------ Instantiation Options
% 1.53/1.01  
% 1.53/1.01  --instantiation_flag                    true
% 1.53/1.01  --inst_sos_flag                         false
% 1.53/1.01  --inst_sos_phase                        true
% 1.53/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.53/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.53/1.01  --inst_lit_sel_side                     none
% 1.53/1.01  --inst_solver_per_active                1400
% 1.53/1.01  --inst_solver_calls_frac                1.
% 1.53/1.01  --inst_passive_queue_type               priority_queues
% 1.53/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.53/1.01  --inst_passive_queues_freq              [25;2]
% 1.53/1.01  --inst_dismatching                      true
% 1.53/1.01  --inst_eager_unprocessed_to_passive     true
% 1.53/1.01  --inst_prop_sim_given                   true
% 1.53/1.01  --inst_prop_sim_new                     false
% 1.53/1.01  --inst_subs_new                         false
% 1.53/1.01  --inst_eq_res_simp                      false
% 1.53/1.01  --inst_subs_given                       false
% 1.53/1.01  --inst_orphan_elimination               true
% 1.53/1.01  --inst_learning_loop_flag               true
% 1.53/1.01  --inst_learning_start                   3000
% 1.53/1.01  --inst_learning_factor                  2
% 1.53/1.01  --inst_start_prop_sim_after_learn       3
% 1.53/1.01  --inst_sel_renew                        solver
% 1.53/1.01  --inst_lit_activity_flag                true
% 1.53/1.01  --inst_restr_to_given                   false
% 1.53/1.01  --inst_activity_threshold               500
% 1.53/1.01  --inst_out_proof                        true
% 1.53/1.01  
% 1.53/1.01  ------ Resolution Options
% 1.53/1.01  
% 1.53/1.01  --resolution_flag                       false
% 1.53/1.01  --res_lit_sel                           adaptive
% 1.53/1.01  --res_lit_sel_side                      none
% 1.53/1.01  --res_ordering                          kbo
% 1.53/1.01  --res_to_prop_solver                    active
% 1.53/1.01  --res_prop_simpl_new                    false
% 1.53/1.01  --res_prop_simpl_given                  true
% 1.53/1.01  --res_passive_queue_type                priority_queues
% 1.53/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.53/1.01  --res_passive_queues_freq               [15;5]
% 1.53/1.01  --res_forward_subs                      full
% 1.53/1.01  --res_backward_subs                     full
% 1.53/1.01  --res_forward_subs_resolution           true
% 1.53/1.01  --res_backward_subs_resolution          true
% 1.53/1.01  --res_orphan_elimination                true
% 1.53/1.01  --res_time_limit                        2.
% 1.53/1.01  --res_out_proof                         true
% 1.53/1.01  
% 1.53/1.01  ------ Superposition Options
% 1.53/1.01  
% 1.53/1.01  --superposition_flag                    true
% 1.53/1.01  --sup_passive_queue_type                priority_queues
% 1.53/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.53/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.53/1.01  --demod_completeness_check              fast
% 1.53/1.01  --demod_use_ground                      true
% 1.53/1.01  --sup_to_prop_solver                    passive
% 1.53/1.01  --sup_prop_simpl_new                    true
% 1.53/1.01  --sup_prop_simpl_given                  true
% 1.53/1.01  --sup_fun_splitting                     false
% 1.53/1.01  --sup_smt_interval                      50000
% 1.53/1.01  
% 1.53/1.01  ------ Superposition Simplification Setup
% 1.53/1.01  
% 1.53/1.01  --sup_indices_passive                   []
% 1.53/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.53/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/1.01  --sup_full_bw                           [BwDemod]
% 1.53/1.01  --sup_immed_triv                        [TrivRules]
% 1.53/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.53/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/1.01  --sup_immed_bw_main                     []
% 1.53/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.53/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.53/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.53/1.01  
% 1.53/1.01  ------ Combination Options
% 1.53/1.01  
% 1.53/1.01  --comb_res_mult                         3
% 1.53/1.01  --comb_sup_mult                         2
% 1.53/1.01  --comb_inst_mult                        10
% 1.53/1.01  
% 1.53/1.01  ------ Debug Options
% 1.53/1.01  
% 1.53/1.01  --dbg_backtrace                         false
% 1.53/1.01  --dbg_dump_prop_clauses                 false
% 1.53/1.01  --dbg_dump_prop_clauses_file            -
% 1.53/1.01  --dbg_out_stat                          false
% 1.53/1.01  
% 1.53/1.01  
% 1.53/1.01  
% 1.53/1.01  
% 1.53/1.01  ------ Proving...
% 1.53/1.01  
% 1.53/1.01  
% 1.53/1.01  % SZS status CounterSatisfiable for theBenchmark.p
% 1.53/1.01  
% 1.53/1.01  % SZS output start Saturation for theBenchmark.p
% 1.53/1.01  
% 1.53/1.01  fof(f9,axiom,(
% 1.53/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/1.01  
% 1.53/1.01  fof(f40,plain,(
% 1.53/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.53/1.01    inference(cnf_transformation,[],[f9])).
% 1.53/1.01  
% 1.53/1.01  fof(f5,axiom,(
% 1.53/1.01    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 1.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/1.01  
% 1.53/1.01  fof(f36,plain,(
% 1.53/1.01    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 1.53/1.01    inference(cnf_transformation,[],[f5])).
% 1.53/1.01  
% 1.53/1.01  fof(f7,axiom,(
% 1.53/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/1.01  
% 1.53/1.01  fof(f38,plain,(
% 1.53/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.53/1.01    inference(cnf_transformation,[],[f7])).
% 1.53/1.01  
% 1.53/1.01  fof(f8,axiom,(
% 1.53/1.01    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/1.01  
% 1.53/1.01  fof(f39,plain,(
% 1.53/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.53/1.01    inference(cnf_transformation,[],[f8])).
% 1.53/1.01  
% 1.53/1.01  fof(f3,axiom,(
% 1.53/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/1.01  
% 1.53/1.01  fof(f34,plain,(
% 1.53/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.53/1.01    inference(cnf_transformation,[],[f3])).
% 1.53/1.01  
% 1.53/1.01  fof(f52,plain,(
% 1.53/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 1.53/1.01    inference(definition_unfolding,[],[f39,f34])).
% 1.53/1.01  
% 1.53/1.01  fof(f54,plain,(
% 1.53/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1))) )),
% 1.53/1.01    inference(definition_unfolding,[],[f38,f34,f34,f52])).
% 1.53/1.01  
% 1.53/1.01  fof(f10,axiom,(
% 1.53/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/1.01  
% 1.53/1.01  fof(f41,plain,(
% 1.53/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.53/1.01    inference(cnf_transformation,[],[f10])).
% 1.53/1.01  
% 1.53/1.01  fof(f55,plain,(
% 1.53/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.53/1.01    inference(definition_unfolding,[],[f41,f52])).
% 1.53/1.01  
% 1.53/1.01  fof(f6,axiom,(
% 1.53/1.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/1.01  
% 1.53/1.01  fof(f37,plain,(
% 1.53/1.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.53/1.01    inference(cnf_transformation,[],[f6])).
% 1.53/1.01  
% 1.53/1.01  fof(f53,plain,(
% 1.53/1.01    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.53/1.01    inference(definition_unfolding,[],[f37,f34])).
% 1.53/1.01  
% 1.53/1.01  fof(f1,axiom,(
% 1.53/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/1.01  
% 1.53/1.01  fof(f32,plain,(
% 1.53/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.53/1.01    inference(cnf_transformation,[],[f1])).
% 1.53/1.01  
% 1.53/1.01  fof(f12,axiom,(
% 1.53/1.01    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/1.01  
% 1.53/1.01  fof(f43,plain,(
% 1.53/1.01    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.53/1.01    inference(cnf_transformation,[],[f12])).
% 1.53/1.01  
% 1.53/1.01  fof(f11,axiom,(
% 1.53/1.01    ! [X0] : k2_subset_1(X0) = X0),
% 1.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/1.01  
% 1.53/1.01  fof(f42,plain,(
% 1.53/1.01    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.53/1.01    inference(cnf_transformation,[],[f11])).
% 1.53/1.01  
% 1.53/1.01  fof(f14,axiom,(
% 1.53/1.01    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/1.01  
% 1.53/1.01  fof(f25,plain,(
% 1.53/1.01    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.53/1.01    inference(ennf_transformation,[],[f14])).
% 1.53/1.01  
% 1.53/1.01  fof(f45,plain,(
% 1.53/1.01    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.53/1.01    inference(cnf_transformation,[],[f25])).
% 1.53/1.01  
% 1.53/1.01  fof(f57,plain,(
% 1.53/1.01    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.53/1.01    inference(definition_unfolding,[],[f45,f34])).
% 1.53/1.01  
% 1.53/1.01  fof(f15,axiom,(
% 1.53/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/1.01  
% 1.53/1.01  fof(f18,plain,(
% 1.53/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 1.53/1.01    inference(unused_predicate_definition_removal,[],[f15])).
% 1.53/1.01  
% 1.53/1.01  fof(f26,plain,(
% 1.53/1.01    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 1.53/1.01    inference(ennf_transformation,[],[f18])).
% 1.53/1.01  
% 1.53/1.01  fof(f46,plain,(
% 1.53/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.53/1.01    inference(cnf_transformation,[],[f26])).
% 1.53/1.01  
% 1.53/1.01  fof(f4,axiom,(
% 1.53/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/1.01  
% 1.53/1.01  fof(f22,plain,(
% 1.53/1.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.53/1.01    inference(ennf_transformation,[],[f4])).
% 1.53/1.01  
% 1.53/1.01  fof(f35,plain,(
% 1.53/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.53/1.01    inference(cnf_transformation,[],[f22])).
% 1.53/1.01  
% 1.53/1.01  fof(f16,conjecture,(
% 1.53/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 1.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/1.01  
% 1.53/1.01  fof(f17,negated_conjecture,(
% 1.53/1.01    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 1.53/1.01    inference(negated_conjecture,[],[f16])).
% 1.53/1.01  
% 1.53/1.01  fof(f20,plain,(
% 1.53/1.01    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2)))),
% 1.53/1.01    inference(pure_predicate_removal,[],[f17])).
% 1.53/1.01  
% 1.53/1.01  fof(f27,plain,(
% 1.53/1.01    ? [X0,X1] : (? [X2] : ((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & (r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 1.53/1.01    inference(ennf_transformation,[],[f20])).
% 1.53/1.01  
% 1.53/1.01  fof(f28,plain,(
% 1.53/1.01    ? [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 1.53/1.01    inference(flattening,[],[f27])).
% 1.53/1.01  
% 1.53/1.01  fof(f30,plain,(
% 1.53/1.01    ( ! [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != sK2 & r1_xboole_0(X1,sK2) & k4_subset_1(u1_struct_0(X0),X1,sK2) = k2_struct_0(X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.53/1.01    introduced(choice_axiom,[])).
% 1.53/1.01  
% 1.53/1.01  fof(f29,plain,(
% 1.53/1.01    ? [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != X2 & r1_xboole_0(sK1,X2) & k4_subset_1(u1_struct_0(sK0),sK1,X2) = k2_struct_0(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.53/1.01    introduced(choice_axiom,[])).
% 1.53/1.01  
% 1.53/1.01  fof(f31,plain,(
% 1.53/1.01    (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 & r1_xboole_0(sK1,sK2) & k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.53/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f30,f29])).
% 1.53/1.01  
% 1.53/1.01  fof(f48,plain,(
% 1.53/1.01    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.53/1.01    inference(cnf_transformation,[],[f31])).
% 1.53/1.01  
% 1.53/1.01  fof(f13,axiom,(
% 1.53/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 1.53/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/1.02  
% 1.53/1.02  fof(f23,plain,(
% 1.53/1.02    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.53/1.02    inference(ennf_transformation,[],[f13])).
% 1.53/1.02  
% 1.53/1.02  fof(f24,plain,(
% 1.53/1.02    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.53/1.02    inference(flattening,[],[f23])).
% 1.53/1.02  
% 1.53/1.02  fof(f44,plain,(
% 1.53/1.02    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.53/1.02    inference(cnf_transformation,[],[f24])).
% 1.53/1.02  
% 1.53/1.02  fof(f56,plain,(
% 1.53/1.02    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.53/1.02    inference(definition_unfolding,[],[f44,f52])).
% 1.53/1.02  
% 1.53/1.02  fof(f47,plain,(
% 1.53/1.02    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.53/1.02    inference(cnf_transformation,[],[f31])).
% 1.53/1.02  
% 1.53/1.02  fof(f49,plain,(
% 1.53/1.02    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0)),
% 1.53/1.02    inference(cnf_transformation,[],[f31])).
% 1.53/1.02  
% 1.53/1.02  fof(f2,axiom,(
% 1.53/1.02    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.53/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/1.02  
% 1.53/1.02  fof(f19,plain,(
% 1.53/1.02    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.53/1.02    inference(unused_predicate_definition_removal,[],[f2])).
% 1.53/1.02  
% 1.53/1.02  fof(f21,plain,(
% 1.53/1.02    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 1.53/1.02    inference(ennf_transformation,[],[f19])).
% 1.53/1.02  
% 1.53/1.02  fof(f33,plain,(
% 1.53/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.53/1.02    inference(cnf_transformation,[],[f21])).
% 1.53/1.02  
% 1.53/1.02  fof(f50,plain,(
% 1.53/1.02    r1_xboole_0(sK1,sK2)),
% 1.53/1.02    inference(cnf_transformation,[],[f31])).
% 1.53/1.02  
% 1.53/1.02  fof(f51,plain,(
% 1.53/1.02    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2),
% 1.53/1.02    inference(cnf_transformation,[],[f31])).
% 1.53/1.02  
% 1.53/1.02  cnf(c_108,plain,
% 1.53/1.02      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.53/1.02      theory(equality) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_196,plain,( X0_2 = X0_2 ),theory(equality) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_6,plain,
% 1.53/1.02      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 1.53/1.02      inference(cnf_transformation,[],[f40]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3,plain,
% 1.53/1.02      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 1.53/1.02      inference(cnf_transformation,[],[f36]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_5,plain,
% 1.53/1.02      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 1.53/1.02      inference(cnf_transformation,[],[f54]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_7,plain,
% 1.53/1.02      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
% 1.53/1.02      inference(cnf_transformation,[],[f55]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_359,plain,
% 1.53/1.02      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_5,c_7]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1391,plain,
% 1.53/1.02      ( k5_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_3,c_359]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4,plain,
% 1.53/1.02      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 1.53/1.02      inference(cnf_transformation,[],[f53]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_340,plain,
% 1.53/1.02      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_4,c_3]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1409,plain,
% 1.53/1.02      ( k5_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k1_xboole_0) = X0 ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_1391,c_3,c_340]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1418,plain,
% 1.53/1.02      ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k1_xboole_0) = X0 ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_6,c_1409]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2013,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_1418,c_340]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_0,plain,
% 1.53/1.02      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 1.53/1.02      inference(cnf_transformation,[],[f32]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1389,plain,
% 1.53/1.02      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(X1,k3_tarski(k2_tarski(X0,X1)))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_0,c_359]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_9,plain,
% 1.53/1.02      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 1.53/1.02      inference(cnf_transformation,[],[f43]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_324,plain,
% 1.53/1.02      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_8,plain,
% 1.53/1.02      ( k2_subset_1(X0) = X0 ),
% 1.53/1.02      inference(cnf_transformation,[],[f42]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_335,plain,
% 1.53/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_324,c_8]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_11,plain,
% 1.53/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.53/1.02      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 1.53/1.02      inference(cnf_transformation,[],[f57]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_322,plain,
% 1.53/1.02      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 1.53/1.02      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1140,plain,
% 1.53/1.02      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X0,X0,X1) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_335,c_322]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3537,plain,
% 1.53/1.02      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(X1,k3_tarski(k2_tarski(X0,X1)))) = k7_subset_1(X0,X0,X1) ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_1389,c_1140]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1977,plain,
% 1.53/1.02      ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k7_subset_1(X0,X0,X1) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_0,c_1140]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3554,plain,
% 1.53/1.02      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k7_subset_1(X0,X0,X1) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_3537,c_1977]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_7251,plain,
% 1.53/1.02      ( k7_subset_1(X0,X0,X0) = k7_subset_1(k1_xboole_0,k1_xboole_0,X0) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_2013,c_3554]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_12,plain,
% 1.53/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.53/1.02      inference(cnf_transformation,[],[f46]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2,plain,
% 1.53/1.02      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 1.53/1.02      inference(cnf_transformation,[],[f35]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_132,plain,
% 1.53/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | k3_xboole_0(X0,X1) = X0 ),
% 1.53/1.02      inference(resolution,[status(thm)],[c_12,c_2]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_319,plain,
% 1.53/1.02      ( k3_xboole_0(X0,X1) = X0
% 1.53/1.02      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_132]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1083,plain,
% 1.53/1.02      ( k3_xboole_0(X0,X0) = X0 ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_335,c_319]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1984,plain,
% 1.53/1.02      ( k7_subset_1(X0,X0,X0) = k5_xboole_0(X0,X0) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_1083,c_1140]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_649,plain,
% 1.53/1.02      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1981,plain,
% 1.53/1.02      ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_649,c_1140]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1996,plain,
% 1.53/1.02      ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k1_xboole_0 ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_1981,c_340]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_7279,plain,
% 1.53/1.02      ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_7251,c_1984,c_1996]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1396,plain,
% 1.53/1.02      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_359,c_7]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1398,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_1396,c_7]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3162,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_6,c_1398]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_7255,plain,
% 1.53/1.02      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_3162,c_3554]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_7280,plain,
% 1.53/1.02      ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) = k1_xboole_0 ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_7279,c_7255]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1962,plain,
% 1.53/1.02      ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_1140,c_7]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_10299,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_7280,c_1962]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_10301,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X0,X1)) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_10299,c_340]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_11202,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(X1,X0)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_6,c_10301]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3164,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_1398,c_1398]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_9927,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_6,c_3164]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_911,plain,
% 1.53/1.02      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k3_tarski(k2_tarski(X0,k1_xboole_0)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_649,c_7]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_914,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_911,c_340]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4499,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(X0,X0)) = k3_tarski(k2_tarski(X0,k1_xboole_0)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_914,c_3162]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4500,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(X0,X0)) = X0 ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_4499,c_914]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_9981,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(X0,X1)) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_9927,c_4500]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_10106,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X1,X0)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_6,c_9981]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_10697,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X1,X0)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_6,c_10106]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_10714,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_10106,c_1398]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3549,plain,
% 1.53/1.02      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X1,X0)),k3_tarski(k2_tarski(X0,X1)))) = k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0))) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_1398,c_3537]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_7529,plain,
% 1.53/1.02      ( k5_xboole_0(X0,k3_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),X0)) = k7_subset_1(k1_xboole_0,k1_xboole_0,k3_tarski(k2_tarski(X0,k1_xboole_0))) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_2013,c_3549]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_7577,plain,
% 1.53/1.02      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_7529,c_914,c_1083,c_1996]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_7541,plain,
% 1.53/1.02      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k7_subset_1(X1,X1,k3_tarski(k2_tarski(X0,X1))) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_6,c_3549]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_7548,plain,
% 1.53/1.02      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1))) = k7_subset_1(X1,X1,k3_tarski(k2_tarski(X0,X1))) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_7541,c_1083,c_1140]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_7578,plain,
% 1.53/1.02      ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_7577,c_7548]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1961,plain,
% 1.53/1.02      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k7_subset_1(X0,X0,X1) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_1140,c_359]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4877,plain,
% 1.53/1.02      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0))) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_1398,c_1961]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_10656,plain,
% 1.53/1.02      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k1_xboole_0 ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_7578,c_4877]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_9896,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X0)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_6,c_3164]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_10269,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X1,X0)) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_9896,c_9981]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_9915,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X0)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_6,c_3164]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_10231,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X1,X0)) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_9915,c_9981]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_7735,plain,
% 1.53/1.02      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1))) = k7_subset_1(X1,X1,k3_tarski(k2_tarski(X0,X1))) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_7541,c_1083,c_1140]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_8033,plain,
% 1.53/1.02      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1))) = k7_subset_1(X1,X1,k3_tarski(k2_tarski(X1,X0))) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_6,c_7735]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_8098,plain,
% 1.53/1.02      ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0))) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_8033,c_7735]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_10119,plain,
% 1.53/1.02      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1))))) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1))) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_9981,c_8098]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_10151,plain,
% 1.53/1.02      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_10119,c_1398,c_7279]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_10117,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X1,X0)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_6,c_9981]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_9987,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_9981,c_3164]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_7722,plain,
% 1.53/1.02      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_7529,c_914,c_1083,c_1996]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_16,negated_conjecture,
% 1.53/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.53/1.02      inference(cnf_transformation,[],[f48]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_321,plain,
% 1.53/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_642,plain,
% 1.53/1.02      ( k3_xboole_0(sK2,u1_struct_0(sK0)) = sK2 ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_321,c_319]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_918,plain,
% 1.53/1.02      ( k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(sK2,sK2)) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK2)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_642,c_7]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_8373,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(u1_struct_0(sK0),sK2)) = k5_xboole_0(u1_struct_0(sK0),k1_xboole_0) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_7722,c_918]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_8393,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(u1_struct_0(sK0),sK2)) = u1_struct_0(sK0) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_8373,c_340]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_8834,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = u1_struct_0(sK0) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_6,c_8393]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_774,plain,
% 1.53/1.02      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k3_tarski(k2_tarski(X0,X1)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_0,c_7]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1314,plain,
% 1.53/1.02      ( k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_642,c_774]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_9118,plain,
% 1.53/1.02      ( k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)) = u1_struct_0(sK0) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_8834,c_1314]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_10,plain,
% 1.53/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.53/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 1.53/1.02      | k5_xboole_0(X2,k5_xboole_0(X0,k3_xboole_0(X0,X2))) = k4_subset_1(X1,X2,X0) ),
% 1.53/1.02      inference(cnf_transformation,[],[f56]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_323,plain,
% 1.53/1.02      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k4_subset_1(X2,X0,X1)
% 1.53/1.02      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 1.53/1.02      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_362,plain,
% 1.53/1.02      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 1.53/1.02      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 1.53/1.02      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_323,c_7]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4334,plain,
% 1.53/1.02      ( k4_subset_1(u1_struct_0(sK0),sK2,X0) = k3_tarski(k2_tarski(sK2,X0))
% 1.53/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_321,c_362]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4515,plain,
% 1.53/1.02      ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_335,c_4334]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_9117,plain,
% 1.53/1.02      ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_8834,c_4515]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_17,negated_conjecture,
% 1.53/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.53/1.02      inference(cnf_transformation,[],[f47]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_320,plain,
% 1.53/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.53/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_643,plain,
% 1.53/1.02      ( k3_xboole_0(sK1,u1_struct_0(sK0)) = sK1 ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_320,c_319]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_988,plain,
% 1.53/1.02      ( k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(sK1,sK1)) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK1)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_643,c_7]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_8375,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k1_xboole_0) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_7722,c_988]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_8388,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(u1_struct_0(sK0),sK1)) = u1_struct_0(sK0) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_8375,c_340]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_8623,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = u1_struct_0(sK0) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_6,c_8388]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1315,plain,
% 1.53/1.02      ( k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_643,c_774]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_9100,plain,
% 1.53/1.02      ( k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) = u1_struct_0(sK0) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_8623,c_1315]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4335,plain,
% 1.53/1.02      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
% 1.53/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_320,c_362]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4557,plain,
% 1.53/1.02      ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_335,c_4335]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_9099,plain,
% 1.53/1.02      ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = u1_struct_0(sK0) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_8623,c_4557]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_8838,plain,
% 1.53/1.02      ( k5_xboole_0(u1_struct_0(sK0),k3_xboole_0(u1_struct_0(sK0),sK2)) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_8393,c_1961]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2247,plain,
% 1.53/1.02      ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k5_xboole_0(u1_struct_0(sK0),sK2) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_642,c_1977]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_8855,plain,
% 1.53/1.02      ( k5_xboole_0(u1_struct_0(sK0),k3_xboole_0(u1_struct_0(sK0),sK2)) = k5_xboole_0(u1_struct_0(sK0),sK2) ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_8838,c_2247]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4336,plain,
% 1.53/1.02      ( k4_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
% 1.53/1.02      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_335,c_362]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_7324,plain,
% 1.53/1.02      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK2)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_321,c_4336]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_8833,plain,
% 1.53/1.02      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = u1_struct_0(sK0) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_8393,c_7324]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3552,plain,
% 1.53/1.02      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(X0,k3_tarski(k2_tarski(X0,X1)))) = k7_subset_1(X1,X1,X0) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_6,c_3537]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3590,plain,
% 1.53/1.02      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k7_subset_1(X1,X1,X0) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_3552,c_1977]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_8625,plain,
% 1.53/1.02      ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0)) = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_8388,c_3590]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1983,plain,
% 1.53/1.02      ( k7_subset_1(sK1,sK1,u1_struct_0(sK0)) = k5_xboole_0(sK1,sK1) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_643,c_1140]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_8374,plain,
% 1.53/1.02      ( k7_subset_1(sK1,sK1,u1_struct_0(sK0)) = k1_xboole_0 ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_7722,c_1983]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_8647,plain,
% 1.53/1.02      ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0)) = k1_xboole_0 ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_8625,c_8374]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_8627,plain,
% 1.53/1.02      ( k5_xboole_0(u1_struct_0(sK0),k3_xboole_0(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_8388,c_1961]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2248,plain,
% 1.53/1.02      ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_643,c_1977]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_8644,plain,
% 1.53/1.02      ( k5_xboole_0(u1_struct_0(sK0),k3_xboole_0(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),sK1) ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_8627,c_2248]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_7325,plain,
% 1.53/1.02      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK1)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_320,c_4336]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_8622,plain,
% 1.53/1.02      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = u1_struct_0(sK0) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_8388,c_7325]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4555,plain,
% 1.53/1.02      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_tarski(k2_tarski(sK1,sK2)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_321,c_4335]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_15,negated_conjecture,
% 1.53/1.02      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
% 1.53/1.02      inference(cnf_transformation,[],[f49]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1,plain,
% 1.53/1.02      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 1.53/1.02      inference(cnf_transformation,[],[f33]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_14,negated_conjecture,
% 1.53/1.02      ( r1_xboole_0(sK1,sK2) ),
% 1.53/1.02      inference(cnf_transformation,[],[f50]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_126,plain,
% 1.53/1.02      ( k3_xboole_0(X0,X1) = k1_xboole_0 | sK2 != X1 | sK1 != X0 ),
% 1.53/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_14]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_127,plain,
% 1.53/1.02      ( k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
% 1.53/1.02      inference(unflattening,[status(thm)],[c_126]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1312,plain,
% 1.53/1.02      ( k5_xboole_0(sK1,k5_xboole_0(sK2,k1_xboole_0)) = k3_tarski(k2_tarski(sK1,sK2)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_127,c_774]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_777,plain,
% 1.53/1.02      ( k5_xboole_0(sK2,k5_xboole_0(sK1,k1_xboole_0)) = k3_tarski(k2_tarski(sK2,sK1)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_127,c_7]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_779,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(sK2,sK1)) = k5_xboole_0(sK2,sK1) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_777,c_340]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_990,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(sK1,sK2)) = k5_xboole_0(sK2,sK1) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_6,c_779]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1322,plain,
% 1.53/1.02      ( k5_xboole_0(sK1,k5_xboole_0(sK2,k1_xboole_0)) = k5_xboole_0(sK2,sK1) ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_1312,c_990]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1323,plain,
% 1.53/1.02      ( k5_xboole_0(sK1,sK2) = k5_xboole_0(sK2,sK1) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_1322,c_340]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1838,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(sK1,sK2)) = k5_xboole_0(sK1,sK2) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_1323,c_990]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4563,plain,
% 1.53/1.02      ( k5_xboole_0(sK1,sK2) = k2_struct_0(sK0) ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_4555,c_15,c_1838]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1393,plain,
% 1.53/1.02      ( k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK2,sK1),sK2)) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_990,c_359]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1403,plain,
% 1.53/1.02      ( k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK2,sK1),sK2)) = k5_xboole_0(sK1,k1_xboole_0) ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_1393,c_127]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1404,plain,
% 1.53/1.02      ( k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK2,sK1),sK2)) = sK1 ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_1403,c_340]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1734,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(sK2,k5_xboole_0(sK2,sK1))) = k5_xboole_0(sK2,sK1) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_1404,c_7]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1888,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(sK2,k5_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,sK2) ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_1734,c_1323]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4652,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(sK2,k2_struct_0(sK0))) = k2_struct_0(sK0) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_4563,c_1888]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_5302,plain,
% 1.53/1.02      ( k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0))) = k7_subset_1(sK2,sK2,k2_struct_0(sK0)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_4652,c_3537]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_5308,plain,
% 1.53/1.02      ( k7_subset_1(sK2,sK2,k2_struct_0(sK0)) = k5_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_5302,c_1083,c_1140]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_8381,plain,
% 1.53/1.02      ( k7_subset_1(sK2,sK2,k2_struct_0(sK0)) = k1_xboole_0 ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_7722,c_5308]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4648,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(sK1,sK2)) = k2_struct_0(sK0) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_4563,c_1838]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4769,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(sK1,k2_struct_0(sK0))) = k3_tarski(k2_tarski(sK1,sK2)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_4648,c_3162]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4773,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(sK1,k2_struct_0(sK0))) = k2_struct_0(sK0) ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_4769,c_4648]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_5892,plain,
% 1.53/1.02      ( k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0))) = k7_subset_1(sK1,sK1,k2_struct_0(sK0)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_4773,c_3537]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_5898,plain,
% 1.53/1.02      ( k7_subset_1(sK1,sK1,k2_struct_0(sK0)) = k5_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_5892,c_1083,c_1140]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_8379,plain,
% 1.53/1.02      ( k7_subset_1(sK1,sK1,k2_struct_0(sK0)) = k1_xboole_0 ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_7722,c_5898]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1982,plain,
% 1.53/1.02      ( k7_subset_1(sK2,sK2,u1_struct_0(sK0)) = k5_xboole_0(sK2,sK2) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_642,c_1140]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_8372,plain,
% 1.53/1.02      ( k7_subset_1(sK2,sK2,u1_struct_0(sK0)) = k1_xboole_0 ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_7722,c_1982]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_7326,plain,
% 1.53/1.02      ( k4_subset_1(X0,X0,X0) = k3_tarski(k2_tarski(X0,X0)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_335,c_4336]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_7729,plain,
% 1.53/1.02      ( k4_subset_1(X0,X0,X0) = X0 ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_7326,c_4500]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_7581,plain,
% 1.53/1.02      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X1,X0)),k3_tarski(k2_tarski(X0,X1)))) = k1_xboole_0 ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_7578,c_3549]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4556,plain,
% 1.53/1.02      ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_320,c_4335]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_7416,plain,
% 1.53/1.02      ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = sK1 ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_4500,c_4556]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4513,plain,
% 1.53/1.02      ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_321,c_4334]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_7415,plain,
% 1.53/1.02      ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = sK2 ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_4500,c_4513]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_5894,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(k2_struct_0(sK0),k2_struct_0(sK0))) = k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_4773,c_1398]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_5304,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(k2_struct_0(sK0),k2_struct_0(sK0))) = k3_tarski(k2_tarski(k2_struct_0(sK0),sK2)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_4652,c_1398]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_6965,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)) = k3_tarski(k2_tarski(k2_struct_0(sK0),sK2)) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_5894,c_5304]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_6983,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)) = k3_tarski(k2_tarski(sK2,k2_struct_0(sK0))) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_6,c_6965]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_7013,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_6983,c_4652]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_7153,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(k2_struct_0(sK0),k2_struct_0(sK0))) = k2_struct_0(sK0) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_7013,c_5894]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_7019,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(k2_struct_0(sK0),sK2)) = k2_struct_0(sK0) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_7013,c_6965]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4514,plain,
% 1.53/1.02      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k3_tarski(k2_tarski(sK2,sK1)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_320,c_4334]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1839,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(sK2,sK1)) = k5_xboole_0(sK1,sK2) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_1323,c_779]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4519,plain,
% 1.53/1.02      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k5_xboole_0(sK1,sK2) ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_4514,c_1839]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_6331,plain,
% 1.53/1.02      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_struct_0(sK0) ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_4519,c_4563]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_776,plain,
% 1.53/1.02      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) = k3_tarski(k2_tarski(k1_xboole_0,X0)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_3,c_7]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_782,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_776,c_340]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_5179,plain,
% 1.53/1.02      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_782,c_2013]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4654,plain,
% 1.53/1.02      ( k5_xboole_0(sK2,sK1) = k2_struct_0(sK0) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_4563,c_1323]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4653,plain,
% 1.53/1.02      ( k3_tarski(k2_tarski(sK2,sK1)) = k2_struct_0(sK0) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_4563,c_1839]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1732,plain,
% 1.53/1.02      ( k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(sK2,k5_xboole_0(sK2,sK1))) = sK1 ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_0,c_1404]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2257,plain,
% 1.53/1.02      ( k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))) = sK1 ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_1732,c_1323]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4651,plain,
% 1.53/1.02      ( k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(sK2,k2_struct_0(sK0))) = sK1 ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_4563,c_2257]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1837,plain,
% 1.53/1.02      ( k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK2)) = sK1 ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_1323,c_1404]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4650,plain,
% 1.53/1.02      ( k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(k2_struct_0(sK0),sK2)) = sK1 ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_4563,c_1837]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3548,plain,
% 1.53/1.02      ( k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = k7_subset_1(sK2,sK2,sK1) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_1839,c_3537]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2245,plain,
% 1.53/1.02      ( k7_subset_1(sK2,sK2,sK1) = k5_xboole_0(sK2,k1_xboole_0) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_127,c_1977]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2255,plain,
% 1.53/1.02      ( k7_subset_1(sK2,sK2,sK1) = sK2 ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_2245,c_340]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3568,plain,
% 1.53/1.02      ( k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,k5_xboole_0(sK1,sK2))) = sK2 ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_3548,c_2255]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4649,plain,
% 1.53/1.02      ( k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(sK1,k2_struct_0(sK0))) = sK2 ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_4563,c_3568]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_3739,plain,
% 1.53/1.02      ( k7_subset_1(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2),sK1) = sK2 ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_1977,c_3568]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4647,plain,
% 1.53/1.02      ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = sK2 ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_4563,c_3739]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1884,plain,
% 1.53/1.02      ( k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1)) = k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_1839,c_359]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4159,plain,
% 1.53/1.02      ( k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1)) = sK2 ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_1884,c_1140,c_2255]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4646,plain,
% 1.53/1.02      ( k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(k2_struct_0(sK0),sK1)) = sK2 ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_4563,c_4159]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2259,plain,
% 1.53/1.02      ( k7_subset_1(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2),sK2) = sK1 ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_1977,c_2257]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4645,plain,
% 1.53/1.02      ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) = sK1 ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_4563,c_2259]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1394,plain,
% 1.53/1.02      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k5_xboole_0(X1,k3_xboole_0(X1,X0)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_6,c_359]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_4299,plain,
% 1.53/1.02      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k7_subset_1(X1,X1,X0) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_1394,c_1140]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1979,plain,
% 1.53/1.02      ( k7_subset_1(X0,X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_3,c_1140]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_2002,plain,
% 1.53/1.02      ( k7_subset_1(X0,X0,k1_xboole_0) = X0 ),
% 1.53/1.02      inference(light_normalisation,[status(thm)],[c_1979,c_340]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1980,plain,
% 1.53/1.02      ( k7_subset_1(sK1,sK1,sK2) = k5_xboole_0(sK1,k1_xboole_0) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_127,c_1140]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1999,plain,
% 1.53/1.02      ( k7_subset_1(sK1,sK1,sK2) = sK1 ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_1980,c_340]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1139,plain,
% 1.53/1.02      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_320,c_322]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1964,plain,
% 1.53/1.02      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_1140,c_1139]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1138,plain,
% 1.53/1.02      ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) ),
% 1.53/1.02      inference(superposition,[status(thm)],[c_321,c_322]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1963,plain,
% 1.53/1.02      ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0) ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_1140,c_1138]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_1142,plain,
% 1.53/1.02      ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
% 1.53/1.02      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 1.53/1.02      inference(demodulation,[status(thm)],[c_1140,c_322]) ).
% 1.53/1.02  
% 1.53/1.02  cnf(c_13,negated_conjecture,
% 1.53/1.02      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
% 1.53/1.02      inference(cnf_transformation,[],[f51]) ).
% 1.53/1.02  
% 1.53/1.02  
% 1.53/1.02  % SZS output end Saturation for theBenchmark.p
% 1.53/1.02  
% 1.53/1.02  ------                               Statistics
% 1.53/1.02  
% 1.53/1.02  ------ General
% 1.53/1.02  
% 1.53/1.02  abstr_ref_over_cycles:                  0
% 1.53/1.02  abstr_ref_under_cycles:                 0
% 1.53/1.02  gc_basic_clause_elim:                   0
% 1.53/1.02  forced_gc_time:                         0
% 1.53/1.02  parsing_time:                           0.028
% 1.53/1.02  unif_index_cands_time:                  0.
% 1.53/1.02  unif_index_add_time:                    0.
% 1.53/1.02  orderings_time:                         0.
% 1.53/1.02  out_proof_time:                         0.
% 1.53/1.02  total_time:                             0.496
% 1.53/1.02  num_of_symbols:                         48
% 1.53/1.02  num_of_terms:                           9442
% 1.53/1.02  
% 1.53/1.02  ------ Preprocessing
% 1.53/1.02  
% 1.53/1.02  num_of_splits:                          0
% 1.53/1.02  num_of_split_atoms:                     0
% 1.53/1.02  num_of_reused_defs:                     0
% 1.53/1.02  num_eq_ax_congr_red:                    11
% 1.53/1.02  num_of_sem_filtered_clauses:            1
% 1.53/1.02  num_of_subtypes:                        0
% 1.53/1.02  monotx_restored_types:                  0
% 1.53/1.02  sat_num_of_epr_types:                   0
% 1.53/1.02  sat_num_of_non_cyclic_types:            0
% 1.53/1.02  sat_guarded_non_collapsed_types:        0
% 1.53/1.02  num_pure_diseq_elim:                    0
% 1.53/1.02  simp_replaced_by:                       0
% 1.53/1.02  res_preprocessed:                       89
% 1.53/1.02  prep_upred:                             0
% 1.53/1.02  prep_unflattend:                        2
% 1.53/1.02  smt_new_axioms:                         0
% 1.53/1.02  pred_elim_cands:                        1
% 1.53/1.02  pred_elim:                              2
% 1.53/1.02  pred_elim_cl:                           2
% 1.53/1.02  pred_elim_cycles:                       4
% 1.53/1.02  merged_defs:                            0
% 1.53/1.02  merged_defs_ncl:                        0
% 1.53/1.02  bin_hyper_res:                          0
% 1.53/1.02  prep_cycles:                            4
% 1.53/1.02  pred_elim_time:                         0.
% 1.53/1.02  splitting_time:                         0.
% 1.53/1.02  sem_filter_time:                        0.
% 1.53/1.02  monotx_time:                            0.
% 1.53/1.02  subtype_inf_time:                       0.
% 1.53/1.02  
% 1.53/1.02  ------ Problem properties
% 1.53/1.02  
% 1.53/1.02  clauses:                                16
% 1.53/1.02  conjectures:                            4
% 1.53/1.02  epr:                                    0
% 1.53/1.02  horn:                                   16
% 1.53/1.02  ground:                                 5
% 1.53/1.02  unary:                                  13
% 1.53/1.02  binary:                                 2
% 1.53/1.02  lits:                                   20
% 1.53/1.02  lits_eq:                                13
% 1.53/1.02  fd_pure:                                0
% 1.53/1.02  fd_pseudo:                              0
% 1.53/1.02  fd_cond:                                0
% 1.53/1.02  fd_pseudo_cond:                         0
% 1.53/1.02  ac_symbols:                             0
% 1.53/1.02  
% 1.53/1.02  ------ Propositional Solver
% 1.53/1.02  
% 1.53/1.02  prop_solver_calls:                      29
% 1.53/1.02  prop_fast_solver_calls:                 480
% 1.53/1.02  smt_solver_calls:                       0
% 1.53/1.02  smt_fast_solver_calls:                  0
% 1.53/1.02  prop_num_of_clauses:                    4320
% 1.53/1.02  prop_preprocess_simplified:             8518
% 1.53/1.02  prop_fo_subsumed:                       0
% 1.53/1.02  prop_solver_time:                       0.
% 1.53/1.02  smt_solver_time:                        0.
% 1.53/1.02  smt_fast_solver_time:                   0.
% 1.53/1.02  prop_fast_solver_time:                  0.
% 1.53/1.02  prop_unsat_core_time:                   0.
% 1.53/1.02  
% 1.53/1.02  ------ QBF
% 1.53/1.02  
% 1.53/1.02  qbf_q_res:                              0
% 1.53/1.02  qbf_num_tautologies:                    0
% 1.53/1.02  qbf_prep_cycles:                        0
% 1.53/1.02  
% 1.53/1.02  ------ BMC1
% 1.53/1.02  
% 1.53/1.02  bmc1_current_bound:                     -1
% 1.53/1.02  bmc1_last_solved_bound:                 -1
% 1.53/1.02  bmc1_unsat_core_size:                   -1
% 1.53/1.02  bmc1_unsat_core_parents_size:           -1
% 1.53/1.02  bmc1_merge_next_fun:                    0
% 1.53/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.53/1.02  
% 1.53/1.02  ------ Instantiation
% 1.53/1.02  
% 1.53/1.02  inst_num_of_clauses:                    1816
% 1.53/1.02  inst_num_in_passive:                    298
% 1.53/1.02  inst_num_in_active:                     714
% 1.53/1.02  inst_num_in_unprocessed:                806
% 1.53/1.02  inst_num_of_loops:                      730
% 1.53/1.02  inst_num_of_learning_restarts:          0
% 1.53/1.02  inst_num_moves_active_passive:          13
% 1.53/1.02  inst_lit_activity:                      0
% 1.53/1.02  inst_lit_activity_moves:                0
% 1.53/1.02  inst_num_tautologies:                   0
% 1.53/1.02  inst_num_prop_implied:                  0
% 1.53/1.02  inst_num_existing_simplified:           0
% 1.53/1.02  inst_num_eq_res_simplified:             0
% 1.53/1.02  inst_num_child_elim:                    0
% 1.53/1.02  inst_num_of_dismatching_blockings:      505
% 1.53/1.02  inst_num_of_non_proper_insts:           1791
% 1.53/1.02  inst_num_of_duplicates:                 0
% 1.53/1.02  inst_inst_num_from_inst_to_res:         0
% 1.53/1.02  inst_dismatching_checking_time:         0.
% 1.53/1.02  
% 1.53/1.02  ------ Resolution
% 1.53/1.02  
% 1.53/1.02  res_num_of_clauses:                     0
% 1.53/1.02  res_num_in_passive:                     0
% 1.53/1.02  res_num_in_active:                      0
% 1.53/1.02  res_num_of_loops:                       93
% 1.53/1.02  res_forward_subset_subsumed:            162
% 1.53/1.02  res_backward_subset_subsumed:           4
% 1.53/1.02  res_forward_subsumed:                   0
% 1.53/1.02  res_backward_subsumed:                  0
% 1.53/1.02  res_forward_subsumption_resolution:     0
% 1.53/1.02  res_backward_subsumption_resolution:    0
% 1.53/1.02  res_clause_to_clause_subsumption:       1041
% 1.53/1.02  res_orphan_elimination:                 0
% 1.53/1.02  res_tautology_del:                      128
% 1.53/1.02  res_num_eq_res_simplified:              0
% 1.53/1.02  res_num_sel_changes:                    0
% 1.53/1.02  res_moves_from_active_to_pass:          0
% 1.53/1.02  
% 1.53/1.02  ------ Superposition
% 1.53/1.02  
% 1.53/1.02  sup_time_total:                         0.
% 1.53/1.02  sup_time_generating:                    0.
% 1.53/1.02  sup_time_sim_full:                      0.
% 1.53/1.02  sup_time_sim_immed:                     0.
% 1.53/1.02  
% 1.53/1.02  sup_num_of_clauses:                     122
% 1.53/1.02  sup_num_in_active:                      97
% 1.53/1.02  sup_num_in_passive:                     25
% 1.53/1.02  sup_num_of_loops:                       145
% 1.53/1.02  sup_fw_superposition:                   1070
% 1.53/1.02  sup_bw_superposition:                   532
% 1.53/1.02  sup_immediate_simplified:               576
% 1.53/1.02  sup_given_eliminated:                   6
% 1.53/1.02  comparisons_done:                       0
% 1.53/1.02  comparisons_avoided:                    0
% 1.53/1.02  
% 1.53/1.02  ------ Simplifications
% 1.53/1.02  
% 1.53/1.02  
% 1.53/1.02  sim_fw_subset_subsumed:                 0
% 1.53/1.02  sim_bw_subset_subsumed:                 0
% 1.53/1.02  sim_fw_subsumed:                        47
% 1.53/1.02  sim_bw_subsumed:                        0
% 1.53/1.02  sim_fw_subsumption_res:                 0
% 1.53/1.02  sim_bw_subsumption_res:                 0
% 1.53/1.02  sim_tautology_del:                      0
% 1.53/1.02  sim_eq_tautology_del:                   301
% 1.53/1.02  sim_eq_res_simp:                        0
% 1.53/1.02  sim_fw_demodulated:                     217
% 1.53/1.02  sim_bw_demodulated:                     68
% 1.53/1.02  sim_light_normalised:                   501
% 1.53/1.02  sim_joinable_taut:                      0
% 1.53/1.02  sim_joinable_simp:                      0
% 1.53/1.02  sim_ac_normalised:                      0
% 1.53/1.02  sim_smt_subsumption:                    0
% 1.53/1.02  
%------------------------------------------------------------------------------
