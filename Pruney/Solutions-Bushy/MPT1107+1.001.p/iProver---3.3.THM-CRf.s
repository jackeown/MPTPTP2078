%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1107+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:54 EST 2020

% Result     : Theorem 0.89s
% Output     : CNFRefutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :   64 (  93 expanded)
%              Number of clauses        :   35 (  38 expanded)
%              Number of leaves         :   11 (  23 expanded)
%              Depth                    :   13
%              Number of atoms          :  190 ( 291 expanded)
%              Number of equality atoms :   71 (  98 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( u1_struct_0(k1_pre_topc(X0,sK1)) != sK1
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( u1_struct_0(k1_pre_topc(X0,X1)) != X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( u1_struct_0(k1_pre_topc(sK0,X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK1)) != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f18,f17])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f20])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f29,plain,(
    u1_struct_0(k1_pre_topc(sK0,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_427,plain,
    ( X0_40 != X1_40
    | X2_40 != X1_40
    | X2_40 = X0_40 ),
    theory(equality)).

cnf(c_620,plain,
    ( k2_struct_0(k1_pre_topc(sK0,sK1)) != X0_40
    | sK1 != X0_40
    | sK1 = k2_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_427])).

cnf(c_621,plain,
    ( k2_struct_0(k1_pre_topc(sK0,sK1)) != sK1
    | sK1 = k2_struct_0(k1_pre_topc(sK0,sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_5,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_2,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_113,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_5,c_2])).

cnf(c_419,plain,
    ( ~ l1_pre_topc(X0_39)
    | u1_struct_0(X0_39) = k2_struct_0(X0_39) ),
    inference(subtyping,[status(esa)],[c_113])).

cnf(c_598,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | u1_struct_0(k1_pre_topc(sK0,sK1)) = k2_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_419])).

cnf(c_594,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK1)) != X0_40
    | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1
    | sK1 != X0_40 ),
    inference(instantiation,[status(thm)],[c_427])).

cnf(c_597,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK1)) != k2_struct_0(k1_pre_topc(sK0,sK1))
    | u1_struct_0(k1_pre_topc(sK0,sK1)) = sK1
    | sK1 != k2_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_594])).

cnf(c_425,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_584,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_425])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_pre_topc(k1_pre_topc(X1,X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_8,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_256,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_8])).

cnf(c_257,plain,
    ( m1_pre_topc(k1_pre_topc(X0,sK1),X0)
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_256])).

cnf(c_327,plain,
    ( ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X2)
    | X1 != X0
    | k1_pre_topc(X1,sK1) != X2
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(resolution_lifted,[status(thm)],[c_6,c_257])).

cnf(c_328,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(k1_pre_topc(X0,sK1))
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_417,plain,
    ( ~ l1_pre_topc(X0_39)
    | l1_pre_topc(k1_pre_topc(X0_39,sK1))
    | k1_zfmisc_1(u1_struct_0(X0_39)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_328])).

cnf(c_451,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_417])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(k1_pre_topc(X1,X0),X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(k1_pre_topc(X1,X0))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_57,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1,c_4,c_3])).

cnf(c_58,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_57])).

cnf(c_226,plain,
    ( ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_58,c_8])).

cnf(c_227,plain,
    ( ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | k2_struct_0(k1_pre_topc(X0,sK1)) = sK1 ),
    inference(unflattening,[status(thm)],[c_226])).

cnf(c_418,plain,
    ( ~ l1_pre_topc(X0_39)
    | k1_zfmisc_1(u1_struct_0(X0_39)) != k1_zfmisc_1(u1_struct_0(sK0))
    | k2_struct_0(k1_pre_topc(X0_39,sK1)) = sK1 ),
    inference(subtyping,[status(esa)],[c_227])).

cnf(c_448,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | k2_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_418])).

cnf(c_7,negated_conjecture,
    ( u1_struct_0(k1_pre_topc(sK0,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_421,negated_conjecture,
    ( u1_struct_0(k1_pre_topc(sK0,sK1)) != sK1 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_424,plain,
    ( X0_40 = X0_40 ),
    theory(equality)).

cnf(c_441,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_424])).

cnf(c_9,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_621,c_598,c_597,c_584,c_451,c_448,c_421,c_441,c_9])).


%------------------------------------------------------------------------------
