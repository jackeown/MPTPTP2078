%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:44 EST 2020

% Result     : CounterSatisfiable 1.63s
% Output     : Saturation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 293 expanded)
%              Number of clauses        :   42 (  81 expanded)
%              Number of leaves         :   13 ( 104 expanded)
%              Depth                    :   12
%              Number of atoms          :  208 (1872 expanded)
%              Number of equality atoms :   97 ( 638 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => ( ( v2_tops_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v2_tops_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ( ( v2_tops_2(X2,X0)
                        & X2 = X3
                        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                     => v2_tops_2(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ v2_tops_2(X3,X1)
          & v2_tops_2(X2,X0)
          & X2 = X3
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
     => ( ~ v2_tops_2(sK3,X1)
        & v2_tops_2(X2,X0)
        & sK3 = X2
        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ v2_tops_2(X3,X1)
              & v2_tops_2(X2,X0)
              & X2 = X3
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ? [X3] :
            ( ~ v2_tops_2(X3,X1)
            & v2_tops_2(sK2,X0)
            & sK2 = X3
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ v2_tops_2(X3,sK1)
                & v2_tops_2(X2,X0)
                & X2 = X3
                & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v2_tops_2(X3,X1)
                    & v2_tops_2(X2,X0)
                    & X2 = X3
                    & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,sK0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ~ v2_tops_2(sK3,sK1)
    & v2_tops_2(sK2,sK0)
    & sK2 = sK3
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f20,f19,f18,f17])).

fof(f34,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f31,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    ~ v2_tops_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,(
    v2_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_142,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_141,plain,
    ( ~ v1_tops_2(X0,X1)
    | v1_tops_2(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_140,plain,
    ( ~ v2_tops_2(X0,X1)
    | v2_tops_2(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_138,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_235,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_11,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X0
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_368,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_855,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK0) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_368])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_16,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_38,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_40,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_856,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK0) = X1
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_368])).

cnf(c_1027,plain,
    ( u1_pre_topc(sK0) = X1
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_855,c_16,c_40,c_856])).

cnf(c_1028,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK0) = X1 ),
    inference(renaming,[status(thm)],[c_1027])).

cnf(c_1033,plain,
    ( u1_pre_topc(sK1) = u1_pre_topc(sK0) ),
    inference(equality_resolution,[status(thm)],[c_1028])).

cnf(c_1035,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK1) = X1 ),
    inference(demodulation,[status(thm)],[c_1033,c_1028])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_367,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_830,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK0) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_367])).

cnf(c_39,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_831,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK0) = X0
    | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_367])).

cnf(c_848,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK0) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_831])).

cnf(c_1009,plain,
    ( u1_struct_0(sK0) = X0
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_830,c_15,c_39,c_848])).

cnf(c_1010,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK0) = X0 ),
    inference(renaming,[status(thm)],[c_1009])).

cnf(c_1015,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK0) ),
    inference(equality_resolution,[status(thm)],[c_1010])).

cnf(c_1017,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK1) = X0 ),
    inference(demodulation,[status(thm)],[c_1015,c_1010])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_166,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_14])).

cnf(c_167,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(unflattening,[status(thm)],[c_166])).

cnf(c_364,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_167])).

cnf(c_8,negated_conjecture,
    ( ~ v2_tops_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_9,negated_conjecture,
    ( v2_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_159,plain,
    ( sK0 != sK1
    | sK2 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_9])).

cnf(c_10,negated_conjecture,
    ( sK2 = sK3 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_160,plain,
    ( sK0 != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_159,c_10])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_369,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_366,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.09  % Command    : iproveropt_run.sh %d %s
% 0.09/0.28  % Computer   : n014.cluster.edu
% 0.09/0.28  % Model      : x86_64 x86_64
% 0.09/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.28  % Memory     : 8042.1875MB
% 0.09/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.28  % CPULimit   : 60
% 0.09/0.28  % WCLimit    : 600
% 0.09/0.28  % DateTime   : Tue Dec  1 15:58:22 EST 2020
% 0.09/0.28  % CPUTime    : 
% 0.09/0.29  % Running in FOF mode
% 1.63/0.93  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/0.93  
% 1.63/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.63/0.93  
% 1.63/0.93  ------  iProver source info
% 1.63/0.93  
% 1.63/0.93  git: date: 2020-06-30 10:37:57 +0100
% 1.63/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.63/0.93  git: non_committed_changes: false
% 1.63/0.93  git: last_make_outside_of_git: false
% 1.63/0.93  
% 1.63/0.93  ------ 
% 1.63/0.93  
% 1.63/0.93  ------ Input Options
% 1.63/0.93  
% 1.63/0.93  --out_options                           all
% 1.63/0.93  --tptp_safe_out                         true
% 1.63/0.93  --problem_path                          ""
% 1.63/0.93  --include_path                          ""
% 1.63/0.93  --clausifier                            res/vclausify_rel
% 1.63/0.93  --clausifier_options                    --mode clausify
% 1.63/0.93  --stdin                                 false
% 1.63/0.93  --stats_out                             all
% 1.63/0.93  
% 1.63/0.93  ------ General Options
% 1.63/0.93  
% 1.63/0.93  --fof                                   false
% 1.63/0.93  --time_out_real                         305.
% 1.63/0.93  --time_out_virtual                      -1.
% 1.63/0.93  --symbol_type_check                     false
% 1.63/0.93  --clausify_out                          false
% 1.63/0.93  --sig_cnt_out                           false
% 1.63/0.93  --trig_cnt_out                          false
% 1.63/0.93  --trig_cnt_out_tolerance                1.
% 1.63/0.93  --trig_cnt_out_sk_spl                   false
% 1.63/0.93  --abstr_cl_out                          false
% 1.63/0.93  
% 1.63/0.93  ------ Global Options
% 1.63/0.93  
% 1.63/0.93  --schedule                              default
% 1.63/0.93  --add_important_lit                     false
% 1.63/0.93  --prop_solver_per_cl                    1000
% 1.63/0.93  --min_unsat_core                        false
% 1.63/0.93  --soft_assumptions                      false
% 1.63/0.93  --soft_lemma_size                       3
% 1.63/0.93  --prop_impl_unit_size                   0
% 1.63/0.93  --prop_impl_unit                        []
% 1.63/0.93  --share_sel_clauses                     true
% 1.63/0.93  --reset_solvers                         false
% 1.63/0.93  --bc_imp_inh                            [conj_cone]
% 1.63/0.93  --conj_cone_tolerance                   3.
% 1.63/0.93  --extra_neg_conj                        none
% 1.63/0.93  --large_theory_mode                     true
% 1.63/0.93  --prolific_symb_bound                   200
% 1.63/0.93  --lt_threshold                          2000
% 1.63/0.93  --clause_weak_htbl                      true
% 1.63/0.93  --gc_record_bc_elim                     false
% 1.63/0.93  
% 1.63/0.93  ------ Preprocessing Options
% 1.63/0.93  
% 1.63/0.93  --preprocessing_flag                    true
% 1.63/0.93  --time_out_prep_mult                    0.1
% 1.63/0.93  --splitting_mode                        input
% 1.63/0.93  --splitting_grd                         true
% 1.63/0.93  --splitting_cvd                         false
% 1.63/0.93  --splitting_cvd_svl                     false
% 1.63/0.93  --splitting_nvd                         32
% 1.63/0.93  --sub_typing                            true
% 1.63/0.93  --prep_gs_sim                           true
% 1.63/0.93  --prep_unflatten                        true
% 1.63/0.93  --prep_res_sim                          true
% 1.63/0.93  --prep_upred                            true
% 1.63/0.93  --prep_sem_filter                       exhaustive
% 1.63/0.93  --prep_sem_filter_out                   false
% 1.63/0.93  --pred_elim                             true
% 1.63/0.93  --res_sim_input                         true
% 1.63/0.93  --eq_ax_congr_red                       true
% 1.63/0.93  --pure_diseq_elim                       true
% 1.63/0.93  --brand_transform                       false
% 1.63/0.93  --non_eq_to_eq                          false
% 1.63/0.93  --prep_def_merge                        true
% 1.63/0.93  --prep_def_merge_prop_impl              false
% 1.63/0.93  --prep_def_merge_mbd                    true
% 1.63/0.93  --prep_def_merge_tr_red                 false
% 1.63/0.93  --prep_def_merge_tr_cl                  false
% 1.63/0.93  --smt_preprocessing                     true
% 1.63/0.93  --smt_ac_axioms                         fast
% 1.63/0.93  --preprocessed_out                      false
% 1.63/0.93  --preprocessed_stats                    false
% 1.63/0.93  
% 1.63/0.93  ------ Abstraction refinement Options
% 1.63/0.93  
% 1.63/0.93  --abstr_ref                             []
% 1.63/0.93  --abstr_ref_prep                        false
% 1.63/0.93  --abstr_ref_until_sat                   false
% 1.63/0.93  --abstr_ref_sig_restrict                funpre
% 1.63/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 1.63/0.93  --abstr_ref_under                       []
% 1.63/0.93  
% 1.63/0.93  ------ SAT Options
% 1.63/0.93  
% 1.63/0.93  --sat_mode                              false
% 1.63/0.93  --sat_fm_restart_options                ""
% 1.63/0.93  --sat_gr_def                            false
% 1.63/0.93  --sat_epr_types                         true
% 1.63/0.93  --sat_non_cyclic_types                  false
% 1.63/0.93  --sat_finite_models                     false
% 1.63/0.93  --sat_fm_lemmas                         false
% 1.63/0.93  --sat_fm_prep                           false
% 1.63/0.93  --sat_fm_uc_incr                        true
% 1.63/0.93  --sat_out_model                         small
% 1.63/0.93  --sat_out_clauses                       false
% 1.63/0.93  
% 1.63/0.93  ------ QBF Options
% 1.63/0.93  
% 1.63/0.93  --qbf_mode                              false
% 1.63/0.93  --qbf_elim_univ                         false
% 1.63/0.93  --qbf_dom_inst                          none
% 1.63/0.93  --qbf_dom_pre_inst                      false
% 1.63/0.93  --qbf_sk_in                             false
% 1.63/0.93  --qbf_pred_elim                         true
% 1.63/0.93  --qbf_split                             512
% 1.63/0.93  
% 1.63/0.93  ------ BMC1 Options
% 1.63/0.93  
% 1.63/0.93  --bmc1_incremental                      false
% 1.63/0.93  --bmc1_axioms                           reachable_all
% 1.63/0.93  --bmc1_min_bound                        0
% 1.63/0.93  --bmc1_max_bound                        -1
% 1.63/0.93  --bmc1_max_bound_default                -1
% 1.63/0.93  --bmc1_symbol_reachability              true
% 1.63/0.93  --bmc1_property_lemmas                  false
% 1.63/0.93  --bmc1_k_induction                      false
% 1.63/0.93  --bmc1_non_equiv_states                 false
% 1.63/0.93  --bmc1_deadlock                         false
% 1.63/0.93  --bmc1_ucm                              false
% 1.63/0.93  --bmc1_add_unsat_core                   none
% 1.63/0.93  --bmc1_unsat_core_children              false
% 1.63/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 1.63/0.93  --bmc1_out_stat                         full
% 1.63/0.93  --bmc1_ground_init                      false
% 1.63/0.93  --bmc1_pre_inst_next_state              false
% 1.63/0.93  --bmc1_pre_inst_state                   false
% 1.63/0.93  --bmc1_pre_inst_reach_state             false
% 1.63/0.93  --bmc1_out_unsat_core                   false
% 1.63/0.93  --bmc1_aig_witness_out                  false
% 1.63/0.93  --bmc1_verbose                          false
% 1.63/0.93  --bmc1_dump_clauses_tptp                false
% 1.63/0.93  --bmc1_dump_unsat_core_tptp             false
% 1.63/0.93  --bmc1_dump_file                        -
% 1.63/0.93  --bmc1_ucm_expand_uc_limit              128
% 1.63/0.93  --bmc1_ucm_n_expand_iterations          6
% 1.63/0.93  --bmc1_ucm_extend_mode                  1
% 1.63/0.93  --bmc1_ucm_init_mode                    2
% 1.63/0.93  --bmc1_ucm_cone_mode                    none
% 1.63/0.93  --bmc1_ucm_reduced_relation_type        0
% 1.63/0.93  --bmc1_ucm_relax_model                  4
% 1.63/0.93  --bmc1_ucm_full_tr_after_sat            true
% 1.63/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 1.63/0.93  --bmc1_ucm_layered_model                none
% 1.63/0.93  --bmc1_ucm_max_lemma_size               10
% 1.63/0.93  
% 1.63/0.93  ------ AIG Options
% 1.63/0.93  
% 1.63/0.93  --aig_mode                              false
% 1.63/0.93  
% 1.63/0.93  ------ Instantiation Options
% 1.63/0.93  
% 1.63/0.93  --instantiation_flag                    true
% 1.63/0.93  --inst_sos_flag                         false
% 1.63/0.93  --inst_sos_phase                        true
% 1.63/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.63/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.63/0.93  --inst_lit_sel_side                     num_symb
% 1.63/0.93  --inst_solver_per_active                1400
% 1.63/0.93  --inst_solver_calls_frac                1.
% 1.63/0.93  --inst_passive_queue_type               priority_queues
% 1.63/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.63/0.93  --inst_passive_queues_freq              [25;2]
% 1.63/0.93  --inst_dismatching                      true
% 1.63/0.93  --inst_eager_unprocessed_to_passive     true
% 1.63/0.93  --inst_prop_sim_given                   true
% 1.63/0.93  --inst_prop_sim_new                     false
% 1.63/0.93  --inst_subs_new                         false
% 1.63/0.93  --inst_eq_res_simp                      false
% 1.63/0.93  --inst_subs_given                       false
% 1.63/0.93  --inst_orphan_elimination               true
% 1.63/0.93  --inst_learning_loop_flag               true
% 1.63/0.93  --inst_learning_start                   3000
% 1.63/0.93  --inst_learning_factor                  2
% 1.63/0.93  --inst_start_prop_sim_after_learn       3
% 1.63/0.93  --inst_sel_renew                        solver
% 1.63/0.93  --inst_lit_activity_flag                true
% 1.63/0.93  --inst_restr_to_given                   false
% 1.63/0.93  --inst_activity_threshold               500
% 1.63/0.93  --inst_out_proof                        true
% 1.63/0.93  
% 1.63/0.93  ------ Resolution Options
% 1.63/0.93  
% 1.63/0.93  --resolution_flag                       true
% 1.63/0.93  --res_lit_sel                           adaptive
% 1.63/0.93  --res_lit_sel_side                      none
% 1.63/0.93  --res_ordering                          kbo
% 1.63/0.93  --res_to_prop_solver                    active
% 1.63/0.93  --res_prop_simpl_new                    false
% 1.63/0.93  --res_prop_simpl_given                  true
% 1.63/0.93  --res_passive_queue_type                priority_queues
% 1.63/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.63/0.93  --res_passive_queues_freq               [15;5]
% 1.63/0.93  --res_forward_subs                      full
% 1.63/0.93  --res_backward_subs                     full
% 1.63/0.93  --res_forward_subs_resolution           true
% 1.63/0.93  --res_backward_subs_resolution          true
% 1.63/0.93  --res_orphan_elimination                true
% 1.63/0.93  --res_time_limit                        2.
% 1.63/0.93  --res_out_proof                         true
% 1.63/0.93  
% 1.63/0.93  ------ Superposition Options
% 1.63/0.93  
% 1.63/0.93  --superposition_flag                    true
% 1.63/0.93  --sup_passive_queue_type                priority_queues
% 1.63/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.63/0.93  --sup_passive_queues_freq               [8;1;4]
% 1.63/0.93  --demod_completeness_check              fast
% 1.63/0.93  --demod_use_ground                      true
% 1.63/0.93  --sup_to_prop_solver                    passive
% 1.63/0.93  --sup_prop_simpl_new                    true
% 1.63/0.93  --sup_prop_simpl_given                  true
% 1.63/0.93  --sup_fun_splitting                     false
% 1.63/0.93  --sup_smt_interval                      50000
% 1.63/0.93  
% 1.63/0.93  ------ Superposition Simplification Setup
% 1.63/0.93  
% 1.63/0.93  --sup_indices_passive                   []
% 1.63/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.63/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.63/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.63/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 1.63/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.63/0.93  --sup_full_bw                           [BwDemod]
% 1.63/0.93  --sup_immed_triv                        [TrivRules]
% 1.63/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.63/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.63/0.93  --sup_immed_bw_main                     []
% 1.63/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.63/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 1.63/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.63/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.63/0.93  
% 1.63/0.93  ------ Combination Options
% 1.63/0.93  
% 1.63/0.93  --comb_res_mult                         3
% 1.63/0.93  --comb_sup_mult                         2
% 1.63/0.93  --comb_inst_mult                        10
% 1.63/0.93  
% 1.63/0.93  ------ Debug Options
% 1.63/0.93  
% 1.63/0.93  --dbg_backtrace                         false
% 1.63/0.93  --dbg_dump_prop_clauses                 false
% 1.63/0.93  --dbg_dump_prop_clauses_file            -
% 1.63/0.93  --dbg_out_stat                          false
% 1.63/0.93  ------ Parsing...
% 1.63/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.63/0.93  
% 1.63/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.63/0.93  
% 1.63/0.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.63/0.93  
% 1.63/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.63/0.93  ------ Proving...
% 1.63/0.93  ------ Problem Properties 
% 1.63/0.93  
% 1.63/0.93  
% 1.63/0.93  clauses                                 10
% 1.63/0.93  conjectures                             4
% 1.63/0.93  EPR                                     2
% 1.63/0.93  Horn                                    10
% 1.63/0.93  unary                                   7
% 1.63/0.93  binary                                  1
% 1.63/0.93  lits                                    15
% 1.63/0.93  lits eq                                 7
% 1.63/0.93  fd_pure                                 0
% 1.63/0.93  fd_pseudo                               0
% 1.63/0.93  fd_cond                                 0
% 1.63/0.93  fd_pseudo_cond                          2
% 1.63/0.93  AC symbols                              0
% 1.63/0.93  
% 1.63/0.93  ------ Schedule dynamic 5 is on 
% 1.63/0.93  
% 1.63/0.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.63/0.93  
% 1.63/0.93  
% 1.63/0.93  ------ 
% 1.63/0.93  Current options:
% 1.63/0.93  ------ 
% 1.63/0.93  
% 1.63/0.93  ------ Input Options
% 1.63/0.93  
% 1.63/0.93  --out_options                           all
% 1.63/0.93  --tptp_safe_out                         true
% 1.63/0.93  --problem_path                          ""
% 1.63/0.93  --include_path                          ""
% 1.63/0.93  --clausifier                            res/vclausify_rel
% 1.63/0.93  --clausifier_options                    --mode clausify
% 1.63/0.93  --stdin                                 false
% 1.63/0.93  --stats_out                             all
% 1.63/0.93  
% 1.63/0.93  ------ General Options
% 1.63/0.93  
% 1.63/0.93  --fof                                   false
% 1.63/0.93  --time_out_real                         305.
% 1.63/0.93  --time_out_virtual                      -1.
% 1.63/0.93  --symbol_type_check                     false
% 1.63/0.93  --clausify_out                          false
% 1.63/0.93  --sig_cnt_out                           false
% 1.63/0.93  --trig_cnt_out                          false
% 1.63/0.93  --trig_cnt_out_tolerance                1.
% 1.63/0.93  --trig_cnt_out_sk_spl                   false
% 1.63/0.93  --abstr_cl_out                          false
% 1.63/0.93  
% 1.63/0.93  ------ Global Options
% 1.63/0.93  
% 1.63/0.93  --schedule                              default
% 1.63/0.93  --add_important_lit                     false
% 1.63/0.93  --prop_solver_per_cl                    1000
% 1.63/0.93  --min_unsat_core                        false
% 1.63/0.93  --soft_assumptions                      false
% 1.63/0.93  --soft_lemma_size                       3
% 1.63/0.93  --prop_impl_unit_size                   0
% 1.63/0.93  --prop_impl_unit                        []
% 1.63/0.93  --share_sel_clauses                     true
% 1.63/0.93  --reset_solvers                         false
% 1.63/0.93  --bc_imp_inh                            [conj_cone]
% 1.63/0.93  --conj_cone_tolerance                   3.
% 1.63/0.93  --extra_neg_conj                        none
% 1.63/0.93  --large_theory_mode                     true
% 1.63/0.93  --prolific_symb_bound                   200
% 1.63/0.93  --lt_threshold                          2000
% 1.63/0.93  --clause_weak_htbl                      true
% 1.63/0.93  --gc_record_bc_elim                     false
% 1.63/0.93  
% 1.63/0.93  ------ Preprocessing Options
% 1.63/0.93  
% 1.63/0.93  --preprocessing_flag                    true
% 1.63/0.93  --time_out_prep_mult                    0.1
% 1.63/0.93  --splitting_mode                        input
% 1.63/0.93  --splitting_grd                         true
% 1.63/0.93  --splitting_cvd                         false
% 1.63/0.93  --splitting_cvd_svl                     false
% 1.63/0.93  --splitting_nvd                         32
% 1.63/0.93  --sub_typing                            true
% 1.63/0.93  --prep_gs_sim                           true
% 1.63/0.93  --prep_unflatten                        true
% 1.63/0.93  --prep_res_sim                          true
% 1.63/0.93  --prep_upred                            true
% 1.63/0.93  --prep_sem_filter                       exhaustive
% 1.63/0.93  --prep_sem_filter_out                   false
% 1.63/0.93  --pred_elim                             true
% 1.63/0.93  --res_sim_input                         true
% 1.63/0.93  --eq_ax_congr_red                       true
% 1.63/0.93  --pure_diseq_elim                       true
% 1.63/0.93  --brand_transform                       false
% 1.63/0.93  --non_eq_to_eq                          false
% 1.63/0.93  --prep_def_merge                        true
% 1.63/0.93  --prep_def_merge_prop_impl              false
% 1.63/0.93  --prep_def_merge_mbd                    true
% 1.63/0.93  --prep_def_merge_tr_red                 false
% 1.63/0.93  --prep_def_merge_tr_cl                  false
% 1.63/0.93  --smt_preprocessing                     true
% 1.63/0.93  --smt_ac_axioms                         fast
% 1.63/0.93  --preprocessed_out                      false
% 1.63/0.93  --preprocessed_stats                    false
% 1.63/0.93  
% 1.63/0.93  ------ Abstraction refinement Options
% 1.63/0.93  
% 1.63/0.93  --abstr_ref                             []
% 1.63/0.93  --abstr_ref_prep                        false
% 1.63/0.93  --abstr_ref_until_sat                   false
% 1.63/0.93  --abstr_ref_sig_restrict                funpre
% 1.63/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 1.63/0.93  --abstr_ref_under                       []
% 1.63/0.93  
% 1.63/0.93  ------ SAT Options
% 1.63/0.93  
% 1.63/0.93  --sat_mode                              false
% 1.63/0.93  --sat_fm_restart_options                ""
% 1.63/0.93  --sat_gr_def                            false
% 1.63/0.93  --sat_epr_types                         true
% 1.63/0.93  --sat_non_cyclic_types                  false
% 1.63/0.93  --sat_finite_models                     false
% 1.63/0.93  --sat_fm_lemmas                         false
% 1.63/0.93  --sat_fm_prep                           false
% 1.63/0.93  --sat_fm_uc_incr                        true
% 1.63/0.93  --sat_out_model                         small
% 1.63/0.93  --sat_out_clauses                       false
% 1.63/0.93  
% 1.63/0.93  ------ QBF Options
% 1.63/0.93  
% 1.63/0.93  --qbf_mode                              false
% 1.63/0.93  --qbf_elim_univ                         false
% 1.63/0.93  --qbf_dom_inst                          none
% 1.63/0.93  --qbf_dom_pre_inst                      false
% 1.63/0.93  --qbf_sk_in                             false
% 1.63/0.93  --qbf_pred_elim                         true
% 1.63/0.93  --qbf_split                             512
% 1.63/0.93  
% 1.63/0.93  ------ BMC1 Options
% 1.63/0.93  
% 1.63/0.93  --bmc1_incremental                      false
% 1.63/0.93  --bmc1_axioms                           reachable_all
% 1.63/0.93  --bmc1_min_bound                        0
% 1.63/0.93  --bmc1_max_bound                        -1
% 1.63/0.93  --bmc1_max_bound_default                -1
% 1.63/0.93  --bmc1_symbol_reachability              true
% 1.63/0.93  --bmc1_property_lemmas                  false
% 1.63/0.93  --bmc1_k_induction                      false
% 1.63/0.93  --bmc1_non_equiv_states                 false
% 1.63/0.93  --bmc1_deadlock                         false
% 1.63/0.93  --bmc1_ucm                              false
% 1.63/0.93  --bmc1_add_unsat_core                   none
% 1.63/0.93  --bmc1_unsat_core_children              false
% 1.63/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 1.63/0.93  --bmc1_out_stat                         full
% 1.63/0.93  --bmc1_ground_init                      false
% 1.63/0.93  --bmc1_pre_inst_next_state              false
% 1.63/0.93  --bmc1_pre_inst_state                   false
% 1.63/0.93  --bmc1_pre_inst_reach_state             false
% 1.63/0.93  --bmc1_out_unsat_core                   false
% 1.63/0.93  --bmc1_aig_witness_out                  false
% 1.63/0.93  --bmc1_verbose                          false
% 1.63/0.93  --bmc1_dump_clauses_tptp                false
% 1.63/0.93  --bmc1_dump_unsat_core_tptp             false
% 1.63/0.93  --bmc1_dump_file                        -
% 1.63/0.93  --bmc1_ucm_expand_uc_limit              128
% 1.63/0.93  --bmc1_ucm_n_expand_iterations          6
% 1.63/0.93  --bmc1_ucm_extend_mode                  1
% 1.63/0.93  --bmc1_ucm_init_mode                    2
% 1.63/0.93  --bmc1_ucm_cone_mode                    none
% 1.63/0.93  --bmc1_ucm_reduced_relation_type        0
% 1.63/0.93  --bmc1_ucm_relax_model                  4
% 1.63/0.93  --bmc1_ucm_full_tr_after_sat            true
% 1.63/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 1.63/0.93  --bmc1_ucm_layered_model                none
% 1.63/0.93  --bmc1_ucm_max_lemma_size               10
% 1.63/0.93  
% 1.63/0.93  ------ AIG Options
% 1.63/0.93  
% 1.63/0.93  --aig_mode                              false
% 1.63/0.93  
% 1.63/0.93  ------ Instantiation Options
% 1.63/0.93  
% 1.63/0.93  --instantiation_flag                    true
% 1.63/0.93  --inst_sos_flag                         false
% 1.63/0.93  --inst_sos_phase                        true
% 1.63/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.63/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.63/0.93  --inst_lit_sel_side                     none
% 1.63/0.93  --inst_solver_per_active                1400
% 1.63/0.93  --inst_solver_calls_frac                1.
% 1.63/0.93  --inst_passive_queue_type               priority_queues
% 1.63/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.63/0.93  --inst_passive_queues_freq              [25;2]
% 1.63/0.93  --inst_dismatching                      true
% 1.63/0.93  --inst_eager_unprocessed_to_passive     true
% 1.63/0.93  --inst_prop_sim_given                   true
% 1.63/0.93  --inst_prop_sim_new                     false
% 1.63/0.93  --inst_subs_new                         false
% 1.63/0.93  --inst_eq_res_simp                      false
% 1.63/0.93  --inst_subs_given                       false
% 1.63/0.93  --inst_orphan_elimination               true
% 1.63/0.93  --inst_learning_loop_flag               true
% 1.63/0.93  --inst_learning_start                   3000
% 1.63/0.93  --inst_learning_factor                  2
% 1.63/0.93  --inst_start_prop_sim_after_learn       3
% 1.63/0.93  --inst_sel_renew                        solver
% 1.63/0.93  --inst_lit_activity_flag                true
% 1.63/0.93  --inst_restr_to_given                   false
% 1.63/0.93  --inst_activity_threshold               500
% 1.63/0.93  --inst_out_proof                        true
% 1.63/0.93  
% 1.63/0.93  ------ Resolution Options
% 1.63/0.93  
% 1.63/0.93  --resolution_flag                       false
% 1.63/0.93  --res_lit_sel                           adaptive
% 1.63/0.93  --res_lit_sel_side                      none
% 1.63/0.93  --res_ordering                          kbo
% 1.63/0.93  --res_to_prop_solver                    active
% 1.63/0.93  --res_prop_simpl_new                    false
% 1.63/0.93  --res_prop_simpl_given                  true
% 1.63/0.93  --res_passive_queue_type                priority_queues
% 1.63/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.63/0.93  --res_passive_queues_freq               [15;5]
% 1.63/0.93  --res_forward_subs                      full
% 1.63/0.93  --res_backward_subs                     full
% 1.63/0.93  --res_forward_subs_resolution           true
% 1.63/0.93  --res_backward_subs_resolution          true
% 1.63/0.93  --res_orphan_elimination                true
% 1.63/0.93  --res_time_limit                        2.
% 1.63/0.93  --res_out_proof                         true
% 1.63/0.93  
% 1.63/0.93  ------ Superposition Options
% 1.63/0.93  
% 1.63/0.93  --superposition_flag                    true
% 1.63/0.93  --sup_passive_queue_type                priority_queues
% 1.63/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.63/0.93  --sup_passive_queues_freq               [8;1;4]
% 1.63/0.93  --demod_completeness_check              fast
% 1.63/0.93  --demod_use_ground                      true
% 1.63/0.93  --sup_to_prop_solver                    passive
% 1.63/0.93  --sup_prop_simpl_new                    true
% 1.63/0.93  --sup_prop_simpl_given                  true
% 1.63/0.93  --sup_fun_splitting                     false
% 1.63/0.93  --sup_smt_interval                      50000
% 1.63/0.93  
% 1.63/0.93  ------ Superposition Simplification Setup
% 1.63/0.93  
% 1.63/0.93  --sup_indices_passive                   []
% 1.63/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.63/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.63/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.63/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 1.63/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.63/0.93  --sup_full_bw                           [BwDemod]
% 1.63/0.93  --sup_immed_triv                        [TrivRules]
% 1.63/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.63/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.63/0.93  --sup_immed_bw_main                     []
% 1.63/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.63/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 1.63/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.63/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.63/0.93  
% 1.63/0.93  ------ Combination Options
% 1.63/0.93  
% 1.63/0.93  --comb_res_mult                         3
% 1.63/0.93  --comb_sup_mult                         2
% 1.63/0.93  --comb_inst_mult                        10
% 1.63/0.93  
% 1.63/0.93  ------ Debug Options
% 1.63/0.93  
% 1.63/0.93  --dbg_backtrace                         false
% 1.63/0.93  --dbg_dump_prop_clauses                 false
% 1.63/0.93  --dbg_dump_prop_clauses_file            -
% 1.63/0.93  --dbg_out_stat                          false
% 1.63/0.93  
% 1.63/0.93  
% 1.63/0.93  
% 1.63/0.93  
% 1.63/0.93  ------ Proving...
% 1.63/0.93  
% 1.63/0.93  
% 1.63/0.93  % SZS status CounterSatisfiable for theBenchmark.p
% 1.63/0.93  
% 1.63/0.93  % SZS output start Saturation for theBenchmark.p
% 1.63/0.93  
% 1.63/0.93  fof(f6,conjecture,(
% 1.63/0.93    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => ((v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tops_2(X3,X1))))))),
% 1.63/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.63/0.93  
% 1.63/0.93  fof(f7,negated_conjecture,(
% 1.63/0.93    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => ((v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tops_2(X3,X1))))))),
% 1.63/0.93    inference(negated_conjecture,[],[f6])).
% 1.63/0.93  
% 1.63/0.93  fof(f13,plain,(
% 1.63/0.93    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v2_tops_2(X3,X1) & (v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 1.63/0.93    inference(ennf_transformation,[],[f7])).
% 1.63/0.93  
% 1.63/0.93  fof(f14,plain,(
% 1.63/0.93    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 1.63/0.93    inference(flattening,[],[f13])).
% 1.63/0.93  
% 1.63/0.93  fof(f20,plain,(
% 1.63/0.93    ( ! [X2,X0,X1] : (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) => (~v2_tops_2(sK3,X1) & v2_tops_2(X2,X0) & sK3 = X2 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))))) )),
% 1.63/0.93    introduced(choice_axiom,[])).
% 1.63/0.93  
% 1.63/0.93  fof(f19,plain,(
% 1.63/0.93    ( ! [X0,X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(sK2,X0) & sK2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 1.63/0.93    introduced(choice_axiom,[])).
% 1.63/0.93  
% 1.63/0.93  fof(f18,plain,(
% 1.63/0.93    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : (~v2_tops_2(X3,sK1) & v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(sK1))) )),
% 1.63/0.93    introduced(choice_axiom,[])).
% 1.63/0.93  
% 1.63/0.93  fof(f17,plain,(
% 1.63/0.93    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v2_tops_2(X3,X1) & v2_tops_2(X2,sK0) & X2 = X3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(X1)) & l1_pre_topc(sK0))),
% 1.63/0.93    introduced(choice_axiom,[])).
% 1.63/0.93  
% 1.63/0.93  fof(f21,plain,(
% 1.63/0.93    (((~v2_tops_2(sK3,sK1) & v2_tops_2(sK2,sK0) & sK2 = sK3 & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 1.63/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f20,f19,f18,f17])).
% 1.63/0.93  
% 1.63/0.93  fof(f34,plain,(
% 1.63/0.93    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 1.63/0.93    inference(cnf_transformation,[],[f21])).
% 1.63/0.93  
% 1.63/0.93  fof(f3,axiom,(
% 1.63/0.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 1.63/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.63/0.93  
% 1.63/0.93  fof(f10,plain,(
% 1.63/0.93    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.63/0.93    inference(ennf_transformation,[],[f3])).
% 1.63/0.93  
% 1.63/0.93  fof(f25,plain,(
% 1.63/0.93    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.63/0.93    inference(cnf_transformation,[],[f10])).
% 1.63/0.93  
% 1.63/0.93  fof(f30,plain,(
% 1.63/0.93    l1_pre_topc(sK0)),
% 1.63/0.93    inference(cnf_transformation,[],[f21])).
% 1.63/0.93  
% 1.63/0.93  fof(f2,axiom,(
% 1.63/0.93    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.63/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.63/0.93  
% 1.63/0.93  fof(f9,plain,(
% 1.63/0.93    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.63/0.93    inference(ennf_transformation,[],[f2])).
% 1.63/0.93  
% 1.63/0.93  fof(f23,plain,(
% 1.63/0.93    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.63/0.93    inference(cnf_transformation,[],[f9])).
% 1.63/0.93  
% 1.63/0.93  fof(f24,plain,(
% 1.63/0.93    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.63/0.93    inference(cnf_transformation,[],[f10])).
% 1.63/0.93  
% 1.63/0.93  fof(f31,plain,(
% 1.63/0.93    l1_pre_topc(sK1)),
% 1.63/0.93    inference(cnf_transformation,[],[f21])).
% 1.63/0.93  
% 1.63/0.93  fof(f37,plain,(
% 1.63/0.93    ~v2_tops_2(sK3,sK1)),
% 1.63/0.93    inference(cnf_transformation,[],[f21])).
% 1.63/0.93  
% 1.63/0.93  fof(f36,plain,(
% 1.63/0.93    v2_tops_2(sK2,sK0)),
% 1.63/0.93    inference(cnf_transformation,[],[f21])).
% 1.63/0.93  
% 1.63/0.93  fof(f35,plain,(
% 1.63/0.93    sK2 = sK3),
% 1.63/0.93    inference(cnf_transformation,[],[f21])).
% 1.63/0.93  
% 1.63/0.93  fof(f1,axiom,(
% 1.63/0.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.63/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.63/0.93  
% 1.63/0.93  fof(f8,plain,(
% 1.63/0.93    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.63/0.93    inference(ennf_transformation,[],[f1])).
% 1.63/0.93  
% 1.63/0.93  fof(f22,plain,(
% 1.63/0.93    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.63/0.93    inference(cnf_transformation,[],[f8])).
% 1.63/0.93  
% 1.63/0.93  fof(f33,plain,(
% 1.63/0.93    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.63/0.93    inference(cnf_transformation,[],[f21])).
% 1.63/0.93  
% 1.63/0.93  cnf(c_142,plain,
% 1.63/0.93      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,X2) | X2 != X1 ),
% 1.63/0.93      theory(equality) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_141,plain,
% 1.63/0.93      ( ~ v1_tops_2(X0,X1) | v1_tops_2(X2,X1) | X2 != X0 ),
% 1.63/0.93      theory(equality) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_140,plain,
% 1.63/0.93      ( ~ v2_tops_2(X0,X1) | v2_tops_2(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.63/0.93      theory(equality) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_138,plain,
% 1.63/0.93      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | X1 != X0 ),
% 1.63/0.93      theory(equality) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_235,plain,( X0_2 = X0_2 ),theory(equality) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_11,negated_conjecture,
% 1.63/0.93      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
% 1.63/0.93      inference(cnf_transformation,[],[f34]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_2,plain,
% 1.63/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.63/0.93      | X2 = X0
% 1.63/0.93      | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
% 1.63/0.93      inference(cnf_transformation,[],[f25]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_368,plain,
% 1.63/0.93      ( X0 = X1
% 1.63/0.93      | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
% 1.63/0.93      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
% 1.63/0.93      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_855,plain,
% 1.63/0.93      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 1.63/0.93      | u1_pre_topc(sK0) = X1
% 1.63/0.93      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 1.63/0.93      inference(superposition,[status(thm)],[c_11,c_368]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_15,negated_conjecture,
% 1.63/0.93      ( l1_pre_topc(sK0) ),
% 1.63/0.93      inference(cnf_transformation,[],[f30]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_16,plain,
% 1.63/0.93      ( l1_pre_topc(sK0) = iProver_top ),
% 1.63/0.93      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_1,plain,
% 1.63/0.93      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 1.63/0.93      | ~ l1_pre_topc(X0) ),
% 1.63/0.93      inference(cnf_transformation,[],[f23]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_38,plain,
% 1.63/0.93      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 1.63/0.93      | l1_pre_topc(X0) != iProver_top ),
% 1.63/0.93      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_40,plain,
% 1.63/0.93      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 1.63/0.93      | l1_pre_topc(sK0) != iProver_top ),
% 1.63/0.93      inference(instantiation,[status(thm)],[c_38]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_856,plain,
% 1.63/0.93      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 1.63/0.93      | u1_pre_topc(sK0) = X1
% 1.63/0.93      | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 1.63/0.93      inference(superposition,[status(thm)],[c_11,c_368]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_1027,plain,
% 1.63/0.93      ( u1_pre_topc(sK0) = X1
% 1.63/0.93      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1) ),
% 1.63/0.93      inference(global_propositional_subsumption,
% 1.63/0.93                [status(thm)],
% 1.63/0.93                [c_855,c_16,c_40,c_856]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_1028,plain,
% 1.63/0.93      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 1.63/0.93      | u1_pre_topc(sK0) = X1 ),
% 1.63/0.93      inference(renaming,[status(thm)],[c_1027]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_1033,plain,
% 1.63/0.93      ( u1_pre_topc(sK1) = u1_pre_topc(sK0) ),
% 1.63/0.93      inference(equality_resolution,[status(thm)],[c_1028]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_1035,plain,
% 1.63/0.93      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 1.63/0.93      | u1_pre_topc(sK1) = X1 ),
% 1.63/0.93      inference(demodulation,[status(thm)],[c_1033,c_1028]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_3,plain,
% 1.63/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.63/0.93      | X2 = X1
% 1.63/0.93      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 1.63/0.93      inference(cnf_transformation,[],[f24]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_367,plain,
% 1.63/0.93      ( X0 = X1
% 1.63/0.93      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 1.63/0.93      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 1.63/0.93      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_830,plain,
% 1.63/0.93      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 1.63/0.93      | u1_struct_0(sK0) = X0
% 1.63/0.93      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 1.63/0.93      inference(superposition,[status(thm)],[c_11,c_367]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_39,plain,
% 1.63/0.93      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 1.63/0.93      | ~ l1_pre_topc(sK0) ),
% 1.63/0.93      inference(instantiation,[status(thm)],[c_1]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_831,plain,
% 1.63/0.93      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 1.63/0.93      | u1_struct_0(sK0) = X0
% 1.63/0.93      | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 1.63/0.93      inference(superposition,[status(thm)],[c_11,c_367]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_848,plain,
% 1.63/0.93      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 1.63/0.93      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 1.63/0.93      | u1_struct_0(sK0) = X0 ),
% 1.63/0.93      inference(predicate_to_equality_rev,[status(thm)],[c_831]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_1009,plain,
% 1.63/0.93      ( u1_struct_0(sK0) = X0
% 1.63/0.93      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1) ),
% 1.63/0.93      inference(global_propositional_subsumption,
% 1.63/0.93                [status(thm)],
% 1.63/0.93                [c_830,c_15,c_39,c_848]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_1010,plain,
% 1.63/0.93      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 1.63/0.93      | u1_struct_0(sK0) = X0 ),
% 1.63/0.93      inference(renaming,[status(thm)],[c_1009]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_1015,plain,
% 1.63/0.93      ( u1_struct_0(sK1) = u1_struct_0(sK0) ),
% 1.63/0.93      inference(equality_resolution,[status(thm)],[c_1010]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_1017,plain,
% 1.63/0.93      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 1.63/0.93      | u1_struct_0(sK1) = X0 ),
% 1.63/0.93      inference(demodulation,[status(thm)],[c_1015,c_1010]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_14,negated_conjecture,
% 1.63/0.93      ( l1_pre_topc(sK1) ),
% 1.63/0.93      inference(cnf_transformation,[],[f31]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_166,plain,
% 1.63/0.93      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 1.63/0.93      | sK1 != X0 ),
% 1.63/0.93      inference(resolution_lifted,[status(thm)],[c_1,c_14]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_167,plain,
% 1.63/0.93      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
% 1.63/0.93      inference(unflattening,[status(thm)],[c_166]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_364,plain,
% 1.63/0.93      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
% 1.63/0.93      inference(predicate_to_equality,[status(thm)],[c_167]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_8,negated_conjecture,
% 1.63/0.93      ( ~ v2_tops_2(sK3,sK1) ),
% 1.63/0.93      inference(cnf_transformation,[],[f37]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_9,negated_conjecture,
% 1.63/0.93      ( v2_tops_2(sK2,sK0) ),
% 1.63/0.93      inference(cnf_transformation,[],[f36]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_159,plain,
% 1.63/0.93      ( sK0 != sK1 | sK2 != sK3 ),
% 1.63/0.93      inference(resolution_lifted,[status(thm)],[c_8,c_9]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_10,negated_conjecture,
% 1.63/0.93      ( sK2 = sK3 ),
% 1.63/0.93      inference(cnf_transformation,[],[f35]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_160,plain,
% 1.63/0.93      ( sK0 != sK1 ),
% 1.63/0.93      inference(global_propositional_subsumption,[status(thm)],[c_159,c_10]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_0,plain,
% 1.63/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.63/0.93      | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
% 1.63/0.93      inference(cnf_transformation,[],[f22]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_369,plain,
% 1.63/0.93      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 1.63/0.93      | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) = iProver_top ),
% 1.63/0.93      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_12,negated_conjecture,
% 1.63/0.93      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
% 1.63/0.93      inference(cnf_transformation,[],[f33]) ).
% 1.63/0.93  
% 1.63/0.93  cnf(c_366,plain,
% 1.63/0.93      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
% 1.63/0.93      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.63/0.93  
% 1.63/0.93  
% 1.63/0.93  % SZS output end Saturation for theBenchmark.p
% 1.63/0.93  
% 1.63/0.93  ------                               Statistics
% 1.63/0.93  
% 1.63/0.93  ------ General
% 1.63/0.93  
% 1.63/0.93  abstr_ref_over_cycles:                  0
% 1.63/0.93  abstr_ref_under_cycles:                 0
% 1.63/0.93  gc_basic_clause_elim:                   0
% 1.63/0.93  forced_gc_time:                         0
% 1.63/0.93  parsing_time:                           0.015
% 1.63/0.93  unif_index_cands_time:                  0.
% 1.63/0.93  unif_index_add_time:                    0.
% 1.63/0.93  orderings_time:                         0.
% 1.63/0.93  out_proof_time:                         0.
% 1.63/0.93  total_time:                             0.127
% 1.63/0.93  num_of_symbols:                         45
% 1.63/0.93  num_of_terms:                           1921
% 1.63/0.93  
% 1.63/0.93  ------ Preprocessing
% 1.63/0.93  
% 1.63/0.93  num_of_splits:                          0
% 1.63/0.93  num_of_split_atoms:                     0
% 1.63/0.93  num_of_reused_defs:                     0
% 1.63/0.93  num_eq_ax_congr_red:                    7
% 1.63/0.93  num_of_sem_filtered_clauses:            1
% 1.63/0.93  num_of_subtypes:                        0
% 1.63/0.93  monotx_restored_types:                  0
% 1.63/0.93  sat_num_of_epr_types:                   0
% 1.63/0.93  sat_num_of_non_cyclic_types:            0
% 1.63/0.93  sat_guarded_non_collapsed_types:        0
% 1.63/0.93  num_pure_diseq_elim:                    0
% 1.63/0.93  simp_replaced_by:                       0
% 1.63/0.93  res_preprocessed:                       61
% 1.63/0.93  prep_upred:                             0
% 1.63/0.93  prep_unflattend:                        2
% 1.63/0.93  smt_new_axioms:                         0
% 1.63/0.93  pred_elim_cands:                        1
% 1.63/0.93  pred_elim:                              4
% 1.63/0.93  pred_elim_cl:                           6
% 1.63/0.93  pred_elim_cycles:                       6
% 1.63/0.93  merged_defs:                            0
% 1.63/0.93  merged_defs_ncl:                        0
% 1.63/0.93  bin_hyper_res:                          0
% 1.63/0.93  prep_cycles:                            4
% 1.63/0.93  pred_elim_time:                         0.001
% 1.63/0.93  splitting_time:                         0.
% 1.63/0.93  sem_filter_time:                        0.
% 1.63/0.93  monotx_time:                            0.001
% 1.63/0.93  subtype_inf_time:                       0.
% 1.63/0.93  
% 1.63/0.93  ------ Problem properties
% 1.63/0.93  
% 1.63/0.93  clauses:                                10
% 1.63/0.93  conjectures:                            4
% 1.63/0.93  epr:                                    2
% 1.63/0.93  horn:                                   10
% 1.63/0.93  ground:                                 7
% 1.63/0.93  unary:                                  7
% 1.63/0.93  binary:                                 1
% 1.63/0.93  lits:                                   15
% 1.63/0.93  lits_eq:                                7
% 1.63/0.93  fd_pure:                                0
% 1.63/0.93  fd_pseudo:                              0
% 1.63/0.93  fd_cond:                                0
% 1.63/0.93  fd_pseudo_cond:                         2
% 1.63/0.93  ac_symbols:                             0
% 1.63/0.93  
% 1.63/0.93  ------ Propositional Solver
% 1.63/0.93  
% 1.63/0.93  prop_solver_calls:                      26
% 1.63/0.93  prop_fast_solver_calls:                 271
% 1.63/0.93  smt_solver_calls:                       0
% 1.63/0.93  smt_fast_solver_calls:                  0
% 1.63/0.93  prop_num_of_clauses:                    693
% 1.63/0.93  prop_preprocess_simplified:             2257
% 1.63/0.93  prop_fo_subsumed:                       4
% 1.63/0.93  prop_solver_time:                       0.
% 1.63/0.93  smt_solver_time:                        0.
% 1.63/0.93  smt_fast_solver_time:                   0.
% 1.63/0.93  prop_fast_solver_time:                  0.
% 1.63/0.93  prop_unsat_core_time:                   0.
% 1.63/0.93  
% 1.63/0.93  ------ QBF
% 1.63/0.93  
% 1.63/0.93  qbf_q_res:                              0
% 1.63/0.93  qbf_num_tautologies:                    0
% 1.63/0.93  qbf_prep_cycles:                        0
% 1.63/0.93  
% 1.63/0.93  ------ BMC1
% 1.63/0.93  
% 1.63/0.93  bmc1_current_bound:                     -1
% 1.63/0.93  bmc1_last_solved_bound:                 -1
% 1.63/0.93  bmc1_unsat_core_size:                   -1
% 1.63/0.93  bmc1_unsat_core_parents_size:           -1
% 1.63/0.93  bmc1_merge_next_fun:                    0
% 1.63/0.93  bmc1_unsat_core_clauses_time:           0.
% 1.63/0.93  
% 1.63/0.93  ------ Instantiation
% 1.63/0.93  
% 1.63/0.93  inst_num_of_clauses:                    212
% 1.63/0.93  inst_num_in_passive:                    82
% 1.63/0.93  inst_num_in_active:                     89
% 1.63/0.93  inst_num_in_unprocessed:                41
% 1.63/0.93  inst_num_of_loops:                      90
% 1.63/0.93  inst_num_of_learning_restarts:          0
% 1.63/0.93  inst_num_moves_active_passive:          0
% 1.63/0.93  inst_lit_activity:                      0
% 1.63/0.93  inst_lit_activity_moves:                0
% 1.63/0.93  inst_num_tautologies:                   0
% 1.63/0.93  inst_num_prop_implied:                  0
% 1.63/0.93  inst_num_existing_simplified:           0
% 1.63/0.93  inst_num_eq_res_simplified:             0
% 1.63/0.93  inst_num_child_elim:                    0
% 1.63/0.93  inst_num_of_dismatching_blockings:      7
% 1.63/0.93  inst_num_of_non_proper_insts:           208
% 1.63/0.93  inst_num_of_duplicates:                 0
% 1.63/0.93  inst_inst_num_from_inst_to_res:         0
% 1.63/0.93  inst_dismatching_checking_time:         0.
% 1.63/0.93  
% 1.63/0.93  ------ Resolution
% 1.63/0.93  
% 1.63/0.93  res_num_of_clauses:                     0
% 1.63/0.93  res_num_in_passive:                     0
% 1.63/0.93  res_num_in_active:                      0
% 1.63/0.93  res_num_of_loops:                       65
% 1.63/0.93  res_forward_subset_subsumed:            13
% 1.63/0.93  res_backward_subset_subsumed:           0
% 1.63/0.93  res_forward_subsumed:                   0
% 1.63/0.93  res_backward_subsumed:                  0
% 1.63/0.93  res_forward_subsumption_resolution:     0
% 1.63/0.93  res_backward_subsumption_resolution:    0
% 1.63/0.93  res_clause_to_clause_subsumption:       40
% 1.63/0.93  res_orphan_elimination:                 0
% 1.63/0.93  res_tautology_del:                      13
% 1.63/0.93  res_num_eq_res_simplified:              0
% 1.63/0.93  res_num_sel_changes:                    0
% 1.63/0.93  res_moves_from_active_to_pass:          0
% 1.63/0.93  
% 1.63/0.93  ------ Superposition
% 1.63/0.93  
% 1.63/0.93  sup_time_total:                         0.
% 1.63/0.93  sup_time_generating:                    0.
% 1.63/0.93  sup_time_sim_full:                      0.
% 1.63/0.93  sup_time_sim_immed:                     0.
% 1.63/0.93  
% 1.63/0.93  sup_num_of_clauses:                     15
% 1.63/0.93  sup_num_in_active:                      11
% 1.63/0.93  sup_num_in_passive:                     4
% 1.63/0.93  sup_num_of_loops:                       17
% 1.63/0.93  sup_fw_superposition:                   6
% 1.63/0.93  sup_bw_superposition:                   4
% 1.63/0.93  sup_immediate_simplified:               2
% 1.63/0.93  sup_given_eliminated:                   2
% 1.63/0.93  comparisons_done:                       0
% 1.63/0.93  comparisons_avoided:                    0
% 1.63/0.93  
% 1.63/0.93  ------ Simplifications
% 1.63/0.93  
% 1.63/0.93  
% 1.63/0.93  sim_fw_subset_subsumed:                 2
% 1.63/0.93  sim_bw_subset_subsumed:                 2
% 1.63/0.93  sim_fw_subsumed:                        0
% 1.63/0.93  sim_bw_subsumed:                        0
% 1.63/0.93  sim_fw_subsumption_res:                 0
% 1.63/0.93  sim_bw_subsumption_res:                 0
% 1.63/0.93  sim_tautology_del:                      0
% 1.63/0.93  sim_eq_tautology_del:                   7
% 1.63/0.93  sim_eq_res_simp:                        0
% 1.63/0.93  sim_fw_demodulated:                     0
% 1.63/0.93  sim_bw_demodulated:                     6
% 1.63/0.93  sim_light_normalised:                   2
% 1.63/0.93  sim_joinable_taut:                      0
% 1.63/0.93  sim_joinable_simp:                      0
% 1.63/0.93  sim_ac_normalised:                      0
% 1.63/0.93  sim_smt_subsumption:                    0
% 1.63/0.93  
%------------------------------------------------------------------------------
