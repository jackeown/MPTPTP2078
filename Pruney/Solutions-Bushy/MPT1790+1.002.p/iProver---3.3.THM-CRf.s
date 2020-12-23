%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1790+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:25 EST 2020

% Result     : Theorem 1.12s
% Output     : CNFRefutation 1.12s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 403 expanded)
%              Number of clauses        :   58 (  95 expanded)
%              Number of leaves         :   11 ( 130 expanded)
%              Depth                    :   22
%              Number of atoms          :  348 (2332 expanded)
%              Number of equality atoms :   82 ( 417 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f34,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
             => ( X1 = X2
               => v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
               => ( X1 = X2
                 => v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X2,k6_tmap_1(X0,X1))
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X2,k6_tmap_1(X0,X1))
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,k6_tmap_1(X0,X1))
          & X1 = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
     => ( ~ v3_pre_topc(sK2,k6_tmap_1(X0,X1))
        & sK2 = X1
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X2,k6_tmap_1(X0,X1))
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v3_pre_topc(X2,k6_tmap_1(X0,sK1))
            & sK1 = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,sK1)))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v3_pre_topc(X2,k6_tmap_1(X0,X1))
                & X1 = X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X2,k6_tmap_1(sK0,X1))
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X1)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ v3_pre_topc(sK2,k6_tmap_1(sK0,sK1))
    & sK1 = sK2
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f26,f25,f24])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    sK1 = sK2 ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r2_hidden(X1,k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k5_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    ~ v3_pre_topc(sK2,k6_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_7,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_17,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_323,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k6_tmap_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_17])).

cnf(c_324,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | l1_pre_topc(k6_tmap_1(sK0,X0))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_16,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_328,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_324,c_16,c_15])).

cnf(c_329,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | l1_pre_topc(k6_tmap_1(sK0,X0)) ),
    inference(renaming,[status(thm)],[c_328])).

cnf(c_739,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | k6_tmap_1(sK0,X0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_329])).

cnf(c_740,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(u1_pre_topc(k6_tmap_1(sK0,X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0))))) ),
    inference(unflattening,[status(thm)],[c_739])).

cnf(c_989,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(u1_pre_topc(k6_tmap_1(sK0,X0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X0))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_740])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_993,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_12,negated_conjecture,
    ( sK1 = sK2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_999,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_993,c_12])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k6_tmap_1(X1,X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_287,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k6_tmap_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_17])).

cnf(c_288,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_pre_topc(k6_tmap_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_292,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_pre_topc(k6_tmap_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_288,c_16,c_15])).

cnf(c_375,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(sK0,X0) != X1
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_292])).

cnf(c_376,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,X0))
    | g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) = k6_tmap_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_380,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) = k6_tmap_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_376,c_16,c_15,c_324])).

cnf(c_991,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) = k6_tmap_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_380])).

cnf(c_1404,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK2)),u1_pre_topc(k6_tmap_1(sK0,sK2))) = k6_tmap_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_999,c_991])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_341,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_17])).

cnf(c_342,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) = k6_tmap_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_341])).

cnf(c_346,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) = k6_tmap_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_342,c_16,c_15])).

cnf(c_992,plain,
    ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) = k6_tmap_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_1206,plain,
    ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK2)) = k6_tmap_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_999,c_992])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X0
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_996,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1479,plain,
    ( k5_tmap_1(sK0,sK2) = X0
    | g1_pre_topc(X1,X0) != k6_tmap_1(sK0,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1206,c_996])).

cnf(c_1724,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,sK2)) = k5_tmap_1(sK0,sK2)
    | m1_subset_1(u1_pre_topc(k6_tmap_1(sK0,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK2))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1404,c_1479])).

cnf(c_670,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,X0))
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_329])).

cnf(c_671,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_670])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,k5_tmap_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_11,negated_conjecture,
    ( ~ v3_pre_topc(sK2,k6_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_222,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | k6_tmap_1(sK0,sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_11])).

cnf(c_223,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
    | ~ r2_hidden(sK2,u1_pre_topc(k6_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_225,plain,
    ( ~ r2_hidden(sK2,u1_pre_topc(k6_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_223,c_13])).

cnf(c_239,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | u1_pre_topc(k6_tmap_1(sK0,sK1)) != k5_tmap_1(X1,X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_225])).

cnf(c_240,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | u1_pre_topc(k6_tmap_1(sK0,sK1)) != k5_tmap_1(X0,sK2) ),
    inference(unflattening,[status(thm)],[c_239])).

cnf(c_270,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | u1_pre_topc(k6_tmap_1(sK0,sK1)) != k5_tmap_1(X0,sK2)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_240,c_17])).

cnf(c_271,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | u1_pre_topc(k6_tmap_1(sK0,sK1)) != k5_tmap_1(sK0,sK2) ),
    inference(unflattening,[status(thm)],[c_270])).

cnf(c_273,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(k6_tmap_1(sK0,sK1)) != k5_tmap_1(sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_271,c_16,c_15])).

cnf(c_274,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | u1_pre_topc(k6_tmap_1(sK0,sK1)) != k5_tmap_1(sK0,sK2) ),
    inference(renaming,[status(thm)],[c_273])).

cnf(c_721,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(k6_tmap_1(sK0,sK1)) != k5_tmap_1(sK0,sK2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_671,c_274])).

cnf(c_988,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,sK1)) != k5_tmap_1(sK0,sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_721])).

cnf(c_1007,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,sK2)) != k5_tmap_1(sK0,sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_988,c_12])).

cnf(c_1010,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,sK2)) != k5_tmap_1(sK0,sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1007,c_999])).

cnf(c_1732,plain,
    ( m1_subset_1(u1_pre_topc(k6_tmap_1(sK0,sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK2))))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1724,c_1010])).

cnf(c_1737,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_989,c_1732])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1737,c_999])).


%------------------------------------------------------------------------------
