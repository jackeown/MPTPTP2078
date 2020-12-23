%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:54 EST 2020

% Result     : Theorem 1.07s
% Output     : CNFRefutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 902 expanded)
%              Number of clauses        :   54 ( 195 expanded)
%              Number of leaves         :    8 ( 207 expanded)
%              Depth                    :   19
%              Number of atoms          :  341 (5639 expanded)
%              Number of equality atoms :  112 (1394 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X1,u1_pre_topc(X0))
              | u1_pre_topc(X0) != k5_tmap_1(X0,X1) )
            & ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,sK1)
          | ~ v3_pre_topc(sK1,X0) )
        & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,sK1)
          | v3_pre_topc(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

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

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f10])).

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

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_12,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_189,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_12])).

cnf(c_190,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(X0,u1_pre_topc(sK0))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | k5_tmap_1(sK0,X0) = u1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_189])).

cnf(c_13,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_11,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_194,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(X0,u1_pre_topc(sK0))
    | k5_tmap_1(sK0,X0) = u1_pre_topc(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_190,c_13,c_11])).

cnf(c_9,negated_conjecture,
    ( v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_103,plain,
    ( v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_260,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ v3_pre_topc(X0,X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_11])).

cnf(c_261,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(X0,u1_pre_topc(sK0))
    | ~ v3_pre_topc(X0,sK0) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_309,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(X0,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_103,c_261])).

cnf(c_310,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_309])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_312,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_310,c_10])).

cnf(c_356,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k5_tmap_1(sK0,X0) = u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) != u1_pre_topc(sK0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_194,c_312])).

cnf(c_357,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_359,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_357,c_10])).

cnf(c_449,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_10,c_357])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_210,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_12])).

cnf(c_211,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(X0,u1_pre_topc(sK0))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | k5_tmap_1(sK0,X0) != u1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_210])).

cnf(c_215,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(X0,u1_pre_topc(sK0))
    | k5_tmap_1(sK0,X0) != u1_pre_topc(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_211,c_13,c_11])).

cnf(c_8,negated_conjecture,
    ( ~ v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_101,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v3_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_275,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | v3_pre_topc(X0,X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_11])).

cnf(c_276,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(X0,u1_pre_topc(sK0))
    | v3_pre_topc(X0,sK0) ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_323,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(X0,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_101,c_276])).

cnf(c_324,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_326,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_324,c_10])).

cnf(c_345,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k5_tmap_1(sK0,X0) != u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) != u1_pre_topc(sK0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_215,c_326])).

cnf(c_346,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_348,plain,
    ( k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_346,c_10])).

cnf(c_447,plain,
    ( k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_10,c_346])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_231,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_12])).

cnf(c_232,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) = k6_tmap_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_231])).

cnf(c_236,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) = k6_tmap_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_232,c_13,c_11])).

cnf(c_419,plain,
    ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) = k6_tmap_1(sK0,X0)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_236])).

cnf(c_420,plain,
    ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) = k6_tmap_1(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X0
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_2,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_290,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_11])).

cnf(c_291,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_407,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) != k1_zfmisc_1(k1_zfmisc_1(X3))
    | u1_pre_topc(sK0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_291])).

cnf(c_408,plain,
    ( X0 = u1_pre_topc(sK0)
    | g1_pre_topc(X1,X0) != g1_pre_topc(X2,u1_pre_topc(sK0))
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) != k1_zfmisc_1(k1_zfmisc_1(X2)) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_745,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | g1_pre_topc(X0,u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) != k1_zfmisc_1(k1_zfmisc_1(X0)) ),
    inference(superposition,[status(thm)],[c_420,c_408])).

cnf(c_757,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(equality_resolution,[status(thm)],[c_745])).

cnf(c_792,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_447,c_10,c_346,c_757])).

cnf(c_795,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_449,c_10,c_346,c_357,c_757])).

cnf(c_799,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_795,c_420])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_799,c_792])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:29:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  % Running in FOF mode
% 1.07/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.07/1.00  
% 1.07/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.07/1.00  
% 1.07/1.00  ------  iProver source info
% 1.07/1.00  
% 1.07/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.07/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.07/1.00  git: non_committed_changes: false
% 1.07/1.00  git: last_make_outside_of_git: false
% 1.07/1.00  
% 1.07/1.00  ------ 
% 1.07/1.00  
% 1.07/1.00  ------ Input Options
% 1.07/1.00  
% 1.07/1.00  --out_options                           all
% 1.07/1.00  --tptp_safe_out                         true
% 1.07/1.00  --problem_path                          ""
% 1.07/1.00  --include_path                          ""
% 1.07/1.00  --clausifier                            res/vclausify_rel
% 1.07/1.00  --clausifier_options                    --mode clausify
% 1.07/1.00  --stdin                                 false
% 1.07/1.00  --stats_out                             all
% 1.07/1.00  
% 1.07/1.00  ------ General Options
% 1.07/1.00  
% 1.07/1.00  --fof                                   false
% 1.07/1.00  --time_out_real                         305.
% 1.07/1.00  --time_out_virtual                      -1.
% 1.07/1.00  --symbol_type_check                     false
% 1.07/1.00  --clausify_out                          false
% 1.07/1.00  --sig_cnt_out                           false
% 1.07/1.00  --trig_cnt_out                          false
% 1.07/1.00  --trig_cnt_out_tolerance                1.
% 1.07/1.00  --trig_cnt_out_sk_spl                   false
% 1.07/1.00  --abstr_cl_out                          false
% 1.07/1.00  
% 1.07/1.00  ------ Global Options
% 1.07/1.00  
% 1.07/1.00  --schedule                              default
% 1.07/1.00  --add_important_lit                     false
% 1.07/1.00  --prop_solver_per_cl                    1000
% 1.07/1.00  --min_unsat_core                        false
% 1.07/1.00  --soft_assumptions                      false
% 1.07/1.00  --soft_lemma_size                       3
% 1.07/1.00  --prop_impl_unit_size                   0
% 1.07/1.00  --prop_impl_unit                        []
% 1.07/1.00  --share_sel_clauses                     true
% 1.07/1.00  --reset_solvers                         false
% 1.07/1.00  --bc_imp_inh                            [conj_cone]
% 1.07/1.00  --conj_cone_tolerance                   3.
% 1.07/1.00  --extra_neg_conj                        none
% 1.07/1.00  --large_theory_mode                     true
% 1.07/1.00  --prolific_symb_bound                   200
% 1.07/1.00  --lt_threshold                          2000
% 1.07/1.00  --clause_weak_htbl                      true
% 1.07/1.00  --gc_record_bc_elim                     false
% 1.07/1.00  
% 1.07/1.00  ------ Preprocessing Options
% 1.07/1.00  
% 1.07/1.00  --preprocessing_flag                    true
% 1.07/1.00  --time_out_prep_mult                    0.1
% 1.07/1.00  --splitting_mode                        input
% 1.07/1.00  --splitting_grd                         true
% 1.07/1.00  --splitting_cvd                         false
% 1.07/1.00  --splitting_cvd_svl                     false
% 1.07/1.00  --splitting_nvd                         32
% 1.07/1.00  --sub_typing                            true
% 1.07/1.00  --prep_gs_sim                           true
% 1.07/1.00  --prep_unflatten                        true
% 1.07/1.00  --prep_res_sim                          true
% 1.07/1.00  --prep_upred                            true
% 1.07/1.00  --prep_sem_filter                       exhaustive
% 1.07/1.00  --prep_sem_filter_out                   false
% 1.07/1.00  --pred_elim                             true
% 1.07/1.00  --res_sim_input                         true
% 1.07/1.00  --eq_ax_congr_red                       true
% 1.07/1.00  --pure_diseq_elim                       true
% 1.07/1.00  --brand_transform                       false
% 1.07/1.00  --non_eq_to_eq                          false
% 1.07/1.00  --prep_def_merge                        true
% 1.07/1.00  --prep_def_merge_prop_impl              false
% 1.07/1.01  --prep_def_merge_mbd                    true
% 1.07/1.01  --prep_def_merge_tr_red                 false
% 1.07/1.01  --prep_def_merge_tr_cl                  false
% 1.07/1.01  --smt_preprocessing                     true
% 1.07/1.01  --smt_ac_axioms                         fast
% 1.07/1.01  --preprocessed_out                      false
% 1.07/1.01  --preprocessed_stats                    false
% 1.07/1.01  
% 1.07/1.01  ------ Abstraction refinement Options
% 1.07/1.01  
% 1.07/1.01  --abstr_ref                             []
% 1.07/1.01  --abstr_ref_prep                        false
% 1.07/1.01  --abstr_ref_until_sat                   false
% 1.07/1.01  --abstr_ref_sig_restrict                funpre
% 1.07/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.07/1.01  --abstr_ref_under                       []
% 1.07/1.01  
% 1.07/1.01  ------ SAT Options
% 1.07/1.01  
% 1.07/1.01  --sat_mode                              false
% 1.07/1.01  --sat_fm_restart_options                ""
% 1.07/1.01  --sat_gr_def                            false
% 1.07/1.01  --sat_epr_types                         true
% 1.07/1.01  --sat_non_cyclic_types                  false
% 1.07/1.01  --sat_finite_models                     false
% 1.07/1.01  --sat_fm_lemmas                         false
% 1.07/1.01  --sat_fm_prep                           false
% 1.07/1.01  --sat_fm_uc_incr                        true
% 1.07/1.01  --sat_out_model                         small
% 1.07/1.01  --sat_out_clauses                       false
% 1.07/1.01  
% 1.07/1.01  ------ QBF Options
% 1.07/1.01  
% 1.07/1.01  --qbf_mode                              false
% 1.07/1.01  --qbf_elim_univ                         false
% 1.07/1.01  --qbf_dom_inst                          none
% 1.07/1.01  --qbf_dom_pre_inst                      false
% 1.07/1.01  --qbf_sk_in                             false
% 1.07/1.01  --qbf_pred_elim                         true
% 1.07/1.01  --qbf_split                             512
% 1.07/1.01  
% 1.07/1.01  ------ BMC1 Options
% 1.07/1.01  
% 1.07/1.01  --bmc1_incremental                      false
% 1.07/1.01  --bmc1_axioms                           reachable_all
% 1.07/1.01  --bmc1_min_bound                        0
% 1.07/1.01  --bmc1_max_bound                        -1
% 1.07/1.01  --bmc1_max_bound_default                -1
% 1.07/1.01  --bmc1_symbol_reachability              true
% 1.07/1.01  --bmc1_property_lemmas                  false
% 1.07/1.01  --bmc1_k_induction                      false
% 1.07/1.01  --bmc1_non_equiv_states                 false
% 1.07/1.01  --bmc1_deadlock                         false
% 1.07/1.01  --bmc1_ucm                              false
% 1.07/1.01  --bmc1_add_unsat_core                   none
% 1.07/1.01  --bmc1_unsat_core_children              false
% 1.07/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.07/1.01  --bmc1_out_stat                         full
% 1.07/1.01  --bmc1_ground_init                      false
% 1.07/1.01  --bmc1_pre_inst_next_state              false
% 1.07/1.01  --bmc1_pre_inst_state                   false
% 1.07/1.01  --bmc1_pre_inst_reach_state             false
% 1.07/1.01  --bmc1_out_unsat_core                   false
% 1.07/1.01  --bmc1_aig_witness_out                  false
% 1.07/1.01  --bmc1_verbose                          false
% 1.07/1.01  --bmc1_dump_clauses_tptp                false
% 1.07/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.07/1.01  --bmc1_dump_file                        -
% 1.07/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.07/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.07/1.01  --bmc1_ucm_extend_mode                  1
% 1.07/1.01  --bmc1_ucm_init_mode                    2
% 1.07/1.01  --bmc1_ucm_cone_mode                    none
% 1.07/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.07/1.01  --bmc1_ucm_relax_model                  4
% 1.07/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.07/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.07/1.01  --bmc1_ucm_layered_model                none
% 1.07/1.01  --bmc1_ucm_max_lemma_size               10
% 1.07/1.01  
% 1.07/1.01  ------ AIG Options
% 1.07/1.01  
% 1.07/1.01  --aig_mode                              false
% 1.07/1.01  
% 1.07/1.01  ------ Instantiation Options
% 1.07/1.01  
% 1.07/1.01  --instantiation_flag                    true
% 1.07/1.01  --inst_sos_flag                         false
% 1.07/1.01  --inst_sos_phase                        true
% 1.07/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.07/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.07/1.01  --inst_lit_sel_side                     num_symb
% 1.07/1.01  --inst_solver_per_active                1400
% 1.07/1.01  --inst_solver_calls_frac                1.
% 1.07/1.01  --inst_passive_queue_type               priority_queues
% 1.07/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.07/1.01  --inst_passive_queues_freq              [25;2]
% 1.07/1.01  --inst_dismatching                      true
% 1.07/1.01  --inst_eager_unprocessed_to_passive     true
% 1.07/1.01  --inst_prop_sim_given                   true
% 1.07/1.01  --inst_prop_sim_new                     false
% 1.07/1.01  --inst_subs_new                         false
% 1.07/1.01  --inst_eq_res_simp                      false
% 1.07/1.01  --inst_subs_given                       false
% 1.07/1.01  --inst_orphan_elimination               true
% 1.07/1.01  --inst_learning_loop_flag               true
% 1.07/1.01  --inst_learning_start                   3000
% 1.07/1.01  --inst_learning_factor                  2
% 1.07/1.01  --inst_start_prop_sim_after_learn       3
% 1.07/1.01  --inst_sel_renew                        solver
% 1.07/1.01  --inst_lit_activity_flag                true
% 1.07/1.01  --inst_restr_to_given                   false
% 1.07/1.01  --inst_activity_threshold               500
% 1.07/1.01  --inst_out_proof                        true
% 1.07/1.01  
% 1.07/1.01  ------ Resolution Options
% 1.07/1.01  
% 1.07/1.01  --resolution_flag                       true
% 1.07/1.01  --res_lit_sel                           adaptive
% 1.07/1.01  --res_lit_sel_side                      none
% 1.07/1.01  --res_ordering                          kbo
% 1.07/1.01  --res_to_prop_solver                    active
% 1.07/1.01  --res_prop_simpl_new                    false
% 1.07/1.01  --res_prop_simpl_given                  true
% 1.07/1.01  --res_passive_queue_type                priority_queues
% 1.07/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.07/1.01  --res_passive_queues_freq               [15;5]
% 1.07/1.01  --res_forward_subs                      full
% 1.07/1.01  --res_backward_subs                     full
% 1.07/1.01  --res_forward_subs_resolution           true
% 1.07/1.01  --res_backward_subs_resolution          true
% 1.07/1.01  --res_orphan_elimination                true
% 1.07/1.01  --res_time_limit                        2.
% 1.07/1.01  --res_out_proof                         true
% 1.07/1.01  
% 1.07/1.01  ------ Superposition Options
% 1.07/1.01  
% 1.07/1.01  --superposition_flag                    true
% 1.07/1.01  --sup_passive_queue_type                priority_queues
% 1.07/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.07/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.07/1.01  --demod_completeness_check              fast
% 1.07/1.01  --demod_use_ground                      true
% 1.07/1.01  --sup_to_prop_solver                    passive
% 1.07/1.01  --sup_prop_simpl_new                    true
% 1.07/1.01  --sup_prop_simpl_given                  true
% 1.07/1.01  --sup_fun_splitting                     false
% 1.07/1.01  --sup_smt_interval                      50000
% 1.07/1.01  
% 1.07/1.01  ------ Superposition Simplification Setup
% 1.07/1.01  
% 1.07/1.01  --sup_indices_passive                   []
% 1.07/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.07/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.01  --sup_full_bw                           [BwDemod]
% 1.07/1.01  --sup_immed_triv                        [TrivRules]
% 1.07/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.07/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.01  --sup_immed_bw_main                     []
% 1.07/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.07/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.07/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.07/1.01  
% 1.07/1.01  ------ Combination Options
% 1.07/1.01  
% 1.07/1.01  --comb_res_mult                         3
% 1.07/1.01  --comb_sup_mult                         2
% 1.07/1.01  --comb_inst_mult                        10
% 1.07/1.01  
% 1.07/1.01  ------ Debug Options
% 1.07/1.01  
% 1.07/1.01  --dbg_backtrace                         false
% 1.07/1.01  --dbg_dump_prop_clauses                 false
% 1.07/1.01  --dbg_dump_prop_clauses_file            -
% 1.07/1.01  --dbg_out_stat                          false
% 1.07/1.01  ------ Parsing...
% 1.07/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.07/1.01  
% 1.07/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 1.07/1.01  
% 1.07/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.07/1.01  
% 1.07/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 1.07/1.01  ------ Proving...
% 1.07/1.01  ------ Problem Properties 
% 1.07/1.01  
% 1.07/1.01  
% 1.07/1.01  clauses                                 8
% 1.07/1.01  conjectures                             0
% 1.07/1.01  EPR                                     0
% 1.07/1.01  Horn                                    7
% 1.07/1.01  unary                                   1
% 1.07/1.01  binary                                  3
% 1.07/1.01  lits                                    19
% 1.07/1.01  lits eq                                 19
% 1.07/1.01  fd_pure                                 0
% 1.07/1.01  fd_pseudo                               0
% 1.07/1.01  fd_cond                                 2
% 1.07/1.01  fd_pseudo_cond                          2
% 1.07/1.01  AC symbols                              0
% 1.07/1.01  
% 1.07/1.01  ------ Schedule dynamic 5 is on 
% 1.07/1.01  
% 1.07/1.01  ------ no conjectures: strip conj schedule 
% 1.07/1.01  
% 1.07/1.01  ------ pure equality problem: resolution off 
% 1.07/1.01  
% 1.07/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 1.07/1.01  
% 1.07/1.01  
% 1.07/1.01  ------ 
% 1.07/1.01  Current options:
% 1.07/1.01  ------ 
% 1.07/1.01  
% 1.07/1.01  ------ Input Options
% 1.07/1.01  
% 1.07/1.01  --out_options                           all
% 1.07/1.01  --tptp_safe_out                         true
% 1.07/1.01  --problem_path                          ""
% 1.07/1.01  --include_path                          ""
% 1.07/1.01  --clausifier                            res/vclausify_rel
% 1.07/1.01  --clausifier_options                    --mode clausify
% 1.07/1.01  --stdin                                 false
% 1.07/1.01  --stats_out                             all
% 1.07/1.01  
% 1.07/1.01  ------ General Options
% 1.07/1.01  
% 1.07/1.01  --fof                                   false
% 1.07/1.01  --time_out_real                         305.
% 1.07/1.01  --time_out_virtual                      -1.
% 1.07/1.01  --symbol_type_check                     false
% 1.07/1.01  --clausify_out                          false
% 1.07/1.01  --sig_cnt_out                           false
% 1.07/1.01  --trig_cnt_out                          false
% 1.07/1.01  --trig_cnt_out_tolerance                1.
% 1.07/1.01  --trig_cnt_out_sk_spl                   false
% 1.07/1.01  --abstr_cl_out                          false
% 1.07/1.01  
% 1.07/1.01  ------ Global Options
% 1.07/1.01  
% 1.07/1.01  --schedule                              default
% 1.07/1.01  --add_important_lit                     false
% 1.07/1.01  --prop_solver_per_cl                    1000
% 1.07/1.01  --min_unsat_core                        false
% 1.07/1.01  --soft_assumptions                      false
% 1.07/1.01  --soft_lemma_size                       3
% 1.07/1.01  --prop_impl_unit_size                   0
% 1.07/1.01  --prop_impl_unit                        []
% 1.07/1.01  --share_sel_clauses                     true
% 1.07/1.01  --reset_solvers                         false
% 1.07/1.01  --bc_imp_inh                            [conj_cone]
% 1.07/1.01  --conj_cone_tolerance                   3.
% 1.07/1.01  --extra_neg_conj                        none
% 1.07/1.01  --large_theory_mode                     true
% 1.07/1.01  --prolific_symb_bound                   200
% 1.07/1.01  --lt_threshold                          2000
% 1.07/1.01  --clause_weak_htbl                      true
% 1.07/1.01  --gc_record_bc_elim                     false
% 1.07/1.01  
% 1.07/1.01  ------ Preprocessing Options
% 1.07/1.01  
% 1.07/1.01  --preprocessing_flag                    true
% 1.07/1.01  --time_out_prep_mult                    0.1
% 1.07/1.01  --splitting_mode                        input
% 1.07/1.01  --splitting_grd                         true
% 1.07/1.01  --splitting_cvd                         false
% 1.07/1.01  --splitting_cvd_svl                     false
% 1.07/1.01  --splitting_nvd                         32
% 1.07/1.01  --sub_typing                            true
% 1.07/1.01  --prep_gs_sim                           true
% 1.07/1.01  --prep_unflatten                        true
% 1.07/1.01  --prep_res_sim                          true
% 1.07/1.01  --prep_upred                            true
% 1.07/1.01  --prep_sem_filter                       exhaustive
% 1.07/1.01  --prep_sem_filter_out                   false
% 1.07/1.01  --pred_elim                             true
% 1.07/1.01  --res_sim_input                         true
% 1.07/1.01  --eq_ax_congr_red                       true
% 1.07/1.01  --pure_diseq_elim                       true
% 1.07/1.01  --brand_transform                       false
% 1.07/1.01  --non_eq_to_eq                          false
% 1.07/1.01  --prep_def_merge                        true
% 1.07/1.01  --prep_def_merge_prop_impl              false
% 1.07/1.01  --prep_def_merge_mbd                    true
% 1.07/1.01  --prep_def_merge_tr_red                 false
% 1.07/1.01  --prep_def_merge_tr_cl                  false
% 1.07/1.01  --smt_preprocessing                     true
% 1.07/1.01  --smt_ac_axioms                         fast
% 1.07/1.01  --preprocessed_out                      false
% 1.07/1.01  --preprocessed_stats                    false
% 1.07/1.01  
% 1.07/1.01  ------ Abstraction refinement Options
% 1.07/1.01  
% 1.07/1.01  --abstr_ref                             []
% 1.07/1.01  --abstr_ref_prep                        false
% 1.07/1.01  --abstr_ref_until_sat                   false
% 1.07/1.01  --abstr_ref_sig_restrict                funpre
% 1.07/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.07/1.01  --abstr_ref_under                       []
% 1.07/1.01  
% 1.07/1.01  ------ SAT Options
% 1.07/1.01  
% 1.07/1.01  --sat_mode                              false
% 1.07/1.01  --sat_fm_restart_options                ""
% 1.07/1.01  --sat_gr_def                            false
% 1.07/1.01  --sat_epr_types                         true
% 1.07/1.01  --sat_non_cyclic_types                  false
% 1.07/1.01  --sat_finite_models                     false
% 1.07/1.01  --sat_fm_lemmas                         false
% 1.07/1.01  --sat_fm_prep                           false
% 1.07/1.01  --sat_fm_uc_incr                        true
% 1.07/1.01  --sat_out_model                         small
% 1.07/1.01  --sat_out_clauses                       false
% 1.07/1.01  
% 1.07/1.01  ------ QBF Options
% 1.07/1.01  
% 1.07/1.01  --qbf_mode                              false
% 1.07/1.01  --qbf_elim_univ                         false
% 1.07/1.01  --qbf_dom_inst                          none
% 1.07/1.01  --qbf_dom_pre_inst                      false
% 1.07/1.01  --qbf_sk_in                             false
% 1.07/1.01  --qbf_pred_elim                         true
% 1.07/1.01  --qbf_split                             512
% 1.07/1.01  
% 1.07/1.01  ------ BMC1 Options
% 1.07/1.01  
% 1.07/1.01  --bmc1_incremental                      false
% 1.07/1.01  --bmc1_axioms                           reachable_all
% 1.07/1.01  --bmc1_min_bound                        0
% 1.07/1.01  --bmc1_max_bound                        -1
% 1.07/1.01  --bmc1_max_bound_default                -1
% 1.07/1.01  --bmc1_symbol_reachability              true
% 1.07/1.01  --bmc1_property_lemmas                  false
% 1.07/1.01  --bmc1_k_induction                      false
% 1.07/1.01  --bmc1_non_equiv_states                 false
% 1.07/1.01  --bmc1_deadlock                         false
% 1.07/1.01  --bmc1_ucm                              false
% 1.07/1.01  --bmc1_add_unsat_core                   none
% 1.07/1.01  --bmc1_unsat_core_children              false
% 1.07/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.07/1.01  --bmc1_out_stat                         full
% 1.07/1.01  --bmc1_ground_init                      false
% 1.07/1.01  --bmc1_pre_inst_next_state              false
% 1.07/1.01  --bmc1_pre_inst_state                   false
% 1.07/1.01  --bmc1_pre_inst_reach_state             false
% 1.07/1.01  --bmc1_out_unsat_core                   false
% 1.07/1.01  --bmc1_aig_witness_out                  false
% 1.07/1.01  --bmc1_verbose                          false
% 1.07/1.01  --bmc1_dump_clauses_tptp                false
% 1.07/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.07/1.01  --bmc1_dump_file                        -
% 1.07/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.07/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.07/1.01  --bmc1_ucm_extend_mode                  1
% 1.07/1.01  --bmc1_ucm_init_mode                    2
% 1.07/1.01  --bmc1_ucm_cone_mode                    none
% 1.07/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.07/1.01  --bmc1_ucm_relax_model                  4
% 1.07/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.07/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.07/1.01  --bmc1_ucm_layered_model                none
% 1.07/1.01  --bmc1_ucm_max_lemma_size               10
% 1.07/1.01  
% 1.07/1.01  ------ AIG Options
% 1.07/1.01  
% 1.07/1.01  --aig_mode                              false
% 1.07/1.01  
% 1.07/1.01  ------ Instantiation Options
% 1.07/1.01  
% 1.07/1.01  --instantiation_flag                    true
% 1.07/1.01  --inst_sos_flag                         false
% 1.07/1.01  --inst_sos_phase                        true
% 1.07/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.07/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.07/1.01  --inst_lit_sel_side                     none
% 1.07/1.01  --inst_solver_per_active                1400
% 1.07/1.01  --inst_solver_calls_frac                1.
% 1.07/1.01  --inst_passive_queue_type               priority_queues
% 1.07/1.01  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 1.07/1.01  --inst_passive_queues_freq              [25;2]
% 1.07/1.01  --inst_dismatching                      true
% 1.07/1.01  --inst_eager_unprocessed_to_passive     true
% 1.07/1.01  --inst_prop_sim_given                   true
% 1.07/1.01  --inst_prop_sim_new                     false
% 1.07/1.01  --inst_subs_new                         false
% 1.07/1.01  --inst_eq_res_simp                      false
% 1.07/1.01  --inst_subs_given                       false
% 1.07/1.01  --inst_orphan_elimination               true
% 1.07/1.01  --inst_learning_loop_flag               true
% 1.07/1.01  --inst_learning_start                   3000
% 1.07/1.01  --inst_learning_factor                  2
% 1.07/1.01  --inst_start_prop_sim_after_learn       3
% 1.07/1.01  --inst_sel_renew                        solver
% 1.07/1.01  --inst_lit_activity_flag                true
% 1.07/1.01  --inst_restr_to_given                   false
% 1.07/1.01  --inst_activity_threshold               500
% 1.07/1.01  --inst_out_proof                        true
% 1.07/1.01  
% 1.07/1.01  ------ Resolution Options
% 1.07/1.01  
% 1.07/1.01  --resolution_flag                       false
% 1.07/1.01  --res_lit_sel                           adaptive
% 1.07/1.01  --res_lit_sel_side                      none
% 1.07/1.01  --res_ordering                          kbo
% 1.07/1.01  --res_to_prop_solver                    active
% 1.07/1.01  --res_prop_simpl_new                    false
% 1.07/1.01  --res_prop_simpl_given                  true
% 1.07/1.01  --res_passive_queue_type                priority_queues
% 1.07/1.01  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 1.07/1.01  --res_passive_queues_freq               [15;5]
% 1.07/1.01  --res_forward_subs                      full
% 1.07/1.01  --res_backward_subs                     full
% 1.07/1.01  --res_forward_subs_resolution           true
% 1.07/1.01  --res_backward_subs_resolution          true
% 1.07/1.01  --res_orphan_elimination                true
% 1.07/1.01  --res_time_limit                        2.
% 1.07/1.01  --res_out_proof                         true
% 1.07/1.01  
% 1.07/1.01  ------ Superposition Options
% 1.07/1.01  
% 1.07/1.01  --superposition_flag                    true
% 1.07/1.01  --sup_passive_queue_type                priority_queues
% 1.07/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.07/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.07/1.01  --demod_completeness_check              fast
% 1.07/1.01  --demod_use_ground                      true
% 1.07/1.01  --sup_to_prop_solver                    passive
% 1.07/1.01  --sup_prop_simpl_new                    true
% 1.07/1.01  --sup_prop_simpl_given                  true
% 1.07/1.01  --sup_fun_splitting                     false
% 1.07/1.01  --sup_smt_interval                      50000
% 1.07/1.01  
% 1.07/1.01  ------ Superposition Simplification Setup
% 1.07/1.01  
% 1.07/1.01  --sup_indices_passive                   []
% 1.07/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.07/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.01  --sup_full_bw                           [BwDemod]
% 1.07/1.01  --sup_immed_triv                        [TrivRules]
% 1.07/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.07/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.01  --sup_immed_bw_main                     []
% 1.07/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.07/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.07/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.07/1.01  
% 1.07/1.01  ------ Combination Options
% 1.07/1.01  
% 1.07/1.01  --comb_res_mult                         3
% 1.07/1.01  --comb_sup_mult                         2
% 1.07/1.01  --comb_inst_mult                        10
% 1.07/1.01  
% 1.07/1.01  ------ Debug Options
% 1.07/1.01  
% 1.07/1.01  --dbg_backtrace                         false
% 1.07/1.01  --dbg_dump_prop_clauses                 false
% 1.07/1.01  --dbg_dump_prop_clauses_file            -
% 1.07/1.01  --dbg_out_stat                          false
% 1.07/1.01  
% 1.07/1.01  
% 1.07/1.01  
% 1.07/1.01  
% 1.07/1.01  ------ Proving...
% 1.07/1.01  
% 1.07/1.01  
% 1.07/1.01  % SZS status Theorem for theBenchmark.p
% 1.07/1.01  
% 1.07/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.07/1.01  
% 1.07/1.01  fof(f5,axiom,(
% 1.07/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 1.07/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.01  
% 1.07/1.01  fof(f13,plain,(
% 1.07/1.01    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.07/1.01    inference(ennf_transformation,[],[f5])).
% 1.07/1.01  
% 1.07/1.01  fof(f14,plain,(
% 1.07/1.01    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.07/1.01    inference(flattening,[],[f13])).
% 1.07/1.01  
% 1.07/1.01  fof(f18,plain,(
% 1.07/1.01    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.07/1.01    inference(nnf_transformation,[],[f14])).
% 1.07/1.01  
% 1.07/1.01  fof(f30,plain,(
% 1.07/1.01    ( ! [X0,X1] : (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.07/1.01    inference(cnf_transformation,[],[f18])).
% 1.07/1.01  
% 1.07/1.01  fof(f6,conjecture,(
% 1.07/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 1.07/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.01  
% 1.07/1.01  fof(f7,negated_conjecture,(
% 1.07/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 1.07/1.01    inference(negated_conjecture,[],[f6])).
% 1.07/1.01  
% 1.07/1.01  fof(f15,plain,(
% 1.07/1.01    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.07/1.01    inference(ennf_transformation,[],[f7])).
% 1.07/1.01  
% 1.07/1.01  fof(f16,plain,(
% 1.07/1.01    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.07/1.01    inference(flattening,[],[f15])).
% 1.07/1.01  
% 1.07/1.01  fof(f19,plain,(
% 1.07/1.01    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.07/1.01    inference(nnf_transformation,[],[f16])).
% 1.07/1.01  
% 1.07/1.01  fof(f20,plain,(
% 1.07/1.01    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.07/1.01    inference(flattening,[],[f19])).
% 1.07/1.01  
% 1.07/1.01  fof(f22,plain,(
% 1.07/1.01    ( ! [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,sK1) | ~v3_pre_topc(sK1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,sK1) | v3_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.07/1.01    introduced(choice_axiom,[])).
% 1.07/1.01  
% 1.07/1.01  fof(f21,plain,(
% 1.07/1.01    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1) | ~v3_pre_topc(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.07/1.01    introduced(choice_axiom,[])).
% 1.07/1.01  
% 1.07/1.01  fof(f23,plain,(
% 1.07/1.01    ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.07/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).
% 1.07/1.01  
% 1.07/1.01  fof(f33,plain,(
% 1.07/1.01    v2_pre_topc(sK0)),
% 1.07/1.01    inference(cnf_transformation,[],[f23])).
% 1.07/1.01  
% 1.07/1.01  fof(f32,plain,(
% 1.07/1.01    ~v2_struct_0(sK0)),
% 1.07/1.01    inference(cnf_transformation,[],[f23])).
% 1.07/1.01  
% 1.07/1.01  fof(f34,plain,(
% 1.07/1.01    l1_pre_topc(sK0)),
% 1.07/1.01    inference(cnf_transformation,[],[f23])).
% 1.07/1.01  
% 1.07/1.01  fof(f36,plain,(
% 1.07/1.01    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)),
% 1.07/1.01    inference(cnf_transformation,[],[f23])).
% 1.07/1.01  
% 1.07/1.01  fof(f1,axiom,(
% 1.07/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 1.07/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.01  
% 1.07/1.01  fof(f8,plain,(
% 1.07/1.01    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.07/1.01    inference(ennf_transformation,[],[f1])).
% 1.07/1.01  
% 1.07/1.01  fof(f17,plain,(
% 1.07/1.01    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.07/1.01    inference(nnf_transformation,[],[f8])).
% 1.07/1.01  
% 1.07/1.01  fof(f24,plain,(
% 1.07/1.01    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.07/1.01    inference(cnf_transformation,[],[f17])).
% 1.07/1.01  
% 1.07/1.01  fof(f35,plain,(
% 1.07/1.01    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.07/1.01    inference(cnf_transformation,[],[f23])).
% 1.07/1.01  
% 1.07/1.01  fof(f31,plain,(
% 1.07/1.01    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.07/1.01    inference(cnf_transformation,[],[f18])).
% 1.07/1.01  
% 1.07/1.01  fof(f37,plain,(
% 1.07/1.01    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 1.07/1.01    inference(cnf_transformation,[],[f23])).
% 1.07/1.01  
% 1.07/1.01  fof(f25,plain,(
% 1.07/1.01    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.07/1.01    inference(cnf_transformation,[],[f17])).
% 1.07/1.01  
% 1.07/1.01  fof(f4,axiom,(
% 1.07/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1)))),
% 1.07/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.01  
% 1.07/1.01  fof(f11,plain,(
% 1.07/1.01    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.07/1.01    inference(ennf_transformation,[],[f4])).
% 1.07/1.01  
% 1.07/1.01  fof(f12,plain,(
% 1.07/1.01    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.07/1.01    inference(flattening,[],[f11])).
% 1.07/1.01  
% 1.07/1.01  fof(f29,plain,(
% 1.07/1.01    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) = k6_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.07/1.01    inference(cnf_transformation,[],[f12])).
% 1.07/1.01  
% 1.07/1.01  fof(f3,axiom,(
% 1.07/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 1.07/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.01  
% 1.07/1.01  fof(f10,plain,(
% 1.07/1.01    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.07/1.01    inference(ennf_transformation,[],[f3])).
% 1.07/1.01  
% 1.07/1.01  fof(f28,plain,(
% 1.07/1.01    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.07/1.01    inference(cnf_transformation,[],[f10])).
% 1.07/1.01  
% 1.07/1.01  fof(f2,axiom,(
% 1.07/1.01    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.07/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.01  
% 1.07/1.01  fof(f9,plain,(
% 1.07/1.01    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.07/1.01    inference(ennf_transformation,[],[f2])).
% 1.07/1.01  
% 1.07/1.01  fof(f26,plain,(
% 1.07/1.01    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.07/1.01    inference(cnf_transformation,[],[f9])).
% 1.07/1.01  
% 1.07/1.01  cnf(c_7,plain,
% 1.07/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.07/1.01      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 1.07/1.01      | v2_struct_0(X1)
% 1.07/1.01      | ~ v2_pre_topc(X1)
% 1.07/1.01      | ~ l1_pre_topc(X1)
% 1.07/1.01      | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
% 1.07/1.01      inference(cnf_transformation,[],[f30]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_12,negated_conjecture,
% 1.07/1.01      ( v2_pre_topc(sK0) ),
% 1.07/1.01      inference(cnf_transformation,[],[f33]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_189,plain,
% 1.07/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.07/1.01      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 1.07/1.01      | v2_struct_0(X1)
% 1.07/1.01      | ~ l1_pre_topc(X1)
% 1.07/1.01      | k5_tmap_1(X1,X0) = u1_pre_topc(X1)
% 1.07/1.01      | sK0 != X1 ),
% 1.07/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_12]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_190,plain,
% 1.07/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.07/1.01      | ~ r2_hidden(X0,u1_pre_topc(sK0))
% 1.07/1.01      | v2_struct_0(sK0)
% 1.07/1.01      | ~ l1_pre_topc(sK0)
% 1.07/1.01      | k5_tmap_1(sK0,X0) = u1_pre_topc(sK0) ),
% 1.07/1.01      inference(unflattening,[status(thm)],[c_189]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_13,negated_conjecture,
% 1.07/1.01      ( ~ v2_struct_0(sK0) ),
% 1.07/1.01      inference(cnf_transformation,[],[f32]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_11,negated_conjecture,
% 1.07/1.01      ( l1_pre_topc(sK0) ),
% 1.07/1.01      inference(cnf_transformation,[],[f34]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_194,plain,
% 1.07/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.07/1.01      | ~ r2_hidden(X0,u1_pre_topc(sK0))
% 1.07/1.01      | k5_tmap_1(sK0,X0) = u1_pre_topc(sK0) ),
% 1.07/1.01      inference(global_propositional_subsumption,
% 1.07/1.01                [status(thm)],
% 1.07/1.01                [c_190,c_13,c_11]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_9,negated_conjecture,
% 1.07/1.01      ( v3_pre_topc(sK1,sK0)
% 1.07/1.01      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 1.07/1.01      inference(cnf_transformation,[],[f36]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_103,plain,
% 1.07/1.01      ( v3_pre_topc(sK1,sK0)
% 1.07/1.01      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 1.07/1.01      inference(prop_impl,[status(thm)],[c_9]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_1,plain,
% 1.07/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.07/1.01      | r2_hidden(X0,u1_pre_topc(X1))
% 1.07/1.01      | ~ v3_pre_topc(X0,X1)
% 1.07/1.01      | ~ l1_pre_topc(X1) ),
% 1.07/1.01      inference(cnf_transformation,[],[f24]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_260,plain,
% 1.07/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.07/1.01      | r2_hidden(X0,u1_pre_topc(X1))
% 1.07/1.01      | ~ v3_pre_topc(X0,X1)
% 1.07/1.01      | sK0 != X1 ),
% 1.07/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_11]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_261,plain,
% 1.07/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.07/1.01      | r2_hidden(X0,u1_pre_topc(sK0))
% 1.07/1.01      | ~ v3_pre_topc(X0,sK0) ),
% 1.07/1.01      inference(unflattening,[status(thm)],[c_260]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_309,plain,
% 1.07/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.07/1.01      | r2_hidden(X0,u1_pre_topc(sK0))
% 1.07/1.01      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
% 1.07/1.01      | sK1 != X0
% 1.07/1.01      | sK0 != sK0 ),
% 1.07/1.01      inference(resolution_lifted,[status(thm)],[c_103,c_261]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_310,plain,
% 1.07/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.07/1.01      | r2_hidden(sK1,u1_pre_topc(sK0))
% 1.07/1.01      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 1.07/1.01      inference(unflattening,[status(thm)],[c_309]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_10,negated_conjecture,
% 1.07/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.07/1.01      inference(cnf_transformation,[],[f35]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_312,plain,
% 1.07/1.01      ( r2_hidden(sK1,u1_pre_topc(sK0))
% 1.07/1.01      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 1.07/1.01      inference(global_propositional_subsumption,
% 1.07/1.01                [status(thm)],
% 1.07/1.01                [c_310,c_10]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_356,plain,
% 1.07/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.07/1.01      | k5_tmap_1(sK0,X0) = u1_pre_topc(sK0)
% 1.07/1.01      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
% 1.07/1.01      | u1_pre_topc(sK0) != u1_pre_topc(sK0)
% 1.07/1.01      | sK1 != X0 ),
% 1.07/1.01      inference(resolution_lifted,[status(thm)],[c_194,c_312]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_357,plain,
% 1.07/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.07/1.01      | k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 1.07/1.01      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 1.07/1.01      inference(unflattening,[status(thm)],[c_356]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_359,plain,
% 1.07/1.01      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 1.07/1.01      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 1.07/1.01      inference(global_propositional_subsumption,
% 1.07/1.01                [status(thm)],
% 1.07/1.01                [c_357,c_10]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_449,plain,
% 1.07/1.01      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 1.07/1.01      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 1.07/1.01      inference(prop_impl,[status(thm)],[c_10,c_357]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_6,plain,
% 1.07/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.07/1.01      | r2_hidden(X0,u1_pre_topc(X1))
% 1.07/1.01      | v2_struct_0(X1)
% 1.07/1.01      | ~ v2_pre_topc(X1)
% 1.07/1.01      | ~ l1_pre_topc(X1)
% 1.07/1.01      | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
% 1.07/1.01      inference(cnf_transformation,[],[f31]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_210,plain,
% 1.07/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.07/1.01      | r2_hidden(X0,u1_pre_topc(X1))
% 1.07/1.01      | v2_struct_0(X1)
% 1.07/1.01      | ~ l1_pre_topc(X1)
% 1.07/1.01      | k5_tmap_1(X1,X0) != u1_pre_topc(X1)
% 1.07/1.01      | sK0 != X1 ),
% 1.07/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_12]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_211,plain,
% 1.07/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.07/1.01      | r2_hidden(X0,u1_pre_topc(sK0))
% 1.07/1.01      | v2_struct_0(sK0)
% 1.07/1.01      | ~ l1_pre_topc(sK0)
% 1.07/1.01      | k5_tmap_1(sK0,X0) != u1_pre_topc(sK0) ),
% 1.07/1.01      inference(unflattening,[status(thm)],[c_210]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_215,plain,
% 1.07/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.07/1.01      | r2_hidden(X0,u1_pre_topc(sK0))
% 1.07/1.01      | k5_tmap_1(sK0,X0) != u1_pre_topc(sK0) ),
% 1.07/1.01      inference(global_propositional_subsumption,
% 1.07/1.01                [status(thm)],
% 1.07/1.01                [c_211,c_13,c_11]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_8,negated_conjecture,
% 1.07/1.01      ( ~ v3_pre_topc(sK1,sK0)
% 1.07/1.01      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 1.07/1.01      inference(cnf_transformation,[],[f37]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_101,plain,
% 1.07/1.01      ( ~ v3_pre_topc(sK1,sK0)
% 1.07/1.01      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 1.07/1.01      inference(prop_impl,[status(thm)],[c_8]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_0,plain,
% 1.07/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.07/1.01      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 1.07/1.01      | v3_pre_topc(X0,X1)
% 1.07/1.01      | ~ l1_pre_topc(X1) ),
% 1.07/1.01      inference(cnf_transformation,[],[f25]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_275,plain,
% 1.07/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.07/1.01      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 1.07/1.01      | v3_pre_topc(X0,X1)
% 1.07/1.01      | sK0 != X1 ),
% 1.07/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_11]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_276,plain,
% 1.07/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.07/1.01      | ~ r2_hidden(X0,u1_pre_topc(sK0))
% 1.07/1.01      | v3_pre_topc(X0,sK0) ),
% 1.07/1.01      inference(unflattening,[status(thm)],[c_275]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_323,plain,
% 1.07/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.07/1.01      | ~ r2_hidden(X0,u1_pre_topc(sK0))
% 1.07/1.01      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 1.07/1.01      | sK1 != X0
% 1.07/1.01      | sK0 != sK0 ),
% 1.07/1.01      inference(resolution_lifted,[status(thm)],[c_101,c_276]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_324,plain,
% 1.07/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.07/1.01      | ~ r2_hidden(sK1,u1_pre_topc(sK0))
% 1.07/1.01      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 1.07/1.01      inference(unflattening,[status(thm)],[c_323]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_326,plain,
% 1.07/1.01      ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
% 1.07/1.01      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 1.07/1.01      inference(global_propositional_subsumption,
% 1.07/1.01                [status(thm)],
% 1.07/1.01                [c_324,c_10]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_345,plain,
% 1.07/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.07/1.01      | k5_tmap_1(sK0,X0) != u1_pre_topc(sK0)
% 1.07/1.01      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 1.07/1.01      | u1_pre_topc(sK0) != u1_pre_topc(sK0)
% 1.07/1.01      | sK1 != X0 ),
% 1.07/1.01      inference(resolution_lifted,[status(thm)],[c_215,c_326]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_346,plain,
% 1.07/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.07/1.01      | k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
% 1.07/1.01      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 1.07/1.01      inference(unflattening,[status(thm)],[c_345]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_348,plain,
% 1.07/1.01      ( k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
% 1.07/1.01      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 1.07/1.01      inference(global_propositional_subsumption,
% 1.07/1.01                [status(thm)],
% 1.07/1.01                [c_346,c_10]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_447,plain,
% 1.07/1.01      ( k5_tmap_1(sK0,sK1) != u1_pre_topc(sK0)
% 1.07/1.01      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 1.07/1.01      inference(prop_impl,[status(thm)],[c_10,c_346]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_5,plain,
% 1.07/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.07/1.01      | v2_struct_0(X1)
% 1.07/1.01      | ~ v2_pre_topc(X1)
% 1.07/1.01      | ~ l1_pre_topc(X1)
% 1.07/1.01      | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0) ),
% 1.07/1.01      inference(cnf_transformation,[],[f29]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_231,plain,
% 1.07/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.07/1.01      | v2_struct_0(X1)
% 1.07/1.01      | ~ l1_pre_topc(X1)
% 1.07/1.01      | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0)
% 1.07/1.01      | sK0 != X1 ),
% 1.07/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_12]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_232,plain,
% 1.07/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.07/1.01      | v2_struct_0(sK0)
% 1.07/1.01      | ~ l1_pre_topc(sK0)
% 1.07/1.01      | g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) = k6_tmap_1(sK0,X0) ),
% 1.07/1.01      inference(unflattening,[status(thm)],[c_231]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_236,plain,
% 1.07/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.07/1.01      | g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) = k6_tmap_1(sK0,X0) ),
% 1.07/1.01      inference(global_propositional_subsumption,
% 1.07/1.01                [status(thm)],
% 1.07/1.01                [c_232,c_13,c_11]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_419,plain,
% 1.07/1.01      ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) = k6_tmap_1(sK0,X0)
% 1.07/1.01      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
% 1.07/1.01      | sK1 != X0 ),
% 1.07/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_236]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_420,plain,
% 1.07/1.01      ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) = k6_tmap_1(sK0,sK1) ),
% 1.07/1.01      inference(unflattening,[status(thm)],[c_419]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_3,plain,
% 1.07/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 1.07/1.01      | X2 = X0
% 1.07/1.01      | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
% 1.07/1.01      inference(cnf_transformation,[],[f28]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_2,plain,
% 1.07/1.01      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 1.07/1.01      | ~ l1_pre_topc(X0) ),
% 1.07/1.01      inference(cnf_transformation,[],[f26]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_290,plain,
% 1.07/1.01      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 1.07/1.01      | sK0 != X0 ),
% 1.07/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_11]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_291,plain,
% 1.07/1.01      ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 1.07/1.01      inference(unflattening,[status(thm)],[c_290]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_407,plain,
% 1.07/1.01      ( X0 = X1
% 1.07/1.01      | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
% 1.07/1.01      | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) != k1_zfmisc_1(k1_zfmisc_1(X3))
% 1.07/1.01      | u1_pre_topc(sK0) != X1 ),
% 1.07/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_291]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_408,plain,
% 1.07/1.01      ( X0 = u1_pre_topc(sK0)
% 1.07/1.01      | g1_pre_topc(X1,X0) != g1_pre_topc(X2,u1_pre_topc(sK0))
% 1.07/1.01      | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) != k1_zfmisc_1(k1_zfmisc_1(X2)) ),
% 1.07/1.01      inference(unflattening,[status(thm)],[c_407]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_745,plain,
% 1.07/1.01      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 1.07/1.01      | g1_pre_topc(X0,u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
% 1.07/1.01      | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))) != k1_zfmisc_1(k1_zfmisc_1(X0)) ),
% 1.07/1.01      inference(superposition,[status(thm)],[c_420,c_408]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_757,plain,
% 1.07/1.01      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0)
% 1.07/1.01      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 1.07/1.01      inference(equality_resolution,[status(thm)],[c_745]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_792,plain,
% 1.07/1.01      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
% 1.07/1.01      inference(global_propositional_subsumption,
% 1.07/1.01                [status(thm)],
% 1.07/1.01                [c_447,c_10,c_346,c_757]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_795,plain,
% 1.07/1.01      ( k5_tmap_1(sK0,sK1) = u1_pre_topc(sK0) ),
% 1.07/1.01      inference(global_propositional_subsumption,
% 1.07/1.01                [status(thm)],
% 1.07/1.01                [c_449,c_10,c_346,c_357,c_757]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(c_799,plain,
% 1.07/1.01      ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
% 1.07/1.01      inference(demodulation,[status(thm)],[c_795,c_420]) ).
% 1.07/1.01  
% 1.07/1.01  cnf(contradiction,plain,
% 1.07/1.01      ( $false ),
% 1.07/1.01      inference(minisat,[status(thm)],[c_799,c_792]) ).
% 1.07/1.01  
% 1.07/1.01  
% 1.07/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.07/1.01  
% 1.07/1.01  ------                               Statistics
% 1.07/1.01  
% 1.07/1.01  ------ General
% 1.07/1.01  
% 1.07/1.01  abstr_ref_over_cycles:                  0
% 1.07/1.01  abstr_ref_under_cycles:                 0
% 1.07/1.01  gc_basic_clause_elim:                   0
% 1.07/1.01  forced_gc_time:                         0
% 1.07/1.01  parsing_time:                           0.011
% 1.07/1.01  unif_index_cands_time:                  0.
% 1.07/1.01  unif_index_add_time:                    0.
% 1.07/1.01  orderings_time:                         0.
% 1.07/1.01  out_proof_time:                         0.012
% 1.07/1.01  total_time:                             0.065
% 1.07/1.01  num_of_symbols:                         45
% 1.07/1.01  num_of_terms:                           873
% 1.07/1.01  
% 1.07/1.01  ------ Preprocessing
% 1.07/1.01  
% 1.07/1.01  num_of_splits:                          0
% 1.07/1.01  num_of_split_atoms:                     0
% 1.07/1.01  num_of_reused_defs:                     0
% 1.07/1.01  num_eq_ax_congr_red:                    3
% 1.07/1.01  num_of_sem_filtered_clauses:            0
% 1.07/1.01  num_of_subtypes:                        0
% 1.07/1.01  monotx_restored_types:                  0
% 1.07/1.01  sat_num_of_epr_types:                   0
% 1.07/1.01  sat_num_of_non_cyclic_types:            0
% 1.07/1.01  sat_guarded_non_collapsed_types:        0
% 1.07/1.01  num_pure_diseq_elim:                    0
% 1.07/1.01  simp_replaced_by:                       0
% 1.07/1.01  res_preprocessed:                       38
% 1.07/1.01  prep_upred:                             0
% 1.07/1.01  prep_unflattend:                        16
% 1.07/1.01  smt_new_axioms:                         0
% 1.07/1.01  pred_elim_cands:                        0
% 1.07/1.01  pred_elim:                              6
% 1.07/1.01  pred_elim_cl:                           6
% 1.07/1.01  pred_elim_cycles:                       7
% 1.07/1.01  merged_defs:                            6
% 1.07/1.01  merged_defs_ncl:                        0
% 1.07/1.01  bin_hyper_res:                          6
% 1.07/1.01  prep_cycles:                            3
% 1.07/1.01  pred_elim_time:                         0.004
% 1.07/1.01  splitting_time:                         0.
% 1.07/1.01  sem_filter_time:                        0.
% 1.07/1.01  monotx_time:                            0.
% 1.07/1.01  subtype_inf_time:                       0.
% 1.07/1.01  
% 1.07/1.01  ------ Problem properties
% 1.07/1.01  
% 1.07/1.01  clauses:                                8
% 1.07/1.01  conjectures:                            0
% 1.07/1.01  epr:                                    0
% 1.07/1.01  horn:                                   7
% 1.07/1.01  ground:                                 4
% 1.07/1.01  unary:                                  1
% 1.07/1.01  binary:                                 3
% 1.07/1.01  lits:                                   19
% 1.07/1.01  lits_eq:                                19
% 1.07/1.01  fd_pure:                                0
% 1.07/1.01  fd_pseudo:                              0
% 1.07/1.01  fd_cond:                                2
% 1.07/1.01  fd_pseudo_cond:                         2
% 1.07/1.01  ac_symbols:                             0
% 1.07/1.01  
% 1.07/1.01  ------ Propositional Solver
% 1.07/1.01  
% 1.07/1.01  prop_solver_calls:                      21
% 1.07/1.01  prop_fast_solver_calls:                 287
% 1.07/1.01  smt_solver_calls:                       0
% 1.07/1.01  smt_fast_solver_calls:                  0
% 1.07/1.01  prop_num_of_clauses:                    225
% 1.07/1.01  prop_preprocess_simplified:             946
% 1.07/1.01  prop_fo_subsumed:                       12
% 1.07/1.01  prop_solver_time:                       0.
% 1.07/1.01  smt_solver_time:                        0.
% 1.07/1.01  smt_fast_solver_time:                   0.
% 1.07/1.01  prop_fast_solver_time:                  0.
% 1.07/1.01  prop_unsat_core_time:                   0.
% 1.07/1.01  
% 1.07/1.01  ------ QBF
% 1.07/1.01  
% 1.07/1.01  qbf_q_res:                              0
% 1.07/1.01  qbf_num_tautologies:                    0
% 1.07/1.01  qbf_prep_cycles:                        0
% 1.07/1.01  
% 1.07/1.01  ------ BMC1
% 1.07/1.01  
% 1.07/1.01  bmc1_current_bound:                     -1
% 1.07/1.01  bmc1_last_solved_bound:                 -1
% 1.07/1.01  bmc1_unsat_core_size:                   -1
% 1.07/1.01  bmc1_unsat_core_parents_size:           -1
% 1.07/1.01  bmc1_merge_next_fun:                    0
% 1.07/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.07/1.01  
% 1.07/1.01  ------ Instantiation
% 1.07/1.01  
% 1.07/1.01  inst_num_of_clauses:                    77
% 1.07/1.01  inst_num_in_passive:                    27
% 1.07/1.01  inst_num_in_active:                     48
% 1.07/1.01  inst_num_in_unprocessed:                2
% 1.07/1.01  inst_num_of_loops:                      50
% 1.07/1.01  inst_num_of_learning_restarts:          0
% 1.07/1.01  inst_num_moves_active_passive:          0
% 1.07/1.01  inst_lit_activity:                      0
% 1.07/1.01  inst_lit_activity_moves:                0
% 1.07/1.01  inst_num_tautologies:                   0
% 1.07/1.01  inst_num_prop_implied:                  0
% 1.07/1.01  inst_num_existing_simplified:           0
% 1.07/1.01  inst_num_eq_res_simplified:             0
% 1.07/1.01  inst_num_child_elim:                    0
% 1.07/1.01  inst_num_of_dismatching_blockings:      43
% 1.07/1.01  inst_num_of_non_proper_insts:           83
% 1.07/1.01  inst_num_of_duplicates:                 0
% 1.07/1.01  inst_inst_num_from_inst_to_res:         0
% 1.07/1.01  inst_dismatching_checking_time:         0.
% 1.07/1.01  
% 1.07/1.01  ------ Resolution
% 1.07/1.01  
% 1.07/1.01  res_num_of_clauses:                     0
% 1.07/1.01  res_num_in_passive:                     0
% 1.07/1.01  res_num_in_active:                      0
% 1.07/1.01  res_num_of_loops:                       41
% 1.07/1.01  res_forward_subset_subsumed:            2
% 1.07/1.01  res_backward_subset_subsumed:           0
% 1.07/1.01  res_forward_subsumed:                   0
% 1.07/1.01  res_backward_subsumed:                  0
% 1.07/1.01  res_forward_subsumption_resolution:     0
% 1.07/1.01  res_backward_subsumption_resolution:    0
% 1.07/1.01  res_clause_to_clause_subsumption:       18
% 1.07/1.01  res_orphan_elimination:                 0
% 1.07/1.01  res_tautology_del:                      25
% 1.07/1.01  res_num_eq_res_simplified:              0
% 1.07/1.01  res_num_sel_changes:                    0
% 1.07/1.01  res_moves_from_active_to_pass:          0
% 1.07/1.01  
% 1.07/1.01  ------ Superposition
% 1.07/1.01  
% 1.07/1.01  sup_time_total:                         0.
% 1.07/1.01  sup_time_generating:                    0.
% 1.07/1.01  sup_time_sim_full:                      0.
% 1.07/1.01  sup_time_sim_immed:                     0.
% 1.07/1.01  
% 1.07/1.01  sup_num_of_clauses:                     9
% 1.07/1.01  sup_num_in_active:                      6
% 1.07/1.01  sup_num_in_passive:                     3
% 1.07/1.01  sup_num_of_loops:                       9
% 1.07/1.01  sup_fw_superposition:                   2
% 1.07/1.01  sup_bw_superposition:                   0
% 1.07/1.01  sup_immediate_simplified:               0
% 1.07/1.01  sup_given_eliminated:                   0
% 1.07/1.01  comparisons_done:                       0
% 1.07/1.01  comparisons_avoided:                    0
% 1.07/1.01  
% 1.07/1.01  ------ Simplifications
% 1.07/1.01  
% 1.07/1.01  
% 1.07/1.01  sim_fw_subset_subsumed:                 0
% 1.07/1.01  sim_bw_subset_subsumed:                 2
% 1.07/1.01  sim_fw_subsumed:                        0
% 1.07/1.01  sim_bw_subsumed:                        0
% 1.07/1.01  sim_fw_subsumption_res:                 0
% 1.07/1.01  sim_bw_subsumption_res:                 0
% 1.07/1.01  sim_tautology_del:                      0
% 1.07/1.01  sim_eq_tautology_del:                   2
% 1.07/1.01  sim_eq_res_simp:                        0
% 1.07/1.01  sim_fw_demodulated:                     0
% 1.07/1.01  sim_bw_demodulated:                     2
% 1.07/1.01  sim_light_normalised:                   0
% 1.07/1.01  sim_joinable_taut:                      0
% 1.07/1.01  sim_joinable_simp:                      0
% 1.07/1.01  sim_ac_normalised:                      0
% 1.07/1.01  sim_smt_subsumption:                    0
% 1.07/1.01  
%------------------------------------------------------------------------------
