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
% DateTime   : Thu Dec  3 12:26:25 EST 2020

% Result     : Theorem 1.06s
% Output     : CNFRefutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 274 expanded)
%              Number of clauses        :   54 (  74 expanded)
%              Number of leaves         :   10 (  67 expanded)
%              Depth                    :   20
%              Number of atoms          :  466 (1301 expanded)
%              Number of equality atoms :   43 (  45 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),sK2),X0)
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK1),X1),sK1)
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK1),sK2),sK1)
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f40,f48,f47])).

fof(f80,plain,(
    ~ v2_tex_2(k6_domain_1(u1_struct_0(sK1),sK2),sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f76,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f77,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( v2_pre_topc(X1)
              & v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( v2_tdlat_3(X1)
              & v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( v2_pre_topc(X1)
              & v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_pre_topc(X1)
          | ~ v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_pre_topc(X1)
          | ~ v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_pre_topc(X1)
      | ~ v7_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_tex_2(X0,X1) = X2
                  | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1) )
                & ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
                  | k1_tex_2(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_tex_2(X0,X1)) = k6_domain_1(u1_struct_0(X0),X1)
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_179,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_tex_2(u1_struct_0(X0),X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_23])).

cnf(c_180,plain,
    ( v2_tex_2(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_179])).

cnf(c_26,negated_conjecture,
    ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK1),sK2),sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_494,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(sK1),sK2) != u1_struct_0(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_180,c_26])).

cnf(c_495,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k6_domain_1(u1_struct_0(sK1),sK2) != u1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_499,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | k6_domain_1(u1_struct_0(sK1),sK2) != u1_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_495,c_30,c_28])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_697,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_28])).

cnf(c_698,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | v2_pre_topc(X0)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_697])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_700,plain,
    ( v2_pre_topc(X0)
    | ~ m1_pre_topc(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_698,c_29])).

cnf(c_701,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | v2_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_700])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v7_struct_0(X0)
    | v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_672,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v7_struct_0(X0)
    | v1_tdlat_3(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_28])).

cnf(c_673,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ v7_struct_0(X0)
    | v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_672])).

cnf(c_677,plain,
    ( v2_struct_0(X0)
    | v1_tdlat_3(X0)
    | ~ v7_struct_0(X0)
    | ~ m1_pre_topc(X0,sK1)
    | ~ v2_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_673,c_30])).

cnf(c_678,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ v7_struct_0(X0)
    | v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0) ),
    inference(renaming,[status(thm)],[c_677])).

cnf(c_710,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ v7_struct_0(X0)
    | v1_tdlat_3(X0)
    | v2_struct_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_701,c_678])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v7_struct_0(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_590,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v7_struct_0(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_591,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v7_struct_0(k1_tex_2(sK1,X0))
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_590])).

cnf(c_595,plain,
    ( v7_struct_0(k1_tex_2(sK1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_591,c_30])).

cnf(c_596,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v7_struct_0(k1_tex_2(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_595])).

cnf(c_779,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v1_tdlat_3(X0)
    | v2_struct_0(X0)
    | k1_tex_2(sK1,X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_710,c_596])).

cnf(c_780,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,X0),sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v1_tdlat_3(k1_tex_2(sK1,X0))
    | v2_struct_0(k1_tex_2(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_779])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_608,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_609,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v2_struct_0(k1_tex_2(sK1,X0))
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_17,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_726,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_28])).

cnf(c_727,plain,
    ( m1_pre_topc(k1_tex_2(sK1,X0),sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_726])).

cnf(c_784,plain,
    ( v1_tdlat_3(k1_tex_2(sK1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_780,c_30,c_609,c_727])).

cnf(c_785,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v1_tdlat_3(k1_tex_2(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_784])).

cnf(c_800,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(X0)
    | k1_tex_2(sK1,X1) != X0
    | k6_domain_1(u1_struct_0(sK1),sK2) != u1_struct_0(X0) ),
    inference(resolution_lifted,[status(thm)],[c_499,c_785])).

cnf(c_801,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,X0),sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(k1_tex_2(sK1,X0))
    | k6_domain_1(u1_struct_0(sK1),sK2) != u1_struct_0(k1_tex_2(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_800])).

cnf(c_805,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK2) != u1_struct_0(k1_tex_2(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_801,c_30,c_609,c_727])).

cnf(c_1241,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK2) != u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_805])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_pre_topc(k1_tex_2(X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(k1_tex_2(X0,X1))
    | ~ l1_pre_topc(X0)
    | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_195,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_pre_topc(k1_tex_2(X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(k1_tex_2(X0,X1))
    | ~ l1_pre_topc(X0)
    | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_17])).

cnf(c_196,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_pre_topc(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(renaming,[status(thm)],[c_195])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v1_pre_topc(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_201,plain,
    ( v2_struct_0(X1)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_196,c_22,c_20])).

cnf(c_202,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(renaming,[status(thm)],[c_201])).

cnf(c_560,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_202,c_28])).

cnf(c_561,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | k6_domain_1(u1_struct_0(sK1),X0) = u1_struct_0(k1_tex_2(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_560])).

cnf(c_565,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),X0) = u1_struct_0(k1_tex_2(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_561,c_30])).

cnf(c_1238,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK2) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_565])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1241,c_1238,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.95/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.95/1.02  
% 0.95/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.95/1.02  
% 0.95/1.02  ------  iProver source info
% 0.95/1.02  
% 0.95/1.02  git: date: 2020-06-30 10:37:57 +0100
% 0.95/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.95/1.02  git: non_committed_changes: false
% 0.95/1.02  git: last_make_outside_of_git: false
% 0.95/1.02  
% 0.95/1.02  ------ 
% 0.95/1.02  
% 0.95/1.02  ------ Input Options
% 0.95/1.02  
% 0.95/1.02  --out_options                           all
% 0.95/1.02  --tptp_safe_out                         true
% 0.95/1.02  --problem_path                          ""
% 0.95/1.02  --include_path                          ""
% 0.95/1.02  --clausifier                            res/vclausify_rel
% 0.95/1.02  --clausifier_options                    --mode clausify
% 0.95/1.02  --stdin                                 false
% 0.95/1.02  --stats_out                             all
% 0.95/1.02  
% 0.95/1.02  ------ General Options
% 0.95/1.02  
% 0.95/1.02  --fof                                   false
% 0.95/1.02  --time_out_real                         305.
% 0.95/1.02  --time_out_virtual                      -1.
% 0.95/1.02  --symbol_type_check                     false
% 0.95/1.02  --clausify_out                          false
% 0.95/1.02  --sig_cnt_out                           false
% 0.95/1.02  --trig_cnt_out                          false
% 0.95/1.02  --trig_cnt_out_tolerance                1.
% 0.95/1.02  --trig_cnt_out_sk_spl                   false
% 0.95/1.02  --abstr_cl_out                          false
% 0.95/1.02  
% 0.95/1.02  ------ Global Options
% 0.95/1.02  
% 0.95/1.02  --schedule                              default
% 0.95/1.02  --add_important_lit                     false
% 0.95/1.02  --prop_solver_per_cl                    1000
% 0.95/1.02  --min_unsat_core                        false
% 0.95/1.02  --soft_assumptions                      false
% 0.95/1.02  --soft_lemma_size                       3
% 0.95/1.02  --prop_impl_unit_size                   0
% 0.95/1.02  --prop_impl_unit                        []
% 0.95/1.02  --share_sel_clauses                     true
% 0.95/1.02  --reset_solvers                         false
% 0.95/1.02  --bc_imp_inh                            [conj_cone]
% 0.95/1.02  --conj_cone_tolerance                   3.
% 0.95/1.02  --extra_neg_conj                        none
% 0.95/1.02  --large_theory_mode                     true
% 0.95/1.02  --prolific_symb_bound                   200
% 0.95/1.02  --lt_threshold                          2000
% 0.95/1.02  --clause_weak_htbl                      true
% 0.95/1.02  --gc_record_bc_elim                     false
% 0.95/1.02  
% 0.95/1.02  ------ Preprocessing Options
% 0.95/1.02  
% 0.95/1.02  --preprocessing_flag                    true
% 0.95/1.02  --time_out_prep_mult                    0.1
% 0.95/1.02  --splitting_mode                        input
% 0.95/1.02  --splitting_grd                         true
% 0.95/1.02  --splitting_cvd                         false
% 0.95/1.02  --splitting_cvd_svl                     false
% 0.95/1.02  --splitting_nvd                         32
% 0.95/1.02  --sub_typing                            true
% 0.95/1.02  --prep_gs_sim                           true
% 0.95/1.02  --prep_unflatten                        true
% 0.95/1.02  --prep_res_sim                          true
% 0.95/1.02  --prep_upred                            true
% 0.95/1.02  --prep_sem_filter                       exhaustive
% 0.95/1.02  --prep_sem_filter_out                   false
% 0.95/1.02  --pred_elim                             true
% 0.95/1.02  --res_sim_input                         true
% 0.95/1.02  --eq_ax_congr_red                       true
% 0.95/1.02  --pure_diseq_elim                       true
% 0.95/1.02  --brand_transform                       false
% 0.95/1.02  --non_eq_to_eq                          false
% 0.95/1.02  --prep_def_merge                        true
% 0.95/1.02  --prep_def_merge_prop_impl              false
% 0.95/1.02  --prep_def_merge_mbd                    true
% 0.95/1.02  --prep_def_merge_tr_red                 false
% 0.95/1.02  --prep_def_merge_tr_cl                  false
% 0.95/1.02  --smt_preprocessing                     true
% 0.95/1.02  --smt_ac_axioms                         fast
% 0.95/1.02  --preprocessed_out                      false
% 0.95/1.02  --preprocessed_stats                    false
% 0.95/1.02  
% 0.95/1.02  ------ Abstraction refinement Options
% 0.95/1.02  
% 0.95/1.02  --abstr_ref                             []
% 0.95/1.02  --abstr_ref_prep                        false
% 0.95/1.02  --abstr_ref_until_sat                   false
% 0.95/1.02  --abstr_ref_sig_restrict                funpre
% 0.95/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 0.95/1.02  --abstr_ref_under                       []
% 0.95/1.02  
% 0.95/1.02  ------ SAT Options
% 0.95/1.02  
% 0.95/1.02  --sat_mode                              false
% 0.95/1.02  --sat_fm_restart_options                ""
% 0.95/1.02  --sat_gr_def                            false
% 0.95/1.02  --sat_epr_types                         true
% 0.95/1.02  --sat_non_cyclic_types                  false
% 0.95/1.02  --sat_finite_models                     false
% 0.95/1.02  --sat_fm_lemmas                         false
% 0.95/1.02  --sat_fm_prep                           false
% 0.95/1.02  --sat_fm_uc_incr                        true
% 0.95/1.02  --sat_out_model                         small
% 0.95/1.02  --sat_out_clauses                       false
% 0.95/1.02  
% 0.95/1.02  ------ QBF Options
% 0.95/1.02  
% 0.95/1.02  --qbf_mode                              false
% 0.95/1.02  --qbf_elim_univ                         false
% 0.95/1.02  --qbf_dom_inst                          none
% 0.95/1.02  --qbf_dom_pre_inst                      false
% 0.95/1.02  --qbf_sk_in                             false
% 0.95/1.02  --qbf_pred_elim                         true
% 0.95/1.02  --qbf_split                             512
% 0.95/1.02  
% 0.95/1.02  ------ BMC1 Options
% 0.95/1.02  
% 0.95/1.02  --bmc1_incremental                      false
% 0.95/1.02  --bmc1_axioms                           reachable_all
% 0.95/1.02  --bmc1_min_bound                        0
% 0.95/1.02  --bmc1_max_bound                        -1
% 0.95/1.02  --bmc1_max_bound_default                -1
% 0.95/1.02  --bmc1_symbol_reachability              true
% 0.95/1.02  --bmc1_property_lemmas                  false
% 0.95/1.02  --bmc1_k_induction                      false
% 0.95/1.02  --bmc1_non_equiv_states                 false
% 0.95/1.02  --bmc1_deadlock                         false
% 0.95/1.02  --bmc1_ucm                              false
% 0.95/1.02  --bmc1_add_unsat_core                   none
% 0.95/1.02  --bmc1_unsat_core_children              false
% 0.95/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 0.95/1.02  --bmc1_out_stat                         full
% 0.95/1.02  --bmc1_ground_init                      false
% 0.95/1.02  --bmc1_pre_inst_next_state              false
% 0.95/1.02  --bmc1_pre_inst_state                   false
% 0.95/1.02  --bmc1_pre_inst_reach_state             false
% 0.95/1.02  --bmc1_out_unsat_core                   false
% 0.95/1.02  --bmc1_aig_witness_out                  false
% 0.95/1.02  --bmc1_verbose                          false
% 0.95/1.02  --bmc1_dump_clauses_tptp                false
% 0.95/1.02  --bmc1_dump_unsat_core_tptp             false
% 0.95/1.02  --bmc1_dump_file                        -
% 0.95/1.02  --bmc1_ucm_expand_uc_limit              128
% 0.95/1.02  --bmc1_ucm_n_expand_iterations          6
% 0.95/1.02  --bmc1_ucm_extend_mode                  1
% 0.95/1.02  --bmc1_ucm_init_mode                    2
% 0.95/1.02  --bmc1_ucm_cone_mode                    none
% 0.95/1.02  --bmc1_ucm_reduced_relation_type        0
% 0.95/1.02  --bmc1_ucm_relax_model                  4
% 0.95/1.02  --bmc1_ucm_full_tr_after_sat            true
% 0.95/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 0.95/1.02  --bmc1_ucm_layered_model                none
% 0.95/1.02  --bmc1_ucm_max_lemma_size               10
% 0.95/1.02  
% 0.95/1.02  ------ AIG Options
% 0.95/1.02  
% 0.95/1.02  --aig_mode                              false
% 0.95/1.02  
% 0.95/1.02  ------ Instantiation Options
% 0.95/1.02  
% 0.95/1.02  --instantiation_flag                    true
% 0.95/1.02  --inst_sos_flag                         false
% 0.95/1.02  --inst_sos_phase                        true
% 0.95/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.95/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.95/1.02  --inst_lit_sel_side                     num_symb
% 0.95/1.02  --inst_solver_per_active                1400
% 0.95/1.02  --inst_solver_calls_frac                1.
% 0.95/1.02  --inst_passive_queue_type               priority_queues
% 0.95/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.95/1.02  --inst_passive_queues_freq              [25;2]
% 0.95/1.02  --inst_dismatching                      true
% 0.95/1.02  --inst_eager_unprocessed_to_passive     true
% 0.95/1.02  --inst_prop_sim_given                   true
% 0.95/1.02  --inst_prop_sim_new                     false
% 0.95/1.02  --inst_subs_new                         false
% 0.95/1.02  --inst_eq_res_simp                      false
% 0.95/1.02  --inst_subs_given                       false
% 0.95/1.02  --inst_orphan_elimination               true
% 0.95/1.02  --inst_learning_loop_flag               true
% 0.95/1.02  --inst_learning_start                   3000
% 0.95/1.02  --inst_learning_factor                  2
% 0.95/1.02  --inst_start_prop_sim_after_learn       3
% 0.95/1.02  --inst_sel_renew                        solver
% 0.95/1.02  --inst_lit_activity_flag                true
% 0.95/1.02  --inst_restr_to_given                   false
% 0.95/1.02  --inst_activity_threshold               500
% 0.95/1.02  --inst_out_proof                        true
% 0.95/1.02  
% 0.95/1.02  ------ Resolution Options
% 0.95/1.02  
% 0.95/1.02  --resolution_flag                       true
% 0.95/1.02  --res_lit_sel                           adaptive
% 0.95/1.02  --res_lit_sel_side                      none
% 0.95/1.02  --res_ordering                          kbo
% 0.95/1.02  --res_to_prop_solver                    active
% 0.95/1.02  --res_prop_simpl_new                    false
% 0.95/1.02  --res_prop_simpl_given                  true
% 0.95/1.02  --res_passive_queue_type                priority_queues
% 0.95/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.95/1.02  --res_passive_queues_freq               [15;5]
% 0.95/1.02  --res_forward_subs                      full
% 0.95/1.02  --res_backward_subs                     full
% 0.95/1.02  --res_forward_subs_resolution           true
% 0.95/1.02  --res_backward_subs_resolution          true
% 0.95/1.02  --res_orphan_elimination                true
% 0.95/1.02  --res_time_limit                        2.
% 0.95/1.02  --res_out_proof                         true
% 0.95/1.02  
% 0.95/1.02  ------ Superposition Options
% 0.95/1.02  
% 0.95/1.02  --superposition_flag                    true
% 0.95/1.02  --sup_passive_queue_type                priority_queues
% 0.95/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.95/1.02  --sup_passive_queues_freq               [8;1;4]
% 0.95/1.02  --demod_completeness_check              fast
% 0.95/1.02  --demod_use_ground                      true
% 0.95/1.02  --sup_to_prop_solver                    passive
% 0.95/1.02  --sup_prop_simpl_new                    true
% 0.95/1.02  --sup_prop_simpl_given                  true
% 0.95/1.02  --sup_fun_splitting                     false
% 0.95/1.02  --sup_smt_interval                      50000
% 0.95/1.02  
% 0.95/1.02  ------ Superposition Simplification Setup
% 0.95/1.02  
% 0.95/1.02  --sup_indices_passive                   []
% 0.95/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 0.95/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/1.02  --sup_full_bw                           [BwDemod]
% 0.95/1.02  --sup_immed_triv                        [TrivRules]
% 0.95/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.95/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/1.02  --sup_immed_bw_main                     []
% 0.95/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.95/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 0.95/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.95/1.02  
% 0.95/1.02  ------ Combination Options
% 0.95/1.02  
% 0.95/1.02  --comb_res_mult                         3
% 0.95/1.02  --comb_sup_mult                         2
% 0.95/1.02  --comb_inst_mult                        10
% 0.95/1.02  
% 0.95/1.02  ------ Debug Options
% 0.95/1.02  
% 0.95/1.02  --dbg_backtrace                         false
% 0.95/1.02  --dbg_dump_prop_clauses                 false
% 0.95/1.02  --dbg_dump_prop_clauses_file            -
% 0.95/1.02  --dbg_out_stat                          false
% 0.95/1.02  ------ Parsing...
% 0.95/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.95/1.02  
% 0.95/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 0.95/1.02  
% 0.95/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.95/1.02  
% 0.95/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.95/1.02  ------ Proving...
% 0.95/1.02  ------ Problem Properties 
% 0.95/1.02  
% 0.95/1.02  
% 0.95/1.02  clauses                                 12
% 0.95/1.02  conjectures                             1
% 0.95/1.02  EPR                                     2
% 0.95/1.02  Horn                                    11
% 0.95/1.02  unary                                   4
% 0.95/1.02  binary                                  3
% 0.95/1.02  lits                                    27
% 0.95/1.02  lits eq                                 6
% 0.95/1.02  fd_pure                                 0
% 0.95/1.02  fd_pseudo                               0
% 0.95/1.02  fd_cond                                 0
% 0.95/1.02  fd_pseudo_cond                          0
% 0.95/1.02  AC symbols                              0
% 0.95/1.02  
% 0.95/1.02  ------ Schedule dynamic 5 is on 
% 0.95/1.02  
% 0.95/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.95/1.02  
% 0.95/1.02  
% 0.95/1.02  ------ 
% 0.95/1.02  Current options:
% 0.95/1.02  ------ 
% 0.95/1.02  
% 0.95/1.02  ------ Input Options
% 0.95/1.02  
% 0.95/1.02  --out_options                           all
% 0.95/1.02  --tptp_safe_out                         true
% 0.95/1.02  --problem_path                          ""
% 0.95/1.02  --include_path                          ""
% 0.95/1.02  --clausifier                            res/vclausify_rel
% 0.95/1.02  --clausifier_options                    --mode clausify
% 0.95/1.02  --stdin                                 false
% 0.95/1.02  --stats_out                             all
% 0.95/1.02  
% 0.95/1.02  ------ General Options
% 0.95/1.02  
% 0.95/1.02  --fof                                   false
% 0.95/1.02  --time_out_real                         305.
% 0.95/1.02  --time_out_virtual                      -1.
% 0.95/1.02  --symbol_type_check                     false
% 0.95/1.02  --clausify_out                          false
% 0.95/1.02  --sig_cnt_out                           false
% 0.95/1.02  --trig_cnt_out                          false
% 0.95/1.02  --trig_cnt_out_tolerance                1.
% 0.95/1.02  --trig_cnt_out_sk_spl                   false
% 0.95/1.02  --abstr_cl_out                          false
% 0.95/1.02  
% 0.95/1.02  ------ Global Options
% 0.95/1.02  
% 0.95/1.02  --schedule                              default
% 0.95/1.02  --add_important_lit                     false
% 0.95/1.02  --prop_solver_per_cl                    1000
% 0.95/1.02  --min_unsat_core                        false
% 0.95/1.02  --soft_assumptions                      false
% 0.95/1.02  --soft_lemma_size                       3
% 0.95/1.02  --prop_impl_unit_size                   0
% 0.95/1.02  --prop_impl_unit                        []
% 0.95/1.02  --share_sel_clauses                     true
% 0.95/1.02  --reset_solvers                         false
% 0.95/1.02  --bc_imp_inh                            [conj_cone]
% 0.95/1.02  --conj_cone_tolerance                   3.
% 0.95/1.02  --extra_neg_conj                        none
% 0.95/1.02  --large_theory_mode                     true
% 0.95/1.02  --prolific_symb_bound                   200
% 0.95/1.02  --lt_threshold                          2000
% 0.95/1.02  --clause_weak_htbl                      true
% 0.95/1.02  --gc_record_bc_elim                     false
% 0.95/1.02  
% 0.95/1.02  ------ Preprocessing Options
% 0.95/1.02  
% 0.95/1.02  --preprocessing_flag                    true
% 0.95/1.02  --time_out_prep_mult                    0.1
% 0.95/1.02  --splitting_mode                        input
% 0.95/1.02  --splitting_grd                         true
% 0.95/1.02  --splitting_cvd                         false
% 0.95/1.02  --splitting_cvd_svl                     false
% 0.95/1.02  --splitting_nvd                         32
% 0.95/1.02  --sub_typing                            true
% 0.95/1.02  --prep_gs_sim                           true
% 0.95/1.02  --prep_unflatten                        true
% 0.95/1.02  --prep_res_sim                          true
% 0.95/1.02  --prep_upred                            true
% 0.95/1.02  --prep_sem_filter                       exhaustive
% 0.95/1.02  --prep_sem_filter_out                   false
% 0.95/1.02  --pred_elim                             true
% 0.95/1.02  --res_sim_input                         true
% 0.95/1.02  --eq_ax_congr_red                       true
% 0.95/1.02  --pure_diseq_elim                       true
% 0.95/1.02  --brand_transform                       false
% 0.95/1.02  --non_eq_to_eq                          false
% 0.95/1.02  --prep_def_merge                        true
% 0.95/1.02  --prep_def_merge_prop_impl              false
% 0.95/1.02  --prep_def_merge_mbd                    true
% 0.95/1.02  --prep_def_merge_tr_red                 false
% 0.95/1.02  --prep_def_merge_tr_cl                  false
% 0.95/1.02  --smt_preprocessing                     true
% 0.95/1.02  --smt_ac_axioms                         fast
% 0.95/1.02  --preprocessed_out                      false
% 0.95/1.02  --preprocessed_stats                    false
% 0.95/1.02  
% 0.95/1.02  ------ Abstraction refinement Options
% 0.95/1.02  
% 0.95/1.02  --abstr_ref                             []
% 0.95/1.02  --abstr_ref_prep                        false
% 0.95/1.02  --abstr_ref_until_sat                   false
% 0.95/1.02  --abstr_ref_sig_restrict                funpre
% 0.95/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 0.95/1.02  --abstr_ref_under                       []
% 0.95/1.02  
% 0.95/1.02  ------ SAT Options
% 0.95/1.02  
% 0.95/1.02  --sat_mode                              false
% 0.95/1.02  --sat_fm_restart_options                ""
% 0.95/1.02  --sat_gr_def                            false
% 0.95/1.02  --sat_epr_types                         true
% 0.95/1.02  --sat_non_cyclic_types                  false
% 0.95/1.02  --sat_finite_models                     false
% 0.95/1.02  --sat_fm_lemmas                         false
% 0.95/1.02  --sat_fm_prep                           false
% 0.95/1.02  --sat_fm_uc_incr                        true
% 0.95/1.02  --sat_out_model                         small
% 0.95/1.02  --sat_out_clauses                       false
% 0.95/1.02  
% 0.95/1.02  ------ QBF Options
% 0.95/1.02  
% 0.95/1.02  --qbf_mode                              false
% 0.95/1.02  --qbf_elim_univ                         false
% 0.95/1.02  --qbf_dom_inst                          none
% 0.95/1.02  --qbf_dom_pre_inst                      false
% 0.95/1.02  --qbf_sk_in                             false
% 0.95/1.02  --qbf_pred_elim                         true
% 0.95/1.02  --qbf_split                             512
% 0.95/1.02  
% 0.95/1.02  ------ BMC1 Options
% 0.95/1.02  
% 0.95/1.02  --bmc1_incremental                      false
% 0.95/1.02  --bmc1_axioms                           reachable_all
% 0.95/1.02  --bmc1_min_bound                        0
% 0.95/1.02  --bmc1_max_bound                        -1
% 0.95/1.02  --bmc1_max_bound_default                -1
% 1.06/1.02  --bmc1_symbol_reachability              true
% 1.06/1.02  --bmc1_property_lemmas                  false
% 1.06/1.02  --bmc1_k_induction                      false
% 1.06/1.02  --bmc1_non_equiv_states                 false
% 1.06/1.02  --bmc1_deadlock                         false
% 1.06/1.02  --bmc1_ucm                              false
% 1.06/1.02  --bmc1_add_unsat_core                   none
% 1.06/1.02  --bmc1_unsat_core_children              false
% 1.06/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.06/1.02  --bmc1_out_stat                         full
% 1.06/1.02  --bmc1_ground_init                      false
% 1.06/1.02  --bmc1_pre_inst_next_state              false
% 1.06/1.02  --bmc1_pre_inst_state                   false
% 1.06/1.02  --bmc1_pre_inst_reach_state             false
% 1.06/1.02  --bmc1_out_unsat_core                   false
% 1.06/1.02  --bmc1_aig_witness_out                  false
% 1.06/1.02  --bmc1_verbose                          false
% 1.06/1.02  --bmc1_dump_clauses_tptp                false
% 1.06/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.06/1.02  --bmc1_dump_file                        -
% 1.06/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.06/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.06/1.02  --bmc1_ucm_extend_mode                  1
% 1.06/1.02  --bmc1_ucm_init_mode                    2
% 1.06/1.02  --bmc1_ucm_cone_mode                    none
% 1.06/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.06/1.02  --bmc1_ucm_relax_model                  4
% 1.06/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.06/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.06/1.02  --bmc1_ucm_layered_model                none
% 1.06/1.02  --bmc1_ucm_max_lemma_size               10
% 1.06/1.02  
% 1.06/1.02  ------ AIG Options
% 1.06/1.02  
% 1.06/1.02  --aig_mode                              false
% 1.06/1.02  
% 1.06/1.02  ------ Instantiation Options
% 1.06/1.02  
% 1.06/1.02  --instantiation_flag                    true
% 1.06/1.02  --inst_sos_flag                         false
% 1.06/1.02  --inst_sos_phase                        true
% 1.06/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.06/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.06/1.02  --inst_lit_sel_side                     none
% 1.06/1.02  --inst_solver_per_active                1400
% 1.06/1.02  --inst_solver_calls_frac                1.
% 1.06/1.02  --inst_passive_queue_type               priority_queues
% 1.06/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.06/1.02  --inst_passive_queues_freq              [25;2]
% 1.06/1.02  --inst_dismatching                      true
% 1.06/1.02  --inst_eager_unprocessed_to_passive     true
% 1.06/1.02  --inst_prop_sim_given                   true
% 1.06/1.02  --inst_prop_sim_new                     false
% 1.06/1.02  --inst_subs_new                         false
% 1.06/1.02  --inst_eq_res_simp                      false
% 1.06/1.02  --inst_subs_given                       false
% 1.06/1.02  --inst_orphan_elimination               true
% 1.06/1.02  --inst_learning_loop_flag               true
% 1.06/1.02  --inst_learning_start                   3000
% 1.06/1.02  --inst_learning_factor                  2
% 1.06/1.02  --inst_start_prop_sim_after_learn       3
% 1.06/1.02  --inst_sel_renew                        solver
% 1.06/1.02  --inst_lit_activity_flag                true
% 1.06/1.02  --inst_restr_to_given                   false
% 1.06/1.02  --inst_activity_threshold               500
% 1.06/1.02  --inst_out_proof                        true
% 1.06/1.02  
% 1.06/1.02  ------ Resolution Options
% 1.06/1.02  
% 1.06/1.02  --resolution_flag                       false
% 1.06/1.02  --res_lit_sel                           adaptive
% 1.06/1.02  --res_lit_sel_side                      none
% 1.06/1.02  --res_ordering                          kbo
% 1.06/1.02  --res_to_prop_solver                    active
% 1.06/1.02  --res_prop_simpl_new                    false
% 1.06/1.02  --res_prop_simpl_given                  true
% 1.06/1.02  --res_passive_queue_type                priority_queues
% 1.06/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.06/1.02  --res_passive_queues_freq               [15;5]
% 1.06/1.02  --res_forward_subs                      full
% 1.06/1.02  --res_backward_subs                     full
% 1.06/1.02  --res_forward_subs_resolution           true
% 1.06/1.02  --res_backward_subs_resolution          true
% 1.06/1.02  --res_orphan_elimination                true
% 1.06/1.02  --res_time_limit                        2.
% 1.06/1.02  --res_out_proof                         true
% 1.06/1.02  
% 1.06/1.02  ------ Superposition Options
% 1.06/1.02  
% 1.06/1.02  --superposition_flag                    true
% 1.06/1.02  --sup_passive_queue_type                priority_queues
% 1.06/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.06/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.06/1.02  --demod_completeness_check              fast
% 1.06/1.02  --demod_use_ground                      true
% 1.06/1.02  --sup_to_prop_solver                    passive
% 1.06/1.02  --sup_prop_simpl_new                    true
% 1.06/1.02  --sup_prop_simpl_given                  true
% 1.06/1.02  --sup_fun_splitting                     false
% 1.06/1.02  --sup_smt_interval                      50000
% 1.06/1.02  
% 1.06/1.02  ------ Superposition Simplification Setup
% 1.06/1.02  
% 1.06/1.02  --sup_indices_passive                   []
% 1.06/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.06/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.06/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.06/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.06/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.06/1.02  --sup_full_bw                           [BwDemod]
% 1.06/1.02  --sup_immed_triv                        [TrivRules]
% 1.06/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.06/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.06/1.02  --sup_immed_bw_main                     []
% 1.06/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.06/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.06/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.06/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.06/1.02  
% 1.06/1.02  ------ Combination Options
% 1.06/1.02  
% 1.06/1.02  --comb_res_mult                         3
% 1.06/1.02  --comb_sup_mult                         2
% 1.06/1.02  --comb_inst_mult                        10
% 1.06/1.02  
% 1.06/1.02  ------ Debug Options
% 1.06/1.02  
% 1.06/1.02  --dbg_backtrace                         false
% 1.06/1.02  --dbg_dump_prop_clauses                 false
% 1.06/1.02  --dbg_dump_prop_clauses_file            -
% 1.06/1.02  --dbg_out_stat                          false
% 1.06/1.02  
% 1.06/1.02  
% 1.06/1.02  
% 1.06/1.02  
% 1.06/1.02  ------ Proving...
% 1.06/1.02  
% 1.06/1.02  
% 1.06/1.02  % SZS status Theorem for theBenchmark.p
% 1.06/1.02  
% 1.06/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.06/1.02  
% 1.06/1.02  fof(f14,axiom,(
% 1.06/1.02    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 1.06/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.06/1.03  
% 1.06/1.03  fof(f37,plain,(
% 1.06/1.03    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.06/1.03    inference(ennf_transformation,[],[f14])).
% 1.06/1.03  
% 1.06/1.03  fof(f38,plain,(
% 1.06/1.03    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.06/1.03    inference(flattening,[],[f37])).
% 1.06/1.03  
% 1.06/1.03  fof(f46,plain,(
% 1.06/1.03    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.06/1.03    inference(nnf_transformation,[],[f38])).
% 1.06/1.03  
% 1.06/1.03  fof(f75,plain,(
% 1.06/1.03    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.06/1.03    inference(cnf_transformation,[],[f46])).
% 1.06/1.03  
% 1.06/1.03  fof(f83,plain,(
% 1.06/1.03    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.06/1.03    inference(equality_resolution,[],[f75])).
% 1.06/1.03  
% 1.06/1.03  fof(f13,axiom,(
% 1.06/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.06/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.06/1.03  
% 1.06/1.03  fof(f36,plain,(
% 1.06/1.03    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.06/1.03    inference(ennf_transformation,[],[f13])).
% 1.06/1.03  
% 1.06/1.03  fof(f73,plain,(
% 1.06/1.03    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.06/1.03    inference(cnf_transformation,[],[f36])).
% 1.06/1.03  
% 1.06/1.03  fof(f15,conjecture,(
% 1.06/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 1.06/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.06/1.03  
% 1.06/1.03  fof(f16,negated_conjecture,(
% 1.06/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 1.06/1.03    inference(negated_conjecture,[],[f15])).
% 1.06/1.03  
% 1.06/1.03  fof(f39,plain,(
% 1.06/1.03    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.06/1.03    inference(ennf_transformation,[],[f16])).
% 1.06/1.03  
% 1.06/1.03  fof(f40,plain,(
% 1.06/1.03    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.06/1.03    inference(flattening,[],[f39])).
% 1.06/1.03  
% 1.06/1.03  fof(f48,plain,(
% 1.06/1.03    ( ! [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) => (~v2_tex_2(k6_domain_1(u1_struct_0(X0),sK2),X0) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.06/1.03    introduced(choice_axiom,[])).
% 1.06/1.03  
% 1.06/1.03  fof(f47,plain,(
% 1.06/1.03    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(sK1),X1),sK1) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.06/1.03    introduced(choice_axiom,[])).
% 1.06/1.03  
% 1.06/1.03  fof(f49,plain,(
% 1.06/1.03    (~v2_tex_2(k6_domain_1(u1_struct_0(sK1),sK2),sK1) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.06/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f40,f48,f47])).
% 1.06/1.03  
% 1.06/1.03  fof(f80,plain,(
% 1.06/1.03    ~v2_tex_2(k6_domain_1(u1_struct_0(sK1),sK2),sK1)),
% 1.06/1.03    inference(cnf_transformation,[],[f49])).
% 1.06/1.03  
% 1.06/1.03  fof(f76,plain,(
% 1.06/1.03    ~v2_struct_0(sK1)),
% 1.06/1.03    inference(cnf_transformation,[],[f49])).
% 1.06/1.03  
% 1.06/1.03  fof(f78,plain,(
% 1.06/1.03    l1_pre_topc(sK1)),
% 1.06/1.03    inference(cnf_transformation,[],[f49])).
% 1.06/1.03  
% 1.06/1.03  fof(f4,axiom,(
% 1.06/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.06/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.06/1.03  
% 1.06/1.03  fof(f20,plain,(
% 1.06/1.03    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.06/1.03    inference(ennf_transformation,[],[f4])).
% 1.06/1.03  
% 1.06/1.03  fof(f21,plain,(
% 1.06/1.03    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.06/1.03    inference(flattening,[],[f20])).
% 1.06/1.03  
% 1.06/1.03  fof(f57,plain,(
% 1.06/1.03    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.06/1.03    inference(cnf_transformation,[],[f21])).
% 1.06/1.03  
% 1.06/1.03  fof(f77,plain,(
% 1.06/1.03    v2_pre_topc(sK1)),
% 1.06/1.03    inference(cnf_transformation,[],[f49])).
% 1.06/1.03  
% 1.06/1.03  fof(f8,axiom,(
% 1.06/1.03    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((v2_pre_topc(X1) & v7_struct_0(X1) & ~v2_struct_0(X1)) => (v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 1.06/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.06/1.03  
% 1.06/1.03  fof(f17,plain,(
% 1.06/1.03    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((v2_pre_topc(X1) & v7_struct_0(X1) & ~v2_struct_0(X1)) => (v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 1.06/1.03    inference(pure_predicate_removal,[],[f8])).
% 1.06/1.03  
% 1.06/1.03  fof(f27,plain,(
% 1.06/1.03    ! [X0] : (! [X1] : (((v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.06/1.03    inference(ennf_transformation,[],[f17])).
% 1.06/1.03  
% 1.06/1.03  fof(f28,plain,(
% 1.06/1.03    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & ~v2_struct_0(X1)) | ~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.06/1.03    inference(flattening,[],[f27])).
% 1.06/1.03  
% 1.06/1.03  fof(f62,plain,(
% 1.06/1.03    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.06/1.03    inference(cnf_transformation,[],[f28])).
% 1.06/1.03  
% 1.06/1.03  fof(f12,axiom,(
% 1.06/1.03    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.06/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.06/1.03  
% 1.06/1.03  fof(f34,plain,(
% 1.06/1.03    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.06/1.03    inference(ennf_transformation,[],[f12])).
% 1.06/1.03  
% 1.06/1.03  fof(f35,plain,(
% 1.06/1.03    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.06/1.03    inference(flattening,[],[f34])).
% 1.06/1.03  
% 1.06/1.03  fof(f71,plain,(
% 1.06/1.03    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.06/1.03    inference(cnf_transformation,[],[f35])).
% 1.06/1.03  
% 1.06/1.03  fof(f11,axiom,(
% 1.06/1.03    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.06/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.06/1.03  
% 1.06/1.03  fof(f32,plain,(
% 1.06/1.03    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.06/1.03    inference(ennf_transformation,[],[f11])).
% 1.06/1.03  
% 1.06/1.03  fof(f33,plain,(
% 1.06/1.03    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.06/1.03    inference(flattening,[],[f32])).
% 1.06/1.03  
% 1.06/1.03  fof(f67,plain,(
% 1.06/1.03    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.06/1.03    inference(cnf_transformation,[],[f33])).
% 1.06/1.03  
% 1.06/1.03  fof(f69,plain,(
% 1.06/1.03    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.06/1.03    inference(cnf_transformation,[],[f33])).
% 1.06/1.03  
% 1.06/1.03  fof(f9,axiom,(
% 1.06/1.03    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)))))),
% 1.06/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.06/1.03  
% 1.06/1.03  fof(f29,plain,(
% 1.06/1.03    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.06/1.03    inference(ennf_transformation,[],[f9])).
% 1.06/1.03  
% 1.06/1.03  fof(f30,plain,(
% 1.06/1.03    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.06/1.03    inference(flattening,[],[f29])).
% 1.06/1.03  
% 1.06/1.03  fof(f44,plain,(
% 1.06/1.03    ! [X0] : (! [X1] : (! [X2] : (((k1_tex_2(X0,X1) = X2 | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1)) & (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.06/1.03    inference(nnf_transformation,[],[f30])).
% 1.06/1.03  
% 1.06/1.03  fof(f63,plain,(
% 1.06/1.03    ( ! [X2,X0,X1] : (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.06/1.03    inference(cnf_transformation,[],[f44])).
% 1.06/1.03  
% 1.06/1.03  fof(f81,plain,(
% 1.06/1.03    ( ! [X0,X1] : (u1_struct_0(k1_tex_2(X0,X1)) = k6_domain_1(u1_struct_0(X0),X1) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | ~v1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.06/1.03    inference(equality_resolution,[],[f63])).
% 1.06/1.03  
% 1.06/1.03  fof(f70,plain,(
% 1.06/1.03    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.06/1.03    inference(cnf_transformation,[],[f35])).
% 1.06/1.03  
% 1.06/1.03  fof(f72,plain,(
% 1.06/1.03    ( ! [X0,X1] : (v1_pre_topc(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.06/1.03    inference(cnf_transformation,[],[f35])).
% 1.06/1.03  
% 1.06/1.03  fof(f79,plain,(
% 1.06/1.03    m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.06/1.03    inference(cnf_transformation,[],[f49])).
% 1.06/1.03  
% 1.06/1.03  cnf(c_24,plain,
% 1.06/1.03      ( v2_tex_2(u1_struct_0(X0),X1)
% 1.06/1.03      | ~ m1_pre_topc(X0,X1)
% 1.06/1.03      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.06/1.03      | ~ v1_tdlat_3(X0)
% 1.06/1.03      | v2_struct_0(X1)
% 1.06/1.03      | v2_struct_0(X0)
% 1.06/1.03      | ~ l1_pre_topc(X1) ),
% 1.06/1.03      inference(cnf_transformation,[],[f83]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_23,plain,
% 1.06/1.03      ( ~ m1_pre_topc(X0,X1)
% 1.06/1.03      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.06/1.03      | ~ l1_pre_topc(X1) ),
% 1.06/1.03      inference(cnf_transformation,[],[f73]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_179,plain,
% 1.06/1.03      ( ~ m1_pre_topc(X0,X1)
% 1.06/1.03      | v2_tex_2(u1_struct_0(X0),X1)
% 1.06/1.03      | ~ v1_tdlat_3(X0)
% 1.06/1.03      | v2_struct_0(X1)
% 1.06/1.03      | v2_struct_0(X0)
% 1.06/1.03      | ~ l1_pre_topc(X1) ),
% 1.06/1.03      inference(global_propositional_subsumption,
% 1.06/1.03                [status(thm)],
% 1.06/1.03                [c_24,c_23]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_180,plain,
% 1.06/1.03      ( v2_tex_2(u1_struct_0(X0),X1)
% 1.06/1.03      | ~ m1_pre_topc(X0,X1)
% 1.06/1.03      | ~ v1_tdlat_3(X0)
% 1.06/1.03      | v2_struct_0(X1)
% 1.06/1.03      | v2_struct_0(X0)
% 1.06/1.03      | ~ l1_pre_topc(X1) ),
% 1.06/1.03      inference(renaming,[status(thm)],[c_179]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_26,negated_conjecture,
% 1.06/1.03      ( ~ v2_tex_2(k6_domain_1(u1_struct_0(sK1),sK2),sK1) ),
% 1.06/1.03      inference(cnf_transformation,[],[f80]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_494,plain,
% 1.06/1.03      ( ~ m1_pre_topc(X0,X1)
% 1.06/1.03      | ~ v1_tdlat_3(X0)
% 1.06/1.03      | v2_struct_0(X1)
% 1.06/1.03      | v2_struct_0(X0)
% 1.06/1.03      | ~ l1_pre_topc(X1)
% 1.06/1.03      | k6_domain_1(u1_struct_0(sK1),sK2) != u1_struct_0(X0)
% 1.06/1.03      | sK1 != X1 ),
% 1.06/1.03      inference(resolution_lifted,[status(thm)],[c_180,c_26]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_495,plain,
% 1.06/1.03      ( ~ m1_pre_topc(X0,sK1)
% 1.06/1.03      | ~ v1_tdlat_3(X0)
% 1.06/1.03      | v2_struct_0(X0)
% 1.06/1.03      | v2_struct_0(sK1)
% 1.06/1.03      | ~ l1_pre_topc(sK1)
% 1.06/1.03      | k6_domain_1(u1_struct_0(sK1),sK2) != u1_struct_0(X0) ),
% 1.06/1.03      inference(unflattening,[status(thm)],[c_494]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_30,negated_conjecture,
% 1.06/1.03      ( ~ v2_struct_0(sK1) ),
% 1.06/1.03      inference(cnf_transformation,[],[f76]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_28,negated_conjecture,
% 1.06/1.03      ( l1_pre_topc(sK1) ),
% 1.06/1.03      inference(cnf_transformation,[],[f78]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_499,plain,
% 1.06/1.03      ( ~ m1_pre_topc(X0,sK1)
% 1.06/1.03      | ~ v1_tdlat_3(X0)
% 1.06/1.03      | v2_struct_0(X0)
% 1.06/1.03      | k6_domain_1(u1_struct_0(sK1),sK2) != u1_struct_0(X0) ),
% 1.06/1.03      inference(global_propositional_subsumption,
% 1.06/1.03                [status(thm)],
% 1.06/1.03                [c_495,c_30,c_28]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_7,plain,
% 1.06/1.03      ( ~ m1_pre_topc(X0,X1)
% 1.06/1.03      | ~ l1_pre_topc(X1)
% 1.06/1.03      | ~ v2_pre_topc(X1)
% 1.06/1.03      | v2_pre_topc(X0) ),
% 1.06/1.03      inference(cnf_transformation,[],[f57]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_697,plain,
% 1.06/1.03      ( ~ m1_pre_topc(X0,X1)
% 1.06/1.03      | ~ v2_pre_topc(X1)
% 1.06/1.03      | v2_pre_topc(X0)
% 1.06/1.03      | sK1 != X1 ),
% 1.06/1.03      inference(resolution_lifted,[status(thm)],[c_7,c_28]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_698,plain,
% 1.06/1.03      ( ~ m1_pre_topc(X0,sK1) | v2_pre_topc(X0) | ~ v2_pre_topc(sK1) ),
% 1.06/1.03      inference(unflattening,[status(thm)],[c_697]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_29,negated_conjecture,
% 1.06/1.03      ( v2_pre_topc(sK1) ),
% 1.06/1.03      inference(cnf_transformation,[],[f77]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_700,plain,
% 1.06/1.03      ( v2_pre_topc(X0) | ~ m1_pre_topc(X0,sK1) ),
% 1.06/1.03      inference(global_propositional_subsumption,
% 1.06/1.03                [status(thm)],
% 1.06/1.03                [c_698,c_29]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_701,plain,
% 1.06/1.03      ( ~ m1_pre_topc(X0,sK1) | v2_pre_topc(X0) ),
% 1.06/1.03      inference(renaming,[status(thm)],[c_700]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_11,plain,
% 1.06/1.03      ( ~ m1_pre_topc(X0,X1)
% 1.06/1.03      | ~ v7_struct_0(X0)
% 1.06/1.03      | v1_tdlat_3(X0)
% 1.06/1.03      | v2_struct_0(X1)
% 1.06/1.03      | v2_struct_0(X0)
% 1.06/1.03      | ~ l1_pre_topc(X1)
% 1.06/1.03      | ~ v2_pre_topc(X0) ),
% 1.06/1.03      inference(cnf_transformation,[],[f62]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_672,plain,
% 1.06/1.03      ( ~ m1_pre_topc(X0,X1)
% 1.06/1.03      | ~ v7_struct_0(X0)
% 1.06/1.03      | v1_tdlat_3(X0)
% 1.06/1.03      | v2_struct_0(X1)
% 1.06/1.03      | v2_struct_0(X0)
% 1.06/1.03      | ~ v2_pre_topc(X0)
% 1.06/1.03      | sK1 != X1 ),
% 1.06/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_28]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_673,plain,
% 1.06/1.03      ( ~ m1_pre_topc(X0,sK1)
% 1.06/1.03      | ~ v7_struct_0(X0)
% 1.06/1.03      | v1_tdlat_3(X0)
% 1.06/1.03      | v2_struct_0(X0)
% 1.06/1.03      | v2_struct_0(sK1)
% 1.06/1.03      | ~ v2_pre_topc(X0) ),
% 1.06/1.03      inference(unflattening,[status(thm)],[c_672]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_677,plain,
% 1.06/1.03      ( v2_struct_0(X0)
% 1.06/1.03      | v1_tdlat_3(X0)
% 1.06/1.03      | ~ v7_struct_0(X0)
% 1.06/1.03      | ~ m1_pre_topc(X0,sK1)
% 1.06/1.03      | ~ v2_pre_topc(X0) ),
% 1.06/1.03      inference(global_propositional_subsumption,
% 1.06/1.03                [status(thm)],
% 1.06/1.03                [c_673,c_30]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_678,plain,
% 1.06/1.03      ( ~ m1_pre_topc(X0,sK1)
% 1.06/1.03      | ~ v7_struct_0(X0)
% 1.06/1.03      | v1_tdlat_3(X0)
% 1.06/1.03      | v2_struct_0(X0)
% 1.06/1.03      | ~ v2_pre_topc(X0) ),
% 1.06/1.03      inference(renaming,[status(thm)],[c_677]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_710,plain,
% 1.06/1.03      ( ~ m1_pre_topc(X0,sK1)
% 1.06/1.03      | ~ v7_struct_0(X0)
% 1.06/1.03      | v1_tdlat_3(X0)
% 1.06/1.03      | v2_struct_0(X0) ),
% 1.06/1.03      inference(backward_subsumption_resolution,
% 1.06/1.03                [status(thm)],
% 1.06/1.03                [c_701,c_678]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_21,plain,
% 1.06/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.06/1.03      | v7_struct_0(k1_tex_2(X1,X0))
% 1.06/1.03      | v2_struct_0(X1)
% 1.06/1.03      | ~ l1_pre_topc(X1) ),
% 1.06/1.03      inference(cnf_transformation,[],[f71]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_590,plain,
% 1.06/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.06/1.03      | v7_struct_0(k1_tex_2(X1,X0))
% 1.06/1.03      | v2_struct_0(X1)
% 1.06/1.03      | sK1 != X1 ),
% 1.06/1.03      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_591,plain,
% 1.06/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.06/1.03      | v7_struct_0(k1_tex_2(sK1,X0))
% 1.06/1.03      | v2_struct_0(sK1) ),
% 1.06/1.03      inference(unflattening,[status(thm)],[c_590]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_595,plain,
% 1.06/1.03      ( v7_struct_0(k1_tex_2(sK1,X0))
% 1.06/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.06/1.03      inference(global_propositional_subsumption,
% 1.06/1.03                [status(thm)],
% 1.06/1.03                [c_591,c_30]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_596,plain,
% 1.06/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.06/1.03      | v7_struct_0(k1_tex_2(sK1,X0)) ),
% 1.06/1.03      inference(renaming,[status(thm)],[c_595]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_779,plain,
% 1.06/1.03      ( ~ m1_pre_topc(X0,sK1)
% 1.06/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.06/1.03      | v1_tdlat_3(X0)
% 1.06/1.03      | v2_struct_0(X0)
% 1.06/1.03      | k1_tex_2(sK1,X1) != X0 ),
% 1.06/1.03      inference(resolution_lifted,[status(thm)],[c_710,c_596]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_780,plain,
% 1.06/1.03      ( ~ m1_pre_topc(k1_tex_2(sK1,X0),sK1)
% 1.06/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.06/1.03      | v1_tdlat_3(k1_tex_2(sK1,X0))
% 1.06/1.03      | v2_struct_0(k1_tex_2(sK1,X0)) ),
% 1.06/1.03      inference(unflattening,[status(thm)],[c_779]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_19,plain,
% 1.06/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.06/1.03      | v2_struct_0(X1)
% 1.06/1.03      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 1.06/1.03      | ~ l1_pre_topc(X1) ),
% 1.06/1.03      inference(cnf_transformation,[],[f67]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_608,plain,
% 1.06/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.06/1.03      | v2_struct_0(X1)
% 1.06/1.03      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 1.06/1.03      | sK1 != X1 ),
% 1.06/1.03      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_609,plain,
% 1.06/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.06/1.03      | ~ v2_struct_0(k1_tex_2(sK1,X0))
% 1.06/1.03      | v2_struct_0(sK1) ),
% 1.06/1.03      inference(unflattening,[status(thm)],[c_608]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_17,plain,
% 1.06/1.03      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
% 1.06/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.06/1.03      | v2_struct_0(X0)
% 1.06/1.03      | ~ l1_pre_topc(X0) ),
% 1.06/1.03      inference(cnf_transformation,[],[f69]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_726,plain,
% 1.06/1.03      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
% 1.06/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.06/1.03      | v2_struct_0(X0)
% 1.06/1.03      | sK1 != X0 ),
% 1.06/1.03      inference(resolution_lifted,[status(thm)],[c_17,c_28]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_727,plain,
% 1.06/1.03      ( m1_pre_topc(k1_tex_2(sK1,X0),sK1)
% 1.06/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.06/1.03      | v2_struct_0(sK1) ),
% 1.06/1.03      inference(unflattening,[status(thm)],[c_726]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_784,plain,
% 1.06/1.03      ( v1_tdlat_3(k1_tex_2(sK1,X0))
% 1.06/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.06/1.03      inference(global_propositional_subsumption,
% 1.06/1.03                [status(thm)],
% 1.06/1.03                [c_780,c_30,c_609,c_727]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_785,plain,
% 1.06/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.06/1.03      | v1_tdlat_3(k1_tex_2(sK1,X0)) ),
% 1.06/1.03      inference(renaming,[status(thm)],[c_784]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_800,plain,
% 1.06/1.03      ( ~ m1_pre_topc(X0,sK1)
% 1.06/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.06/1.03      | v2_struct_0(X0)
% 1.06/1.03      | k1_tex_2(sK1,X1) != X0
% 1.06/1.03      | k6_domain_1(u1_struct_0(sK1),sK2) != u1_struct_0(X0) ),
% 1.06/1.03      inference(resolution_lifted,[status(thm)],[c_499,c_785]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_801,plain,
% 1.06/1.03      ( ~ m1_pre_topc(k1_tex_2(sK1,X0),sK1)
% 1.06/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.06/1.03      | v2_struct_0(k1_tex_2(sK1,X0))
% 1.06/1.03      | k6_domain_1(u1_struct_0(sK1),sK2) != u1_struct_0(k1_tex_2(sK1,X0)) ),
% 1.06/1.03      inference(unflattening,[status(thm)],[c_800]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_805,plain,
% 1.06/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.06/1.03      | k6_domain_1(u1_struct_0(sK1),sK2) != u1_struct_0(k1_tex_2(sK1,X0)) ),
% 1.06/1.03      inference(global_propositional_subsumption,
% 1.06/1.03                [status(thm)],
% 1.06/1.03                [c_801,c_30,c_609,c_727]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_1241,plain,
% 1.06/1.03      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.06/1.03      | k6_domain_1(u1_struct_0(sK1),sK2) != u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 1.06/1.03      inference(instantiation,[status(thm)],[c_805]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_14,plain,
% 1.06/1.03      ( ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
% 1.06/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.06/1.03      | ~ v1_pre_topc(k1_tex_2(X0,X1))
% 1.06/1.03      | v2_struct_0(X0)
% 1.06/1.03      | v2_struct_0(k1_tex_2(X0,X1))
% 1.06/1.03      | ~ l1_pre_topc(X0)
% 1.06/1.03      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
% 1.06/1.03      inference(cnf_transformation,[],[f81]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_195,plain,
% 1.06/1.03      ( ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.06/1.03      | ~ v1_pre_topc(k1_tex_2(X0,X1))
% 1.06/1.03      | v2_struct_0(X0)
% 1.06/1.03      | v2_struct_0(k1_tex_2(X0,X1))
% 1.06/1.03      | ~ l1_pre_topc(X0)
% 1.06/1.03      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
% 1.06/1.03      inference(global_propositional_subsumption,
% 1.06/1.03                [status(thm)],
% 1.06/1.03                [c_14,c_17]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_196,plain,
% 1.06/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.06/1.03      | ~ v1_pre_topc(k1_tex_2(X1,X0))
% 1.06/1.03      | v2_struct_0(X1)
% 1.06/1.03      | v2_struct_0(k1_tex_2(X1,X0))
% 1.06/1.03      | ~ l1_pre_topc(X1)
% 1.06/1.03      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
% 1.06/1.03      inference(renaming,[status(thm)],[c_195]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_22,plain,
% 1.06/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.06/1.03      | v2_struct_0(X1)
% 1.06/1.03      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 1.06/1.03      | ~ l1_pre_topc(X1) ),
% 1.06/1.03      inference(cnf_transformation,[],[f70]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_20,plain,
% 1.06/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.06/1.03      | v1_pre_topc(k1_tex_2(X1,X0))
% 1.06/1.03      | v2_struct_0(X1)
% 1.06/1.03      | ~ l1_pre_topc(X1) ),
% 1.06/1.03      inference(cnf_transformation,[],[f72]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_201,plain,
% 1.06/1.03      ( v2_struct_0(X1)
% 1.06/1.03      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.06/1.03      | ~ l1_pre_topc(X1)
% 1.06/1.03      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
% 1.06/1.03      inference(global_propositional_subsumption,
% 1.06/1.03                [status(thm)],
% 1.06/1.03                [c_196,c_22,c_20]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_202,plain,
% 1.06/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.06/1.03      | v2_struct_0(X1)
% 1.06/1.03      | ~ l1_pre_topc(X1)
% 1.06/1.03      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
% 1.06/1.03      inference(renaming,[status(thm)],[c_201]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_560,plain,
% 1.06/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.06/1.03      | v2_struct_0(X1)
% 1.06/1.03      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0))
% 1.06/1.03      | sK1 != X1 ),
% 1.06/1.03      inference(resolution_lifted,[status(thm)],[c_202,c_28]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_561,plain,
% 1.06/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.06/1.03      | v2_struct_0(sK1)
% 1.06/1.03      | k6_domain_1(u1_struct_0(sK1),X0) = u1_struct_0(k1_tex_2(sK1,X0)) ),
% 1.06/1.03      inference(unflattening,[status(thm)],[c_560]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_565,plain,
% 1.06/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.06/1.03      | k6_domain_1(u1_struct_0(sK1),X0) = u1_struct_0(k1_tex_2(sK1,X0)) ),
% 1.06/1.03      inference(global_propositional_subsumption,
% 1.06/1.03                [status(thm)],
% 1.06/1.03                [c_561,c_30]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_1238,plain,
% 1.06/1.03      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.06/1.03      | k6_domain_1(u1_struct_0(sK1),sK2) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 1.06/1.03      inference(instantiation,[status(thm)],[c_565]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(c_27,negated_conjecture,
% 1.06/1.03      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.06/1.03      inference(cnf_transformation,[],[f79]) ).
% 1.06/1.03  
% 1.06/1.03  cnf(contradiction,plain,
% 1.06/1.03      ( $false ),
% 1.06/1.03      inference(minisat,[status(thm)],[c_1241,c_1238,c_27]) ).
% 1.06/1.03  
% 1.06/1.03  
% 1.06/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.06/1.03  
% 1.06/1.03  ------                               Statistics
% 1.06/1.03  
% 1.06/1.03  ------ General
% 1.06/1.03  
% 1.06/1.03  abstr_ref_over_cycles:                  0
% 1.06/1.03  abstr_ref_under_cycles:                 0
% 1.06/1.03  gc_basic_clause_elim:                   0
% 1.06/1.03  forced_gc_time:                         0
% 1.06/1.03  parsing_time:                           0.01
% 1.06/1.03  unif_index_cands_time:                  0.
% 1.06/1.03  unif_index_add_time:                    0.
% 1.06/1.03  orderings_time:                         0.
% 1.06/1.03  out_proof_time:                         0.024
% 1.06/1.03  total_time:                             0.089
% 1.06/1.03  num_of_symbols:                         52
% 1.06/1.03  num_of_terms:                           684
% 1.06/1.03  
% 1.06/1.03  ------ Preprocessing
% 1.06/1.03  
% 1.06/1.03  num_of_splits:                          0
% 1.06/1.03  num_of_split_atoms:                     0
% 1.06/1.03  num_of_reused_defs:                     0
% 1.06/1.03  num_eq_ax_congr_red:                    16
% 1.06/1.03  num_of_sem_filtered_clauses:            1
% 1.06/1.03  num_of_subtypes:                        0
% 1.06/1.03  monotx_restored_types:                  0
% 1.06/1.03  sat_num_of_epr_types:                   0
% 1.06/1.03  sat_num_of_non_cyclic_types:            0
% 1.06/1.03  sat_guarded_non_collapsed_types:        0
% 1.06/1.03  num_pure_diseq_elim:                    0
% 1.06/1.03  simp_replaced_by:                       0
% 1.06/1.03  res_preprocessed:                       81
% 1.06/1.03  prep_upred:                             0
% 1.06/1.03  prep_unflattend:                        21
% 1.06/1.03  smt_new_axioms:                         0
% 1.06/1.03  pred_elim_cands:                        2
% 1.06/1.03  pred_elim:                              11
% 1.06/1.03  pred_elim_cl:                           16
% 1.06/1.03  pred_elim_cycles:                       16
% 1.06/1.03  merged_defs:                            0
% 1.06/1.03  merged_defs_ncl:                        0
% 1.06/1.03  bin_hyper_res:                          0
% 1.06/1.03  prep_cycles:                            4
% 1.06/1.03  pred_elim_time:                         0.012
% 1.06/1.03  splitting_time:                         0.
% 1.06/1.03  sem_filter_time:                        0.
% 1.06/1.03  monotx_time:                            0.
% 1.06/1.03  subtype_inf_time:                       0.
% 1.06/1.03  
% 1.06/1.03  ------ Problem properties
% 1.06/1.03  
% 1.06/1.03  clauses:                                12
% 1.06/1.03  conjectures:                            1
% 1.06/1.03  epr:                                    2
% 1.06/1.03  horn:                                   11
% 1.06/1.03  ground:                                 2
% 1.06/1.03  unary:                                  4
% 1.06/1.03  binary:                                 3
% 1.06/1.03  lits:                                   27
% 1.06/1.03  lits_eq:                                6
% 1.06/1.03  fd_pure:                                0
% 1.06/1.03  fd_pseudo:                              0
% 1.06/1.03  fd_cond:                                0
% 1.06/1.03  fd_pseudo_cond:                         0
% 1.06/1.03  ac_symbols:                             0
% 1.06/1.03  
% 1.06/1.03  ------ Propositional Solver
% 1.06/1.03  
% 1.06/1.03  prop_solver_calls:                      22
% 1.06/1.03  prop_fast_solver_calls:                 587
% 1.06/1.03  smt_solver_calls:                       0
% 1.06/1.03  smt_fast_solver_calls:                  0
% 1.06/1.03  prop_num_of_clauses:                    274
% 1.06/1.03  prop_preprocess_simplified:             2252
% 1.06/1.03  prop_fo_subsumed:                       23
% 1.06/1.03  prop_solver_time:                       0.
% 1.06/1.03  smt_solver_time:                        0.
% 1.06/1.03  smt_fast_solver_time:                   0.
% 1.06/1.03  prop_fast_solver_time:                  0.
% 1.06/1.03  prop_unsat_core_time:                   0.
% 1.06/1.03  
% 1.06/1.03  ------ QBF
% 1.06/1.03  
% 1.06/1.03  qbf_q_res:                              0
% 1.06/1.03  qbf_num_tautologies:                    0
% 1.06/1.03  qbf_prep_cycles:                        0
% 1.06/1.03  
% 1.06/1.03  ------ BMC1
% 1.06/1.03  
% 1.06/1.03  bmc1_current_bound:                     -1
% 1.06/1.03  bmc1_last_solved_bound:                 -1
% 1.06/1.03  bmc1_unsat_core_size:                   -1
% 1.06/1.03  bmc1_unsat_core_parents_size:           -1
% 1.06/1.03  bmc1_merge_next_fun:                    0
% 1.06/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.06/1.03  
% 1.06/1.03  ------ Instantiation
% 1.06/1.03  
% 1.06/1.03  inst_num_of_clauses:                    21
% 1.06/1.03  inst_num_in_passive:                    16
% 1.06/1.03  inst_num_in_active:                     3
% 1.06/1.03  inst_num_in_unprocessed:                1
% 1.06/1.03  inst_num_of_loops:                      4
% 1.06/1.03  inst_num_of_learning_restarts:          0
% 1.06/1.03  inst_num_moves_active_passive:          0
% 1.06/1.03  inst_lit_activity:                      0
% 1.06/1.03  inst_lit_activity_moves:                0
% 1.06/1.03  inst_num_tautologies:                   0
% 1.06/1.03  inst_num_prop_implied:                  0
% 1.06/1.03  inst_num_existing_simplified:           0
% 1.06/1.03  inst_num_eq_res_simplified:             0
% 1.06/1.03  inst_num_child_elim:                    0
% 1.06/1.03  inst_num_of_dismatching_blockings:      0
% 1.06/1.03  inst_num_of_non_proper_insts:           2
% 1.06/1.03  inst_num_of_duplicates:                 0
% 1.06/1.03  inst_inst_num_from_inst_to_res:         0
% 1.06/1.03  inst_dismatching_checking_time:         0.
% 1.06/1.03  
% 1.06/1.03  ------ Resolution
% 1.06/1.03  
% 1.06/1.03  res_num_of_clauses:                     0
% 1.06/1.03  res_num_in_passive:                     0
% 1.06/1.03  res_num_in_active:                      0
% 1.06/1.03  res_num_of_loops:                       85
% 1.06/1.03  res_forward_subset_subsumed:            0
% 1.06/1.03  res_backward_subset_subsumed:           0
% 1.06/1.03  res_forward_subsumed:                   0
% 1.06/1.03  res_backward_subsumed:                  0
% 1.06/1.03  res_forward_subsumption_resolution:     2
% 1.06/1.03  res_backward_subsumption_resolution:    1
% 1.06/1.03  res_clause_to_clause_subsumption:       42
% 1.06/1.03  res_orphan_elimination:                 0
% 1.06/1.03  res_tautology_del:                      4
% 1.06/1.03  res_num_eq_res_simplified:              0
% 1.06/1.03  res_num_sel_changes:                    0
% 1.06/1.03  res_moves_from_active_to_pass:          0
% 1.06/1.03  
% 1.06/1.03  ------ Superposition
% 1.06/1.03  
% 1.06/1.03  sup_time_total:                         0.
% 1.06/1.03  sup_time_generating:                    0.
% 1.06/1.03  sup_time_sim_full:                      0.
% 1.06/1.03  sup_time_sim_immed:                     0.
% 1.06/1.03  
% 1.06/1.03  sup_num_of_clauses:                     12
% 1.06/1.03  sup_num_in_active:                      0
% 1.06/1.03  sup_num_in_passive:                     12
% 1.06/1.03  sup_num_of_loops:                       0
% 1.06/1.03  sup_fw_superposition:                   0
% 1.06/1.03  sup_bw_superposition:                   0
% 1.06/1.03  sup_immediate_simplified:               0
% 1.06/1.03  sup_given_eliminated:                   0
% 1.06/1.03  comparisons_done:                       0
% 1.06/1.03  comparisons_avoided:                    0
% 1.06/1.03  
% 1.06/1.03  ------ Simplifications
% 1.06/1.03  
% 1.06/1.03  
% 1.06/1.03  sim_fw_subset_subsumed:                 0
% 1.06/1.03  sim_bw_subset_subsumed:                 0
% 1.06/1.03  sim_fw_subsumed:                        0
% 1.06/1.03  sim_bw_subsumed:                        0
% 1.06/1.03  sim_fw_subsumption_res:                 0
% 1.06/1.03  sim_bw_subsumption_res:                 0
% 1.06/1.03  sim_tautology_del:                      0
% 1.06/1.03  sim_eq_tautology_del:                   0
% 1.06/1.03  sim_eq_res_simp:                        0
% 1.06/1.03  sim_fw_demodulated:                     0
% 1.06/1.03  sim_bw_demodulated:                     0
% 1.06/1.03  sim_light_normalised:                   1
% 1.06/1.03  sim_joinable_taut:                      0
% 1.06/1.03  sim_joinable_simp:                      0
% 1.06/1.03  sim_ac_normalised:                      0
% 1.06/1.03  sim_smt_subsumption:                    0
% 1.06/1.03  
%------------------------------------------------------------------------------
