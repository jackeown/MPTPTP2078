%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2048+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:04 EST 2020

% Result     : Theorem 1.00s
% Output     : CNFRefutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 164 expanded)
%              Number of clauses        :   37 (  42 expanded)
%              Number of leaves         :    9 (  49 expanded)
%              Depth                    :   18
%              Number of atoms          :  309 ( 859 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1)
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,sK3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,sK3))),X0,X1)
        & m1_subset_1(sK3,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,sK2,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,sK2,X2))),X0,sK2)
            & m1_subset_1(X2,u1_struct_0(sK2)) )
        & l1_waybel_0(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1)
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,X1,X2)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,X1,X2))),sK1,X1)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,sK2,sK3))),sK1,sK2)
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_waybel_0(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f25,f24,f23])).

fof(f34,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_yellow19(X2,X0,X1)
              <=> ? [X3] :
                    ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                    & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow19(X2,X0,X1)
              <=> ? [X3] :
                    ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_yellow19(X2,X0,X1)
              <=> ? [X3] :
                    ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow19(X2,X0,X1)
                  | ! [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ? [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) = X2
                      & m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ m1_yellow19(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow19(X2,X0,X1)
                  | ! [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ? [X4] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X4)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X4))) = X2
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_yellow19(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X4)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X4))) = X2
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,sK0(X0,X1,X2))),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,sK0(X0,X1,X2)))) = X2
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_yellow19(X2,X0,X1)
                  | ! [X3] :
                      ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ( k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,sK0(X0,X1,X2))),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,sK0(X0,X1,X2)))) = X2
                    & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X1)) )
                  | ~ m1_yellow19(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_yellow19(X2,X0,X1)
      | k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))) != X2
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))),X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X3)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X3))),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f33,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f35,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f36,plain,(
    l1_waybel_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,sK2,sK3))),sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f37,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_774,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X0_45,X1_45)))
    | m1_subset_1(k2_relset_1(X0_45,X1_45,X0_43),k1_zfmisc_1(X1_45)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1219,plain,
    ( m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,sK2,X0_43)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,sK2,X0_43))),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_waybel_0(sK1,k4_waybel_9(sK1,sK2,X0_43)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK1,sK2,X0_43)),u1_struct_0(sK1)))) ),
    inference(instantiation,[status(thm)],[c_774])).

cnf(c_1221,plain,
    ( m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,sK2,sK3))),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_waybel_0(sK1,k4_waybel_9(sK1,sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK1)))) ),
    inference(instantiation,[status(thm)],[c_1219])).

cnf(c_5,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_10,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_160,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_10])).

cnf(c_161,plain,
    ( ~ l1_waybel_0(X0,sK1)
    | m1_subset_1(u1_waybel_0(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) ),
    inference(unflattening,[status(thm)],[c_160])).

cnf(c_770,plain,
    ( ~ l1_waybel_0(X0_44,sK1)
    | m1_subset_1(u1_waybel_0(sK1,X0_44),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_44),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_161])).

cnf(c_1160,plain,
    ( ~ l1_waybel_0(k4_waybel_9(sK1,sK2,X0_43),sK1)
    | m1_subset_1(u1_waybel_0(sK1,k4_waybel_9(sK1,sK2,X0_43)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK1,sK2,X0_43)),u1_struct_0(sK1)))) ),
    inference(instantiation,[status(thm)],[c_770])).

cnf(c_1162,plain,
    ( ~ l1_waybel_0(k4_waybel_9(sK1,sK2,sK3),sK1)
    | m1_subset_1(u1_waybel_0(sK1,k4_waybel_9(sK1,sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK1)))) ),
    inference(instantiation,[status(thm)],[c_1160])).

cnf(c_0,plain,
    ( m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_135,plain,
    ( m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),X0,X1)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X0),u1_waybel_0(X0,k4_waybel_9(X0,X1,X2))),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_136,plain,
    ( m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,X0,X1)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,X0,X1))),sK1,X0)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,X0,X1)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,X0,X1))),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(X0)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_135])).

cnf(c_11,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_140,plain,
    ( v2_struct_0(X0)
    | ~ m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,X0,X1)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,X0,X1))),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_waybel_0(X0,sK1)
    | m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,X0,X1)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,X0,X1))),sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_136,c_11])).

cnf(c_141,plain,
    ( m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,X0,X1)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,X0,X1))),sK1,X0)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,X0,X1)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,X0,X1))),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_140])).

cnf(c_9,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_364,plain,
    ( m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,X0,X1)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,X0,X1))),sK1,X0)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,X0,X1)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,X0,X1))),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_141,c_9])).

cnf(c_365,plain,
    ( m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,sK2,X0)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,sK2,X0))),sK1,sK2)
    | ~ l1_waybel_0(sK2,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,sK2,X0)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,sK2,X0))),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_8,negated_conjecture,
    ( l1_waybel_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_369,plain,
    ( m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,sK2,X0)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,sK2,X0))),sK1,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,sK2,X0)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,sK2,X0))),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_365,c_8])).

cnf(c_768,plain,
    ( m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,sK2,X0_43)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,sK2,X0_43))),sK1,sK2)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2))
    | ~ m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,sK2,X0_43)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,sK2,X0_43))),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_369])).

cnf(c_815,plain,
    ( m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,sK2,sK3))),sK1,sK2)
    | ~ m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,sK2,sK3))),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_768])).

cnf(c_4,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_waybel_0(k4_waybel_9(X1,X0,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_172,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_waybel_0(k4_waybel_9(X1,X0,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_10])).

cnf(c_173,plain,
    ( ~ l1_waybel_0(X0,sK1)
    | l1_waybel_0(k4_waybel_9(sK1,X0,X1),sK1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_172])).

cnf(c_177,plain,
    ( v2_struct_0(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | l1_waybel_0(k4_waybel_9(sK1,X0,X1),sK1)
    | ~ l1_waybel_0(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_173,c_11])).

cnf(c_178,plain,
    ( ~ l1_waybel_0(X0,sK1)
    | l1_waybel_0(k4_waybel_9(sK1,X0,X1),sK1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_177])).

cnf(c_346,plain,
    ( ~ l1_waybel_0(X0,sK1)
    | l1_waybel_0(k4_waybel_9(sK1,X0,X1),sK1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_178,c_9])).

cnf(c_347,plain,
    ( l1_waybel_0(k4_waybel_9(sK1,sK2,X0),sK1)
    | ~ l1_waybel_0(sK2,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_346])).

cnf(c_351,plain,
    ( l1_waybel_0(k4_waybel_9(sK1,sK2,X0),sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_347,c_8])).

cnf(c_769,plain,
    ( l1_waybel_0(k4_waybel_9(sK1,sK2,X0_43),sK1)
    | ~ m1_subset_1(X0_43,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_351])).

cnf(c_812,plain,
    ( l1_waybel_0(k4_waybel_9(sK1,sK2,sK3),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_769])).

cnf(c_6,negated_conjecture,
    ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(sK1,sK2,sK3)),u1_struct_0(sK1),u1_waybel_0(sK1,k4_waybel_9(sK1,sK2,sK3))),sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_7,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1221,c_1162,c_815,c_812,c_6,c_7])).


%------------------------------------------------------------------------------
