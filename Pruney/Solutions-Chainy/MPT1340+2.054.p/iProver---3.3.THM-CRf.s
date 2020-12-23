%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:32 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :  207 (5676 expanded)
%              Number of clauses        :  133 (1807 expanded)
%              Number of leaves         :   20 (1584 expanded)
%              Depth                    :   29
%              Number of atoms          :  733 (35597 expanded)
%              Number of equality atoms :  271 (5863 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2)
        & v2_funct_1(sK2)
        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1)
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2)
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_struct_0(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f43,f47,f46,f45])).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f68,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f75,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f77,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f53,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0] :
      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f57,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f55,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f79,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_635,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1098,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_635])).

cnf(c_19,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_30,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_352,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_353,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_631,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_353])).

cnf(c_28,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_347,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_348,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_347])).

cnf(c_632,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_348])).

cnf(c_1120,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1098,c_631,c_632])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_20,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_334,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_335,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_43,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_337,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_335,c_29,c_28,c_43])).

cnf(c_359,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_337])).

cnf(c_360,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_14,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_456,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_360,c_14])).

cnf(c_9,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_472,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_456,c_9])).

cnf(c_629,plain,
    ( ~ v1_funct_2(X0_52,X0_53,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_52)
    | ~ v1_relat_1(X0_52)
    | k1_relat_1(X0_52) = X0_53 ),
    inference(subtyping,[status(esa)],[c_472])).

cnf(c_1103,plain,
    ( k1_relat_1(X0_52) = X0_53
    | v1_funct_2(X0_52,X0_53,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_629])).

cnf(c_1190,plain,
    ( k1_relat_1(X0_52) = X0_53
    | v1_funct_2(X0_52,X0_53,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1103,c_632])).

cnf(c_1523,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1120,c_1190])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_634,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1099,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_634])).

cnf(c_1114,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1099,c_631,c_632])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_651,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
    | ~ v1_relat_1(X1_52)
    | v1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1342,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | v1_relat_1(X0_52)
    | ~ v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
    inference(instantiation,[status(thm)],[c_651])).

cnf(c_1451,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1342])).

cnf(c_1452,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1451])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_650,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1475,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_650])).

cnf(c_1476,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1475])).

cnf(c_2321,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1523,c_34,c_36,c_1114,c_1452,c_1476])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_642,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1092,plain,
    ( k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_1516,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1120,c_1092])).

cnf(c_24,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_636,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1117,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_636,c_631,c_632])).

cnf(c_1580,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1516,c_1117])).

cnf(c_1582,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1580,c_1516])).

cnf(c_2325,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2321,c_1582])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_641,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X1_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | m1_subset_1(k2_funct_1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | k2_relset_1(X0_53,X1_53,X0_52) != X1_53 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1093,plain,
    ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_641])).

cnf(c_3079,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2325,c_1093])).

cnf(c_633,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1100,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_647,plain,
    ( ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | ~ v1_relat_1(X0_52)
    | k2_funct_1(X0_52) = k4_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1087,plain,
    ( k2_funct_1(X0_52) = k4_relat_1(X0_52)
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_647])).

cnf(c_1742,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1100,c_1087])).

cnf(c_23,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_699,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_647])).

cnf(c_2054,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1742,c_27,c_25,c_23,c_699,c_1451,c_1475])).

cnf(c_3085,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3079,c_2054])).

cnf(c_37,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1584,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1580,c_1120])).

cnf(c_2324,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2321,c_1584])).

cnf(c_1585,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1580,c_1114])).

cnf(c_2326,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2321,c_1585])).

cnf(c_3567,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3085,c_34,c_37,c_2324,c_2326])).

cnf(c_3573,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3567,c_1092])).

cnf(c_1083,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(X1_52)) != iProver_top
    | v1_relat_1(X1_52) != iProver_top
    | v1_relat_1(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_651])).

cnf(c_1447,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1120,c_1083])).

cnf(c_1726,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1447,c_36,c_1452,c_1476])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_649,plain,
    ( ~ v1_relat_1(X0_52)
    | k2_relat_1(k4_relat_1(X0_52)) = k1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1085,plain,
    ( k2_relat_1(k4_relat_1(X0_52)) = k1_relat_1(X0_52)
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_649])).

cnf(c_1732,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1726,c_1085])).

cnf(c_3576,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3573,c_1732])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_638,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X1_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | k2_relset_1(X0_53,X1_53,X0_52) != X1_53
    | k2_tops_2(X0_53,X1_53,X0_52) = k2_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1096,plain,
    ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
    | k2_tops_2(X0_53,X1_53,X0_52) = k2_funct_1(X0_52)
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_638])).

cnf(c_3737,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_funct_1(k4_relat_1(sK2))
    | v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3576,c_1096])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_643,plain,
    ( ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | ~ v1_relat_1(X0_52)
    | k2_funct_1(k2_funct_1(X0_52)) = X0_52 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1091,plain,
    ( k2_funct_1(k2_funct_1(X0_52)) = X0_52
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_643])).

cnf(c_1927,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1100,c_1091])).

cnf(c_711,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_643])).

cnf(c_2088,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1927,c_27,c_25,c_23,c_711,c_1451,c_1475])).

cnf(c_2090,plain,
    ( k2_funct_1(k4_relat_1(sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2088,c_2054])).

cnf(c_3757,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = sK2
    | v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3737,c_2090])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_645,plain,
    ( ~ v1_funct_1(X0_52)
    | v1_funct_1(k2_funct_1(X0_52))
    | ~ v2_funct_1(X0_52)
    | ~ v1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1089,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k2_funct_1(X0_52)) = iProver_top
    | v2_funct_1(X0_52) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_645])).

cnf(c_2058,plain,
    ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2054,c_1089])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_646,plain,
    ( ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | v2_funct_1(k2_funct_1(X0_52))
    | ~ v1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1088,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top
    | v2_funct_1(k2_funct_1(X0_52)) = iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_646])).

cnf(c_2059,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2054,c_1088])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_640,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X1_53)
    | v1_funct_2(k2_funct_1(X0_52),X1_53,X0_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | k2_relset_1(X0_53,X1_53,X0_52) != X1_53 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1094,plain,
    ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | v1_funct_2(k2_funct_1(X0_52),X1_53,X0_53) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_640])).

cnf(c_3078,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2325,c_1094])).

cnf(c_3096,plain,
    ( v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3078,c_2054])).

cnf(c_3862,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3757,c_34,c_36,c_37,c_1452,c_1476,c_2058,c_2059,c_2324,c_2326,c_3085,c_3096])).

cnf(c_3077,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2325,c_1096])).

cnf(c_3107,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k4_relat_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3077,c_2054])).

cnf(c_3234,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3107,c_34,c_37,c_2324,c_2326])).

cnf(c_15,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_22,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_382,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_383,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_630,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_383])).

cnf(c_653,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sP0_iProver_split
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_630])).

cnf(c_1101,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_653])).

cnf(c_1249,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1101,c_631,c_632])).

cnf(c_652,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_52)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_630])).

cnf(c_1102,plain,
    ( v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_652])).

cnf(c_1181,plain,
    ( v1_funct_2(X0_52,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1102,c_631,c_632])).

cnf(c_1255,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1249,c_1181])).

cnf(c_2629,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1255,c_1580,c_2321])).

cnf(c_3237,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3234,c_2629])).

cnf(c_3865,plain,
    ( sK2 != sK2
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3862,c_3237])).

cnf(c_655,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_685,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_655])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3865,c_2326,c_2324,c_685,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:27:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.41/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.03  
% 2.41/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.41/1.03  
% 2.41/1.03  ------  iProver source info
% 2.41/1.03  
% 2.41/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.41/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.41/1.03  git: non_committed_changes: false
% 2.41/1.03  git: last_make_outside_of_git: false
% 2.41/1.03  
% 2.41/1.03  ------ 
% 2.41/1.03  
% 2.41/1.03  ------ Input Options
% 2.41/1.03  
% 2.41/1.03  --out_options                           all
% 2.41/1.03  --tptp_safe_out                         true
% 2.41/1.03  --problem_path                          ""
% 2.41/1.03  --include_path                          ""
% 2.41/1.03  --clausifier                            res/vclausify_rel
% 2.41/1.03  --clausifier_options                    --mode clausify
% 2.41/1.03  --stdin                                 false
% 2.41/1.03  --stats_out                             all
% 2.41/1.03  
% 2.41/1.03  ------ General Options
% 2.41/1.03  
% 2.41/1.03  --fof                                   false
% 2.41/1.03  --time_out_real                         305.
% 2.41/1.03  --time_out_virtual                      -1.
% 2.41/1.03  --symbol_type_check                     false
% 2.41/1.03  --clausify_out                          false
% 2.41/1.03  --sig_cnt_out                           false
% 2.41/1.03  --trig_cnt_out                          false
% 2.41/1.03  --trig_cnt_out_tolerance                1.
% 2.41/1.03  --trig_cnt_out_sk_spl                   false
% 2.41/1.03  --abstr_cl_out                          false
% 2.41/1.03  
% 2.41/1.03  ------ Global Options
% 2.41/1.03  
% 2.41/1.03  --schedule                              default
% 2.41/1.03  --add_important_lit                     false
% 2.41/1.03  --prop_solver_per_cl                    1000
% 2.41/1.03  --min_unsat_core                        false
% 2.41/1.03  --soft_assumptions                      false
% 2.41/1.03  --soft_lemma_size                       3
% 2.41/1.03  --prop_impl_unit_size                   0
% 2.41/1.03  --prop_impl_unit                        []
% 2.41/1.03  --share_sel_clauses                     true
% 2.41/1.03  --reset_solvers                         false
% 2.41/1.03  --bc_imp_inh                            [conj_cone]
% 2.41/1.03  --conj_cone_tolerance                   3.
% 2.41/1.03  --extra_neg_conj                        none
% 2.41/1.03  --large_theory_mode                     true
% 2.41/1.03  --prolific_symb_bound                   200
% 2.41/1.03  --lt_threshold                          2000
% 2.41/1.03  --clause_weak_htbl                      true
% 2.41/1.03  --gc_record_bc_elim                     false
% 2.41/1.03  
% 2.41/1.03  ------ Preprocessing Options
% 2.41/1.03  
% 2.41/1.03  --preprocessing_flag                    true
% 2.41/1.03  --time_out_prep_mult                    0.1
% 2.41/1.03  --splitting_mode                        input
% 2.41/1.03  --splitting_grd                         true
% 2.41/1.03  --splitting_cvd                         false
% 2.41/1.03  --splitting_cvd_svl                     false
% 2.41/1.03  --splitting_nvd                         32
% 2.41/1.03  --sub_typing                            true
% 2.41/1.03  --prep_gs_sim                           true
% 2.41/1.03  --prep_unflatten                        true
% 2.41/1.03  --prep_res_sim                          true
% 2.41/1.03  --prep_upred                            true
% 2.41/1.03  --prep_sem_filter                       exhaustive
% 2.41/1.03  --prep_sem_filter_out                   false
% 2.41/1.03  --pred_elim                             true
% 2.41/1.03  --res_sim_input                         true
% 2.41/1.03  --eq_ax_congr_red                       true
% 2.41/1.03  --pure_diseq_elim                       true
% 2.41/1.03  --brand_transform                       false
% 2.41/1.03  --non_eq_to_eq                          false
% 2.41/1.03  --prep_def_merge                        true
% 2.41/1.03  --prep_def_merge_prop_impl              false
% 2.41/1.03  --prep_def_merge_mbd                    true
% 2.41/1.03  --prep_def_merge_tr_red                 false
% 2.41/1.03  --prep_def_merge_tr_cl                  false
% 2.41/1.03  --smt_preprocessing                     true
% 2.41/1.03  --smt_ac_axioms                         fast
% 2.41/1.03  --preprocessed_out                      false
% 2.41/1.03  --preprocessed_stats                    false
% 2.41/1.03  
% 2.41/1.03  ------ Abstraction refinement Options
% 2.41/1.03  
% 2.41/1.03  --abstr_ref                             []
% 2.41/1.03  --abstr_ref_prep                        false
% 2.41/1.03  --abstr_ref_until_sat                   false
% 2.41/1.03  --abstr_ref_sig_restrict                funpre
% 2.41/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.41/1.03  --abstr_ref_under                       []
% 2.41/1.03  
% 2.41/1.03  ------ SAT Options
% 2.41/1.03  
% 2.41/1.03  --sat_mode                              false
% 2.41/1.03  --sat_fm_restart_options                ""
% 2.41/1.03  --sat_gr_def                            false
% 2.41/1.03  --sat_epr_types                         true
% 2.41/1.03  --sat_non_cyclic_types                  false
% 2.41/1.03  --sat_finite_models                     false
% 2.41/1.03  --sat_fm_lemmas                         false
% 2.41/1.03  --sat_fm_prep                           false
% 2.41/1.03  --sat_fm_uc_incr                        true
% 2.41/1.03  --sat_out_model                         small
% 2.41/1.03  --sat_out_clauses                       false
% 2.41/1.03  
% 2.41/1.03  ------ QBF Options
% 2.41/1.03  
% 2.41/1.03  --qbf_mode                              false
% 2.41/1.03  --qbf_elim_univ                         false
% 2.41/1.03  --qbf_dom_inst                          none
% 2.41/1.03  --qbf_dom_pre_inst                      false
% 2.41/1.03  --qbf_sk_in                             false
% 2.41/1.03  --qbf_pred_elim                         true
% 2.41/1.03  --qbf_split                             512
% 2.41/1.03  
% 2.41/1.03  ------ BMC1 Options
% 2.41/1.03  
% 2.41/1.03  --bmc1_incremental                      false
% 2.41/1.03  --bmc1_axioms                           reachable_all
% 2.41/1.03  --bmc1_min_bound                        0
% 2.41/1.03  --bmc1_max_bound                        -1
% 2.41/1.03  --bmc1_max_bound_default                -1
% 2.41/1.03  --bmc1_symbol_reachability              true
% 2.41/1.03  --bmc1_property_lemmas                  false
% 2.41/1.03  --bmc1_k_induction                      false
% 2.41/1.03  --bmc1_non_equiv_states                 false
% 2.41/1.03  --bmc1_deadlock                         false
% 2.41/1.03  --bmc1_ucm                              false
% 2.41/1.03  --bmc1_add_unsat_core                   none
% 2.41/1.03  --bmc1_unsat_core_children              false
% 2.41/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.41/1.03  --bmc1_out_stat                         full
% 2.41/1.03  --bmc1_ground_init                      false
% 2.41/1.03  --bmc1_pre_inst_next_state              false
% 2.41/1.03  --bmc1_pre_inst_state                   false
% 2.41/1.03  --bmc1_pre_inst_reach_state             false
% 2.41/1.03  --bmc1_out_unsat_core                   false
% 2.41/1.03  --bmc1_aig_witness_out                  false
% 2.41/1.03  --bmc1_verbose                          false
% 2.41/1.03  --bmc1_dump_clauses_tptp                false
% 2.41/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.41/1.03  --bmc1_dump_file                        -
% 2.41/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.41/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.41/1.03  --bmc1_ucm_extend_mode                  1
% 2.41/1.03  --bmc1_ucm_init_mode                    2
% 2.41/1.03  --bmc1_ucm_cone_mode                    none
% 2.41/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.41/1.03  --bmc1_ucm_relax_model                  4
% 2.41/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.41/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.41/1.03  --bmc1_ucm_layered_model                none
% 2.41/1.03  --bmc1_ucm_max_lemma_size               10
% 2.41/1.03  
% 2.41/1.03  ------ AIG Options
% 2.41/1.03  
% 2.41/1.03  --aig_mode                              false
% 2.41/1.03  
% 2.41/1.03  ------ Instantiation Options
% 2.41/1.03  
% 2.41/1.03  --instantiation_flag                    true
% 2.41/1.03  --inst_sos_flag                         false
% 2.41/1.03  --inst_sos_phase                        true
% 2.41/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.41/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.41/1.03  --inst_lit_sel_side                     num_symb
% 2.41/1.03  --inst_solver_per_active                1400
% 2.41/1.03  --inst_solver_calls_frac                1.
% 2.41/1.03  --inst_passive_queue_type               priority_queues
% 2.41/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.41/1.03  --inst_passive_queues_freq              [25;2]
% 2.41/1.03  --inst_dismatching                      true
% 2.41/1.03  --inst_eager_unprocessed_to_passive     true
% 2.41/1.03  --inst_prop_sim_given                   true
% 2.41/1.03  --inst_prop_sim_new                     false
% 2.41/1.03  --inst_subs_new                         false
% 2.41/1.03  --inst_eq_res_simp                      false
% 2.41/1.03  --inst_subs_given                       false
% 2.41/1.03  --inst_orphan_elimination               true
% 2.41/1.03  --inst_learning_loop_flag               true
% 2.41/1.03  --inst_learning_start                   3000
% 2.41/1.03  --inst_learning_factor                  2
% 2.41/1.03  --inst_start_prop_sim_after_learn       3
% 2.41/1.03  --inst_sel_renew                        solver
% 2.41/1.03  --inst_lit_activity_flag                true
% 2.41/1.03  --inst_restr_to_given                   false
% 2.41/1.03  --inst_activity_threshold               500
% 2.41/1.03  --inst_out_proof                        true
% 2.41/1.03  
% 2.41/1.03  ------ Resolution Options
% 2.41/1.03  
% 2.41/1.03  --resolution_flag                       true
% 2.41/1.03  --res_lit_sel                           adaptive
% 2.41/1.03  --res_lit_sel_side                      none
% 2.41/1.03  --res_ordering                          kbo
% 2.41/1.03  --res_to_prop_solver                    active
% 2.41/1.03  --res_prop_simpl_new                    false
% 2.41/1.03  --res_prop_simpl_given                  true
% 2.41/1.03  --res_passive_queue_type                priority_queues
% 2.41/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.41/1.03  --res_passive_queues_freq               [15;5]
% 2.41/1.03  --res_forward_subs                      full
% 2.41/1.03  --res_backward_subs                     full
% 2.41/1.03  --res_forward_subs_resolution           true
% 2.41/1.03  --res_backward_subs_resolution          true
% 2.41/1.03  --res_orphan_elimination                true
% 2.41/1.03  --res_time_limit                        2.
% 2.41/1.03  --res_out_proof                         true
% 2.41/1.03  
% 2.41/1.03  ------ Superposition Options
% 2.41/1.03  
% 2.41/1.03  --superposition_flag                    true
% 2.41/1.03  --sup_passive_queue_type                priority_queues
% 2.41/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.41/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.41/1.03  --demod_completeness_check              fast
% 2.41/1.03  --demod_use_ground                      true
% 2.41/1.03  --sup_to_prop_solver                    passive
% 2.41/1.03  --sup_prop_simpl_new                    true
% 2.41/1.03  --sup_prop_simpl_given                  true
% 2.41/1.03  --sup_fun_splitting                     false
% 2.41/1.03  --sup_smt_interval                      50000
% 2.41/1.03  
% 2.41/1.03  ------ Superposition Simplification Setup
% 2.41/1.03  
% 2.41/1.03  --sup_indices_passive                   []
% 2.41/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.41/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.03  --sup_full_bw                           [BwDemod]
% 2.41/1.03  --sup_immed_triv                        [TrivRules]
% 2.41/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.03  --sup_immed_bw_main                     []
% 2.41/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.41/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/1.03  
% 2.41/1.03  ------ Combination Options
% 2.41/1.03  
% 2.41/1.03  --comb_res_mult                         3
% 2.41/1.03  --comb_sup_mult                         2
% 2.41/1.03  --comb_inst_mult                        10
% 2.41/1.03  
% 2.41/1.03  ------ Debug Options
% 2.41/1.03  
% 2.41/1.03  --dbg_backtrace                         false
% 2.41/1.03  --dbg_dump_prop_clauses                 false
% 2.41/1.03  --dbg_dump_prop_clauses_file            -
% 2.41/1.03  --dbg_out_stat                          false
% 2.41/1.03  ------ Parsing...
% 2.41/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.41/1.03  
% 2.41/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.41/1.03  
% 2.41/1.03  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.41/1.03  
% 2.41/1.03  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.41/1.03  ------ Proving...
% 2.41/1.03  ------ Problem Properties 
% 2.41/1.03  
% 2.41/1.03  
% 2.41/1.03  clauses                                 24
% 2.41/1.03  conjectures                             5
% 2.41/1.03  EPR                                     2
% 2.41/1.03  Horn                                    24
% 2.41/1.03  unary                                   8
% 2.41/1.03  binary                                  3
% 2.41/1.03  lits                                    75
% 2.41/1.03  lits eq                                 15
% 2.41/1.03  fd_pure                                 0
% 2.41/1.03  fd_pseudo                               0
% 2.41/1.03  fd_cond                                 0
% 2.41/1.03  fd_pseudo_cond                          1
% 2.41/1.03  AC symbols                              0
% 2.41/1.03  
% 2.41/1.03  ------ Schedule dynamic 5 is on 
% 2.41/1.03  
% 2.41/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.41/1.03  
% 2.41/1.03  
% 2.41/1.03  ------ 
% 2.41/1.03  Current options:
% 2.41/1.03  ------ 
% 2.41/1.03  
% 2.41/1.03  ------ Input Options
% 2.41/1.03  
% 2.41/1.03  --out_options                           all
% 2.41/1.03  --tptp_safe_out                         true
% 2.41/1.03  --problem_path                          ""
% 2.41/1.03  --include_path                          ""
% 2.41/1.03  --clausifier                            res/vclausify_rel
% 2.41/1.03  --clausifier_options                    --mode clausify
% 2.41/1.03  --stdin                                 false
% 2.41/1.03  --stats_out                             all
% 2.41/1.03  
% 2.41/1.03  ------ General Options
% 2.41/1.03  
% 2.41/1.03  --fof                                   false
% 2.41/1.03  --time_out_real                         305.
% 2.41/1.03  --time_out_virtual                      -1.
% 2.41/1.03  --symbol_type_check                     false
% 2.41/1.03  --clausify_out                          false
% 2.41/1.03  --sig_cnt_out                           false
% 2.41/1.03  --trig_cnt_out                          false
% 2.41/1.03  --trig_cnt_out_tolerance                1.
% 2.41/1.03  --trig_cnt_out_sk_spl                   false
% 2.41/1.03  --abstr_cl_out                          false
% 2.41/1.03  
% 2.41/1.03  ------ Global Options
% 2.41/1.03  
% 2.41/1.03  --schedule                              default
% 2.41/1.03  --add_important_lit                     false
% 2.41/1.03  --prop_solver_per_cl                    1000
% 2.41/1.03  --min_unsat_core                        false
% 2.41/1.03  --soft_assumptions                      false
% 2.41/1.03  --soft_lemma_size                       3
% 2.41/1.03  --prop_impl_unit_size                   0
% 2.41/1.03  --prop_impl_unit                        []
% 2.41/1.03  --share_sel_clauses                     true
% 2.41/1.03  --reset_solvers                         false
% 2.41/1.03  --bc_imp_inh                            [conj_cone]
% 2.41/1.03  --conj_cone_tolerance                   3.
% 2.41/1.03  --extra_neg_conj                        none
% 2.41/1.03  --large_theory_mode                     true
% 2.41/1.03  --prolific_symb_bound                   200
% 2.41/1.03  --lt_threshold                          2000
% 2.41/1.03  --clause_weak_htbl                      true
% 2.41/1.03  --gc_record_bc_elim                     false
% 2.41/1.03  
% 2.41/1.03  ------ Preprocessing Options
% 2.41/1.03  
% 2.41/1.03  --preprocessing_flag                    true
% 2.41/1.03  --time_out_prep_mult                    0.1
% 2.41/1.03  --splitting_mode                        input
% 2.41/1.03  --splitting_grd                         true
% 2.41/1.03  --splitting_cvd                         false
% 2.41/1.03  --splitting_cvd_svl                     false
% 2.41/1.03  --splitting_nvd                         32
% 2.41/1.03  --sub_typing                            true
% 2.41/1.03  --prep_gs_sim                           true
% 2.41/1.03  --prep_unflatten                        true
% 2.41/1.03  --prep_res_sim                          true
% 2.41/1.03  --prep_upred                            true
% 2.41/1.03  --prep_sem_filter                       exhaustive
% 2.41/1.03  --prep_sem_filter_out                   false
% 2.41/1.03  --pred_elim                             true
% 2.41/1.03  --res_sim_input                         true
% 2.41/1.03  --eq_ax_congr_red                       true
% 2.41/1.03  --pure_diseq_elim                       true
% 2.41/1.03  --brand_transform                       false
% 2.41/1.03  --non_eq_to_eq                          false
% 2.41/1.03  --prep_def_merge                        true
% 2.41/1.03  --prep_def_merge_prop_impl              false
% 2.41/1.03  --prep_def_merge_mbd                    true
% 2.41/1.03  --prep_def_merge_tr_red                 false
% 2.41/1.03  --prep_def_merge_tr_cl                  false
% 2.41/1.03  --smt_preprocessing                     true
% 2.41/1.03  --smt_ac_axioms                         fast
% 2.41/1.03  --preprocessed_out                      false
% 2.41/1.03  --preprocessed_stats                    false
% 2.41/1.03  
% 2.41/1.03  ------ Abstraction refinement Options
% 2.41/1.03  
% 2.41/1.03  --abstr_ref                             []
% 2.41/1.03  --abstr_ref_prep                        false
% 2.41/1.03  --abstr_ref_until_sat                   false
% 2.41/1.03  --abstr_ref_sig_restrict                funpre
% 2.41/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.41/1.03  --abstr_ref_under                       []
% 2.41/1.03  
% 2.41/1.03  ------ SAT Options
% 2.41/1.03  
% 2.41/1.03  --sat_mode                              false
% 2.41/1.03  --sat_fm_restart_options                ""
% 2.41/1.03  --sat_gr_def                            false
% 2.41/1.03  --sat_epr_types                         true
% 2.41/1.03  --sat_non_cyclic_types                  false
% 2.41/1.03  --sat_finite_models                     false
% 2.41/1.03  --sat_fm_lemmas                         false
% 2.41/1.03  --sat_fm_prep                           false
% 2.41/1.03  --sat_fm_uc_incr                        true
% 2.41/1.03  --sat_out_model                         small
% 2.41/1.03  --sat_out_clauses                       false
% 2.41/1.03  
% 2.41/1.03  ------ QBF Options
% 2.41/1.03  
% 2.41/1.03  --qbf_mode                              false
% 2.41/1.03  --qbf_elim_univ                         false
% 2.41/1.03  --qbf_dom_inst                          none
% 2.41/1.03  --qbf_dom_pre_inst                      false
% 2.41/1.03  --qbf_sk_in                             false
% 2.41/1.03  --qbf_pred_elim                         true
% 2.41/1.03  --qbf_split                             512
% 2.41/1.03  
% 2.41/1.03  ------ BMC1 Options
% 2.41/1.03  
% 2.41/1.03  --bmc1_incremental                      false
% 2.41/1.03  --bmc1_axioms                           reachable_all
% 2.41/1.03  --bmc1_min_bound                        0
% 2.41/1.03  --bmc1_max_bound                        -1
% 2.41/1.03  --bmc1_max_bound_default                -1
% 2.41/1.03  --bmc1_symbol_reachability              true
% 2.41/1.03  --bmc1_property_lemmas                  false
% 2.41/1.03  --bmc1_k_induction                      false
% 2.41/1.03  --bmc1_non_equiv_states                 false
% 2.41/1.03  --bmc1_deadlock                         false
% 2.41/1.03  --bmc1_ucm                              false
% 2.41/1.03  --bmc1_add_unsat_core                   none
% 2.41/1.03  --bmc1_unsat_core_children              false
% 2.41/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.41/1.03  --bmc1_out_stat                         full
% 2.41/1.03  --bmc1_ground_init                      false
% 2.41/1.03  --bmc1_pre_inst_next_state              false
% 2.41/1.03  --bmc1_pre_inst_state                   false
% 2.41/1.03  --bmc1_pre_inst_reach_state             false
% 2.41/1.03  --bmc1_out_unsat_core                   false
% 2.41/1.03  --bmc1_aig_witness_out                  false
% 2.41/1.03  --bmc1_verbose                          false
% 2.41/1.03  --bmc1_dump_clauses_tptp                false
% 2.41/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.41/1.03  --bmc1_dump_file                        -
% 2.41/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.41/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.41/1.03  --bmc1_ucm_extend_mode                  1
% 2.41/1.03  --bmc1_ucm_init_mode                    2
% 2.41/1.03  --bmc1_ucm_cone_mode                    none
% 2.41/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.41/1.03  --bmc1_ucm_relax_model                  4
% 2.41/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.41/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.41/1.03  --bmc1_ucm_layered_model                none
% 2.41/1.03  --bmc1_ucm_max_lemma_size               10
% 2.41/1.03  
% 2.41/1.03  ------ AIG Options
% 2.41/1.03  
% 2.41/1.03  --aig_mode                              false
% 2.41/1.03  
% 2.41/1.03  ------ Instantiation Options
% 2.41/1.03  
% 2.41/1.03  --instantiation_flag                    true
% 2.41/1.03  --inst_sos_flag                         false
% 2.41/1.03  --inst_sos_phase                        true
% 2.41/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.41/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.41/1.03  --inst_lit_sel_side                     none
% 2.41/1.03  --inst_solver_per_active                1400
% 2.41/1.03  --inst_solver_calls_frac                1.
% 2.41/1.03  --inst_passive_queue_type               priority_queues
% 2.41/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.41/1.03  --inst_passive_queues_freq              [25;2]
% 2.41/1.03  --inst_dismatching                      true
% 2.41/1.03  --inst_eager_unprocessed_to_passive     true
% 2.41/1.03  --inst_prop_sim_given                   true
% 2.41/1.03  --inst_prop_sim_new                     false
% 2.41/1.03  --inst_subs_new                         false
% 2.41/1.03  --inst_eq_res_simp                      false
% 2.41/1.03  --inst_subs_given                       false
% 2.41/1.03  --inst_orphan_elimination               true
% 2.41/1.03  --inst_learning_loop_flag               true
% 2.41/1.03  --inst_learning_start                   3000
% 2.41/1.03  --inst_learning_factor                  2
% 2.41/1.03  --inst_start_prop_sim_after_learn       3
% 2.41/1.03  --inst_sel_renew                        solver
% 2.41/1.03  --inst_lit_activity_flag                true
% 2.41/1.03  --inst_restr_to_given                   false
% 2.41/1.03  --inst_activity_threshold               500
% 2.41/1.03  --inst_out_proof                        true
% 2.41/1.03  
% 2.41/1.03  ------ Resolution Options
% 2.41/1.03  
% 2.41/1.03  --resolution_flag                       false
% 2.41/1.03  --res_lit_sel                           adaptive
% 2.41/1.03  --res_lit_sel_side                      none
% 2.41/1.03  --res_ordering                          kbo
% 2.41/1.03  --res_to_prop_solver                    active
% 2.41/1.03  --res_prop_simpl_new                    false
% 2.41/1.03  --res_prop_simpl_given                  true
% 2.41/1.03  --res_passive_queue_type                priority_queues
% 2.41/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.41/1.03  --res_passive_queues_freq               [15;5]
% 2.41/1.03  --res_forward_subs                      full
% 2.41/1.03  --res_backward_subs                     full
% 2.41/1.03  --res_forward_subs_resolution           true
% 2.41/1.03  --res_backward_subs_resolution          true
% 2.41/1.03  --res_orphan_elimination                true
% 2.41/1.03  --res_time_limit                        2.
% 2.41/1.03  --res_out_proof                         true
% 2.41/1.03  
% 2.41/1.03  ------ Superposition Options
% 2.41/1.03  
% 2.41/1.03  --superposition_flag                    true
% 2.41/1.03  --sup_passive_queue_type                priority_queues
% 2.41/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.41/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.41/1.03  --demod_completeness_check              fast
% 2.41/1.03  --demod_use_ground                      true
% 2.41/1.03  --sup_to_prop_solver                    passive
% 2.41/1.03  --sup_prop_simpl_new                    true
% 2.41/1.03  --sup_prop_simpl_given                  true
% 2.41/1.03  --sup_fun_splitting                     false
% 2.41/1.03  --sup_smt_interval                      50000
% 2.41/1.03  
% 2.41/1.03  ------ Superposition Simplification Setup
% 2.41/1.03  
% 2.41/1.03  --sup_indices_passive                   []
% 2.41/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.41/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.03  --sup_full_bw                           [BwDemod]
% 2.41/1.03  --sup_immed_triv                        [TrivRules]
% 2.41/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.03  --sup_immed_bw_main                     []
% 2.41/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.41/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/1.03  
% 2.41/1.03  ------ Combination Options
% 2.41/1.03  
% 2.41/1.03  --comb_res_mult                         3
% 2.41/1.03  --comb_sup_mult                         2
% 2.41/1.03  --comb_inst_mult                        10
% 2.41/1.03  
% 2.41/1.03  ------ Debug Options
% 2.41/1.03  
% 2.41/1.03  --dbg_backtrace                         false
% 2.41/1.03  --dbg_dump_prop_clauses                 false
% 2.41/1.03  --dbg_dump_prop_clauses_file            -
% 2.41/1.03  --dbg_out_stat                          false
% 2.41/1.03  
% 2.41/1.03  
% 2.41/1.03  
% 2.41/1.03  
% 2.41/1.03  ------ Proving...
% 2.41/1.03  
% 2.41/1.03  
% 2.41/1.03  % SZS status Theorem for theBenchmark.p
% 2.41/1.03  
% 2.41/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.41/1.03  
% 2.41/1.03  fof(f16,conjecture,(
% 2.41/1.03    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.41/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.03  
% 2.41/1.03  fof(f17,negated_conjecture,(
% 2.41/1.03    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.41/1.03    inference(negated_conjecture,[],[f16])).
% 2.41/1.03  
% 2.41/1.03  fof(f42,plain,(
% 2.41/1.03    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.41/1.03    inference(ennf_transformation,[],[f17])).
% 2.41/1.03  
% 2.41/1.03  fof(f43,plain,(
% 2.41/1.03    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.41/1.03    inference(flattening,[],[f42])).
% 2.41/1.03  
% 2.41/1.03  fof(f47,plain,(
% 2.41/1.03    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.41/1.03    introduced(choice_axiom,[])).
% 2.41/1.03  
% 2.41/1.03  fof(f46,plain,(
% 2.41/1.03    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.41/1.03    introduced(choice_axiom,[])).
% 2.41/1.03  
% 2.41/1.03  fof(f45,plain,(
% 2.41/1.03    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.41/1.03    introduced(choice_axiom,[])).
% 2.41/1.03  
% 2.41/1.03  fof(f48,plain,(
% 2.41/1.03    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.41/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f43,f47,f46,f45])).
% 2.41/1.03  
% 2.41/1.03  fof(f76,plain,(
% 2.41/1.03    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.41/1.03    inference(cnf_transformation,[],[f48])).
% 2.41/1.03  
% 2.41/1.03  fof(f13,axiom,(
% 2.41/1.03    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.41/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.03  
% 2.41/1.03  fof(f37,plain,(
% 2.41/1.03    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.41/1.03    inference(ennf_transformation,[],[f13])).
% 2.41/1.03  
% 2.41/1.03  fof(f68,plain,(
% 2.41/1.03    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.41/1.03    inference(cnf_transformation,[],[f37])).
% 2.41/1.03  
% 2.41/1.03  fof(f71,plain,(
% 2.41/1.03    l1_struct_0(sK0)),
% 2.41/1.03    inference(cnf_transformation,[],[f48])).
% 2.41/1.03  
% 2.41/1.03  fof(f73,plain,(
% 2.41/1.03    l1_struct_0(sK1)),
% 2.41/1.03    inference(cnf_transformation,[],[f48])).
% 2.41/1.03  
% 2.41/1.03  fof(f9,axiom,(
% 2.41/1.03    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.41/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.03  
% 2.41/1.03  fof(f29,plain,(
% 2.41/1.03    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.41/1.03    inference(ennf_transformation,[],[f9])).
% 2.41/1.03  
% 2.41/1.03  fof(f30,plain,(
% 2.41/1.03    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.41/1.03    inference(flattening,[],[f29])).
% 2.41/1.03  
% 2.41/1.03  fof(f61,plain,(
% 2.41/1.03    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.41/1.03    inference(cnf_transformation,[],[f30])).
% 2.41/1.03  
% 2.41/1.03  fof(f14,axiom,(
% 2.41/1.03    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.41/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.03  
% 2.41/1.03  fof(f38,plain,(
% 2.41/1.03    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.41/1.03    inference(ennf_transformation,[],[f14])).
% 2.41/1.03  
% 2.41/1.03  fof(f39,plain,(
% 2.41/1.03    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.41/1.03    inference(flattening,[],[f38])).
% 2.41/1.03  
% 2.41/1.03  fof(f69,plain,(
% 2.41/1.03    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.41/1.03    inference(cnf_transformation,[],[f39])).
% 2.41/1.03  
% 2.41/1.03  fof(f72,plain,(
% 2.41/1.03    ~v2_struct_0(sK1)),
% 2.41/1.03    inference(cnf_transformation,[],[f48])).
% 2.41/1.03  
% 2.41/1.03  fof(f10,axiom,(
% 2.41/1.03    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.41/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.03  
% 2.41/1.03  fof(f31,plain,(
% 2.41/1.03    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.41/1.03    inference(ennf_transformation,[],[f10])).
% 2.41/1.03  
% 2.41/1.03  fof(f32,plain,(
% 2.41/1.03    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.41/1.03    inference(flattening,[],[f31])).
% 2.41/1.03  
% 2.41/1.03  fof(f44,plain,(
% 2.41/1.03    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.41/1.03    inference(nnf_transformation,[],[f32])).
% 2.41/1.03  
% 2.41/1.03  fof(f62,plain,(
% 2.41/1.03    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.41/1.03    inference(cnf_transformation,[],[f44])).
% 2.41/1.03  
% 2.41/1.03  fof(f7,axiom,(
% 2.41/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.41/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.03  
% 2.41/1.03  fof(f18,plain,(
% 2.41/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.41/1.03    inference(pure_predicate_removal,[],[f7])).
% 2.41/1.03  
% 2.41/1.03  fof(f27,plain,(
% 2.41/1.03    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.41/1.03    inference(ennf_transformation,[],[f18])).
% 2.41/1.03  
% 2.41/1.03  fof(f58,plain,(
% 2.41/1.03    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.41/1.03    inference(cnf_transformation,[],[f27])).
% 2.41/1.03  
% 2.41/1.03  fof(f74,plain,(
% 2.41/1.03    v1_funct_1(sK2)),
% 2.41/1.03    inference(cnf_transformation,[],[f48])).
% 2.41/1.03  
% 2.41/1.03  fof(f75,plain,(
% 2.41/1.03    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.41/1.03    inference(cnf_transformation,[],[f48])).
% 2.41/1.03  
% 2.41/1.03  fof(f1,axiom,(
% 2.41/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.41/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.03  
% 2.41/1.03  fof(f19,plain,(
% 2.41/1.03    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.41/1.03    inference(ennf_transformation,[],[f1])).
% 2.41/1.03  
% 2.41/1.03  fof(f49,plain,(
% 2.41/1.03    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.41/1.03    inference(cnf_transformation,[],[f19])).
% 2.41/1.03  
% 2.41/1.03  fof(f2,axiom,(
% 2.41/1.03    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.41/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.03  
% 2.41/1.03  fof(f50,plain,(
% 2.41/1.03    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.41/1.03    inference(cnf_transformation,[],[f2])).
% 2.41/1.03  
% 2.41/1.03  fof(f8,axiom,(
% 2.41/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.41/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.03  
% 2.41/1.03  fof(f28,plain,(
% 2.41/1.03    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.41/1.03    inference(ennf_transformation,[],[f8])).
% 2.41/1.03  
% 2.41/1.03  fof(f59,plain,(
% 2.41/1.03    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.41/1.03    inference(cnf_transformation,[],[f28])).
% 2.41/1.03  
% 2.41/1.03  fof(f77,plain,(
% 2.41/1.03    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.41/1.03    inference(cnf_transformation,[],[f48])).
% 2.41/1.03  
% 2.41/1.03  fof(f12,axiom,(
% 2.41/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.41/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.03  
% 2.41/1.03  fof(f35,plain,(
% 2.41/1.03    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.41/1.03    inference(ennf_transformation,[],[f12])).
% 2.41/1.03  
% 2.41/1.03  fof(f36,plain,(
% 2.41/1.03    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.41/1.03    inference(flattening,[],[f35])).
% 2.41/1.03  
% 2.41/1.03  fof(f67,plain,(
% 2.41/1.03    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.41/1.03    inference(cnf_transformation,[],[f36])).
% 2.41/1.03  
% 2.41/1.03  fof(f4,axiom,(
% 2.41/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.41/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.03  
% 2.41/1.03  fof(f21,plain,(
% 2.41/1.03    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.41/1.03    inference(ennf_transformation,[],[f4])).
% 2.41/1.03  
% 2.41/1.03  fof(f22,plain,(
% 2.41/1.03    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.41/1.03    inference(flattening,[],[f21])).
% 2.41/1.03  
% 2.41/1.03  fof(f53,plain,(
% 2.41/1.03    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.41/1.03    inference(cnf_transformation,[],[f22])).
% 2.41/1.03  
% 2.41/1.03  fof(f78,plain,(
% 2.41/1.03    v2_funct_1(sK2)),
% 2.41/1.03    inference(cnf_transformation,[],[f48])).
% 2.41/1.03  
% 2.41/1.03  fof(f3,axiom,(
% 2.41/1.03    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 2.41/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.03  
% 2.41/1.03  fof(f20,plain,(
% 2.41/1.03    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.41/1.03    inference(ennf_transformation,[],[f3])).
% 2.41/1.03  
% 2.41/1.03  fof(f52,plain,(
% 2.41/1.03    ( ! [X0] : (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.41/1.03    inference(cnf_transformation,[],[f20])).
% 2.41/1.03  
% 2.41/1.03  fof(f15,axiom,(
% 2.41/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.41/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.03  
% 2.41/1.03  fof(f40,plain,(
% 2.41/1.03    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.41/1.03    inference(ennf_transformation,[],[f15])).
% 2.41/1.03  
% 2.41/1.03  fof(f41,plain,(
% 2.41/1.03    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.41/1.03    inference(flattening,[],[f40])).
% 2.41/1.03  
% 2.41/1.03  fof(f70,plain,(
% 2.41/1.03    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.41/1.03    inference(cnf_transformation,[],[f41])).
% 2.41/1.03  
% 2.41/1.03  fof(f6,axiom,(
% 2.41/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.41/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.03  
% 2.41/1.03  fof(f25,plain,(
% 2.41/1.03    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.41/1.03    inference(ennf_transformation,[],[f6])).
% 2.41/1.03  
% 2.41/1.03  fof(f26,plain,(
% 2.41/1.03    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.41/1.03    inference(flattening,[],[f25])).
% 2.41/1.03  
% 2.41/1.03  fof(f57,plain,(
% 2.41/1.03    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.41/1.03    inference(cnf_transformation,[],[f26])).
% 2.41/1.03  
% 2.41/1.03  fof(f5,axiom,(
% 2.41/1.03    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.41/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.03  
% 2.41/1.03  fof(f23,plain,(
% 2.41/1.03    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.41/1.03    inference(ennf_transformation,[],[f5])).
% 2.41/1.03  
% 2.41/1.03  fof(f24,plain,(
% 2.41/1.03    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.41/1.03    inference(flattening,[],[f23])).
% 2.41/1.03  
% 2.41/1.03  fof(f55,plain,(
% 2.41/1.03    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.41/1.03    inference(cnf_transformation,[],[f24])).
% 2.41/1.03  
% 2.41/1.03  fof(f56,plain,(
% 2.41/1.03    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.41/1.03    inference(cnf_transformation,[],[f24])).
% 2.41/1.03  
% 2.41/1.03  fof(f66,plain,(
% 2.41/1.03    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.41/1.03    inference(cnf_transformation,[],[f36])).
% 2.41/1.03  
% 2.41/1.03  fof(f11,axiom,(
% 2.41/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 2.41/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.03  
% 2.41/1.03  fof(f33,plain,(
% 2.41/1.03    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.41/1.03    inference(ennf_transformation,[],[f11])).
% 2.41/1.03  
% 2.41/1.03  fof(f34,plain,(
% 2.41/1.03    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.41/1.03    inference(flattening,[],[f33])).
% 2.41/1.03  
% 2.41/1.03  fof(f64,plain,(
% 2.41/1.03    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.41/1.03    inference(cnf_transformation,[],[f34])).
% 2.41/1.03  
% 2.41/1.03  fof(f79,plain,(
% 2.41/1.03    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 2.41/1.03    inference(cnf_transformation,[],[f48])).
% 2.41/1.03  
% 2.41/1.03  cnf(c_25,negated_conjecture,
% 2.41/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.41/1.03      inference(cnf_transformation,[],[f76]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_635,negated_conjecture,
% 2.41/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.41/1.03      inference(subtyping,[status(esa)],[c_25]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1098,plain,
% 2.41/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_635]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_19,plain,
% 2.41/1.03      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.41/1.03      inference(cnf_transformation,[],[f68]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_30,negated_conjecture,
% 2.41/1.03      ( l1_struct_0(sK0) ),
% 2.41/1.03      inference(cnf_transformation,[],[f71]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_352,plain,
% 2.41/1.03      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.41/1.03      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_353,plain,
% 2.41/1.03      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.41/1.03      inference(unflattening,[status(thm)],[c_352]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_631,plain,
% 2.41/1.03      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.41/1.03      inference(subtyping,[status(esa)],[c_353]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_28,negated_conjecture,
% 2.41/1.03      ( l1_struct_0(sK1) ),
% 2.41/1.03      inference(cnf_transformation,[],[f73]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_347,plain,
% 2.41/1.03      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.41/1.03      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_348,plain,
% 2.41/1.03      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.41/1.03      inference(unflattening,[status(thm)],[c_347]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_632,plain,
% 2.41/1.03      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.41/1.03      inference(subtyping,[status(esa)],[c_348]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1120,plain,
% 2.41/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.41/1.03      inference(light_normalisation,[status(thm)],[c_1098,c_631,c_632]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_11,plain,
% 2.41/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.41/1.03      | v1_partfun1(X0,X1)
% 2.41/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.03      | v1_xboole_0(X2)
% 2.41/1.03      | ~ v1_funct_1(X0) ),
% 2.41/1.03      inference(cnf_transformation,[],[f61]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_20,plain,
% 2.41/1.03      ( v2_struct_0(X0)
% 2.41/1.03      | ~ l1_struct_0(X0)
% 2.41/1.03      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.41/1.03      inference(cnf_transformation,[],[f69]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_29,negated_conjecture,
% 2.41/1.03      ( ~ v2_struct_0(sK1) ),
% 2.41/1.03      inference(cnf_transformation,[],[f72]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_334,plain,
% 2.41/1.03      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 2.41/1.03      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_335,plain,
% 2.41/1.03      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.41/1.03      inference(unflattening,[status(thm)],[c_334]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_43,plain,
% 2.41/1.03      ( v2_struct_0(sK1)
% 2.41/1.03      | ~ l1_struct_0(sK1)
% 2.41/1.03      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.41/1.03      inference(instantiation,[status(thm)],[c_20]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_337,plain,
% 2.41/1.03      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.41/1.03      inference(global_propositional_subsumption,
% 2.41/1.03                [status(thm)],
% 2.41/1.03                [c_335,c_29,c_28,c_43]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_359,plain,
% 2.41/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.41/1.03      | v1_partfun1(X0,X1)
% 2.41/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.03      | ~ v1_funct_1(X0)
% 2.41/1.03      | u1_struct_0(sK1) != X2 ),
% 2.41/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_337]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_360,plain,
% 2.41/1.03      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.41/1.03      | v1_partfun1(X0,X1)
% 2.41/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.41/1.03      | ~ v1_funct_1(X0) ),
% 2.41/1.03      inference(unflattening,[status(thm)],[c_359]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_14,plain,
% 2.41/1.03      ( ~ v1_partfun1(X0,X1)
% 2.41/1.03      | ~ v4_relat_1(X0,X1)
% 2.41/1.03      | ~ v1_relat_1(X0)
% 2.41/1.03      | k1_relat_1(X0) = X1 ),
% 2.41/1.03      inference(cnf_transformation,[],[f62]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_456,plain,
% 2.41/1.03      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.41/1.03      | ~ v4_relat_1(X0,X1)
% 2.41/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.41/1.03      | ~ v1_funct_1(X0)
% 2.41/1.03      | ~ v1_relat_1(X0)
% 2.41/1.03      | k1_relat_1(X0) = X1 ),
% 2.41/1.03      inference(resolution,[status(thm)],[c_360,c_14]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_9,plain,
% 2.41/1.03      ( v4_relat_1(X0,X1)
% 2.41/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.41/1.03      inference(cnf_transformation,[],[f58]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_472,plain,
% 2.41/1.03      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.41/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.41/1.03      | ~ v1_funct_1(X0)
% 2.41/1.03      | ~ v1_relat_1(X0)
% 2.41/1.03      | k1_relat_1(X0) = X1 ),
% 2.41/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_456,c_9]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_629,plain,
% 2.41/1.03      ( ~ v1_funct_2(X0_52,X0_53,u1_struct_0(sK1))
% 2.41/1.03      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,u1_struct_0(sK1))))
% 2.41/1.03      | ~ v1_funct_1(X0_52)
% 2.41/1.03      | ~ v1_relat_1(X0_52)
% 2.41/1.03      | k1_relat_1(X0_52) = X0_53 ),
% 2.41/1.03      inference(subtyping,[status(esa)],[c_472]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1103,plain,
% 2.41/1.03      ( k1_relat_1(X0_52) = X0_53
% 2.41/1.03      | v1_funct_2(X0_52,X0_53,u1_struct_0(sK1)) != iProver_top
% 2.41/1.03      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,u1_struct_0(sK1)))) != iProver_top
% 2.41/1.03      | v1_funct_1(X0_52) != iProver_top
% 2.41/1.03      | v1_relat_1(X0_52) != iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_629]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1190,plain,
% 2.41/1.03      ( k1_relat_1(X0_52) = X0_53
% 2.41/1.03      | v1_funct_2(X0_52,X0_53,k2_struct_0(sK1)) != iProver_top
% 2.41/1.03      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,k2_struct_0(sK1)))) != iProver_top
% 2.41/1.03      | v1_funct_1(X0_52) != iProver_top
% 2.41/1.03      | v1_relat_1(X0_52) != iProver_top ),
% 2.41/1.03      inference(light_normalisation,[status(thm)],[c_1103,c_632]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1523,plain,
% 2.41/1.03      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.41/1.03      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.41/1.03      | v1_funct_1(sK2) != iProver_top
% 2.41/1.03      | v1_relat_1(sK2) != iProver_top ),
% 2.41/1.03      inference(superposition,[status(thm)],[c_1120,c_1190]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_27,negated_conjecture,
% 2.41/1.03      ( v1_funct_1(sK2) ),
% 2.41/1.03      inference(cnf_transformation,[],[f74]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_34,plain,
% 2.41/1.03      ( v1_funct_1(sK2) = iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_36,plain,
% 2.41/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_26,negated_conjecture,
% 2.41/1.03      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.41/1.03      inference(cnf_transformation,[],[f75]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_634,negated_conjecture,
% 2.41/1.03      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.41/1.03      inference(subtyping,[status(esa)],[c_26]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1099,plain,
% 2.41/1.03      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_634]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1114,plain,
% 2.41/1.03      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.41/1.03      inference(light_normalisation,[status(thm)],[c_1099,c_631,c_632]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_0,plain,
% 2.41/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.41/1.03      | ~ v1_relat_1(X1)
% 2.41/1.03      | v1_relat_1(X0) ),
% 2.41/1.03      inference(cnf_transformation,[],[f49]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_651,plain,
% 2.41/1.03      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
% 2.41/1.03      | ~ v1_relat_1(X1_52)
% 2.41/1.03      | v1_relat_1(X0_52) ),
% 2.41/1.03      inference(subtyping,[status(esa)],[c_0]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1342,plain,
% 2.41/1.03      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.41/1.03      | v1_relat_1(X0_52)
% 2.41/1.03      | ~ v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
% 2.41/1.03      inference(instantiation,[status(thm)],[c_651]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1451,plain,
% 2.41/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.41/1.03      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.41/1.03      | v1_relat_1(sK2) ),
% 2.41/1.03      inference(instantiation,[status(thm)],[c_1342]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1452,plain,
% 2.41/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.41/1.03      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.41/1.03      | v1_relat_1(sK2) = iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_1451]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1,plain,
% 2.41/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.41/1.03      inference(cnf_transformation,[],[f50]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_650,plain,
% 2.41/1.03      ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
% 2.41/1.03      inference(subtyping,[status(esa)],[c_1]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1475,plain,
% 2.41/1.03      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.41/1.03      inference(instantiation,[status(thm)],[c_650]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1476,plain,
% 2.41/1.03      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_1475]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_2321,plain,
% 2.41/1.03      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.41/1.03      inference(global_propositional_subsumption,
% 2.41/1.03                [status(thm)],
% 2.41/1.03                [c_1523,c_34,c_36,c_1114,c_1452,c_1476]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_10,plain,
% 2.41/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.41/1.03      inference(cnf_transformation,[],[f59]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_642,plain,
% 2.41/1.03      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.41/1.03      | k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52) ),
% 2.41/1.03      inference(subtyping,[status(esa)],[c_10]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1092,plain,
% 2.41/1.03      ( k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52)
% 2.41/1.03      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1516,plain,
% 2.41/1.03      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.41/1.03      inference(superposition,[status(thm)],[c_1120,c_1092]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_24,negated_conjecture,
% 2.41/1.03      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.41/1.03      inference(cnf_transformation,[],[f77]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_636,negated_conjecture,
% 2.41/1.03      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.41/1.03      inference(subtyping,[status(esa)],[c_24]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1117,plain,
% 2.41/1.03      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.41/1.03      inference(light_normalisation,[status(thm)],[c_636,c_631,c_632]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1580,plain,
% 2.41/1.03      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.41/1.03      inference(demodulation,[status(thm)],[c_1516,c_1117]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1582,plain,
% 2.41/1.03      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.41/1.03      inference(demodulation,[status(thm)],[c_1580,c_1516]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_2325,plain,
% 2.41/1.03      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.41/1.03      inference(demodulation,[status(thm)],[c_2321,c_1582]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_16,plain,
% 2.41/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.41/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.03      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.41/1.03      | ~ v1_funct_1(X0)
% 2.41/1.03      | ~ v2_funct_1(X0)
% 2.41/1.03      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.41/1.03      inference(cnf_transformation,[],[f67]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_641,plain,
% 2.41/1.03      ( ~ v1_funct_2(X0_52,X0_53,X1_53)
% 2.41/1.03      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.41/1.03      | m1_subset_1(k2_funct_1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53)))
% 2.41/1.03      | ~ v1_funct_1(X0_52)
% 2.41/1.03      | ~ v2_funct_1(X0_52)
% 2.41/1.03      | k2_relset_1(X0_53,X1_53,X0_52) != X1_53 ),
% 2.41/1.03      inference(subtyping,[status(esa)],[c_16]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1093,plain,
% 2.41/1.03      ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
% 2.41/1.03      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.41/1.03      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.41/1.03      | m1_subset_1(k2_funct_1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) = iProver_top
% 2.41/1.03      | v1_funct_1(X0_52) != iProver_top
% 2.41/1.03      | v2_funct_1(X0_52) != iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_641]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_3079,plain,
% 2.41/1.03      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.41/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 2.41/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.41/1.03      | v1_funct_1(sK2) != iProver_top
% 2.41/1.03      | v2_funct_1(sK2) != iProver_top ),
% 2.41/1.03      inference(superposition,[status(thm)],[c_2325,c_1093]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_633,negated_conjecture,
% 2.41/1.03      ( v1_funct_1(sK2) ),
% 2.41/1.03      inference(subtyping,[status(esa)],[c_27]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1100,plain,
% 2.41/1.03      ( v1_funct_1(sK2) = iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_4,plain,
% 2.41/1.03      ( ~ v1_funct_1(X0)
% 2.41/1.03      | ~ v2_funct_1(X0)
% 2.41/1.03      | ~ v1_relat_1(X0)
% 2.41/1.03      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 2.41/1.03      inference(cnf_transformation,[],[f53]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_647,plain,
% 2.41/1.03      ( ~ v1_funct_1(X0_52)
% 2.41/1.03      | ~ v2_funct_1(X0_52)
% 2.41/1.03      | ~ v1_relat_1(X0_52)
% 2.41/1.03      | k2_funct_1(X0_52) = k4_relat_1(X0_52) ),
% 2.41/1.03      inference(subtyping,[status(esa)],[c_4]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1087,plain,
% 2.41/1.03      ( k2_funct_1(X0_52) = k4_relat_1(X0_52)
% 2.41/1.03      | v1_funct_1(X0_52) != iProver_top
% 2.41/1.03      | v2_funct_1(X0_52) != iProver_top
% 2.41/1.03      | v1_relat_1(X0_52) != iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_647]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1742,plain,
% 2.41/1.03      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 2.41/1.03      | v2_funct_1(sK2) != iProver_top
% 2.41/1.03      | v1_relat_1(sK2) != iProver_top ),
% 2.41/1.03      inference(superposition,[status(thm)],[c_1100,c_1087]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_23,negated_conjecture,
% 2.41/1.03      ( v2_funct_1(sK2) ),
% 2.41/1.03      inference(cnf_transformation,[],[f78]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_699,plain,
% 2.41/1.03      ( ~ v1_funct_1(sK2)
% 2.41/1.03      | ~ v2_funct_1(sK2)
% 2.41/1.03      | ~ v1_relat_1(sK2)
% 2.41/1.03      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.41/1.03      inference(instantiation,[status(thm)],[c_647]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_2054,plain,
% 2.41/1.03      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.41/1.03      inference(global_propositional_subsumption,
% 2.41/1.03                [status(thm)],
% 2.41/1.03                [c_1742,c_27,c_25,c_23,c_699,c_1451,c_1475]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_3085,plain,
% 2.41/1.03      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.41/1.03      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 2.41/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.41/1.03      | v1_funct_1(sK2) != iProver_top
% 2.41/1.03      | v2_funct_1(sK2) != iProver_top ),
% 2.41/1.03      inference(light_normalisation,[status(thm)],[c_3079,c_2054]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_37,plain,
% 2.41/1.03      ( v2_funct_1(sK2) = iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1584,plain,
% 2.41/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.41/1.03      inference(demodulation,[status(thm)],[c_1580,c_1120]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_2324,plain,
% 2.41/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 2.41/1.03      inference(demodulation,[status(thm)],[c_2321,c_1584]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1585,plain,
% 2.41/1.03      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.41/1.03      inference(demodulation,[status(thm)],[c_1580,c_1114]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_2326,plain,
% 2.41/1.03      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 2.41/1.03      inference(demodulation,[status(thm)],[c_2321,c_1585]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_3567,plain,
% 2.41/1.03      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 2.41/1.03      inference(global_propositional_subsumption,
% 2.41/1.03                [status(thm)],
% 2.41/1.03                [c_3085,c_34,c_37,c_2324,c_2326]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_3573,plain,
% 2.41/1.03      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2)) ),
% 2.41/1.03      inference(superposition,[status(thm)],[c_3567,c_1092]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1083,plain,
% 2.41/1.03      ( m1_subset_1(X0_52,k1_zfmisc_1(X1_52)) != iProver_top
% 2.41/1.03      | v1_relat_1(X1_52) != iProver_top
% 2.41/1.03      | v1_relat_1(X0_52) = iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_651]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1447,plain,
% 2.41/1.03      ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != iProver_top
% 2.41/1.03      | v1_relat_1(sK2) = iProver_top ),
% 2.41/1.03      inference(superposition,[status(thm)],[c_1120,c_1083]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1726,plain,
% 2.41/1.03      ( v1_relat_1(sK2) = iProver_top ),
% 2.41/1.03      inference(global_propositional_subsumption,
% 2.41/1.03                [status(thm)],
% 2.41/1.03                [c_1447,c_36,c_1452,c_1476]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_2,plain,
% 2.41/1.03      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 2.41/1.03      inference(cnf_transformation,[],[f52]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_649,plain,
% 2.41/1.03      ( ~ v1_relat_1(X0_52)
% 2.41/1.03      | k2_relat_1(k4_relat_1(X0_52)) = k1_relat_1(X0_52) ),
% 2.41/1.03      inference(subtyping,[status(esa)],[c_2]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1085,plain,
% 2.41/1.03      ( k2_relat_1(k4_relat_1(X0_52)) = k1_relat_1(X0_52)
% 2.41/1.03      | v1_relat_1(X0_52) != iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_649]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1732,plain,
% 2.41/1.03      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.41/1.03      inference(superposition,[status(thm)],[c_1726,c_1085]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_3576,plain,
% 2.41/1.03      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.41/1.03      inference(light_normalisation,[status(thm)],[c_3573,c_1732]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_21,plain,
% 2.41/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.41/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.03      | ~ v1_funct_1(X0)
% 2.41/1.03      | ~ v2_funct_1(X0)
% 2.41/1.03      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.41/1.03      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.41/1.03      inference(cnf_transformation,[],[f70]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_638,plain,
% 2.41/1.03      ( ~ v1_funct_2(X0_52,X0_53,X1_53)
% 2.41/1.03      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.41/1.03      | ~ v1_funct_1(X0_52)
% 2.41/1.03      | ~ v2_funct_1(X0_52)
% 2.41/1.03      | k2_relset_1(X0_53,X1_53,X0_52) != X1_53
% 2.41/1.03      | k2_tops_2(X0_53,X1_53,X0_52) = k2_funct_1(X0_52) ),
% 2.41/1.03      inference(subtyping,[status(esa)],[c_21]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1096,plain,
% 2.41/1.03      ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
% 2.41/1.03      | k2_tops_2(X0_53,X1_53,X0_52) = k2_funct_1(X0_52)
% 2.41/1.03      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.41/1.03      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.41/1.03      | v1_funct_1(X0_52) != iProver_top
% 2.41/1.03      | v2_funct_1(X0_52) != iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_638]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_3737,plain,
% 2.41/1.03      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_funct_1(k4_relat_1(sK2))
% 2.41/1.03      | v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.41/1.03      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.41/1.03      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 2.41/1.03      | v2_funct_1(k4_relat_1(sK2)) != iProver_top ),
% 2.41/1.03      inference(superposition,[status(thm)],[c_3576,c_1096]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_8,plain,
% 2.41/1.03      ( ~ v1_funct_1(X0)
% 2.41/1.03      | ~ v2_funct_1(X0)
% 2.41/1.03      | ~ v1_relat_1(X0)
% 2.41/1.03      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.41/1.03      inference(cnf_transformation,[],[f57]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_643,plain,
% 2.41/1.03      ( ~ v1_funct_1(X0_52)
% 2.41/1.03      | ~ v2_funct_1(X0_52)
% 2.41/1.03      | ~ v1_relat_1(X0_52)
% 2.41/1.03      | k2_funct_1(k2_funct_1(X0_52)) = X0_52 ),
% 2.41/1.03      inference(subtyping,[status(esa)],[c_8]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1091,plain,
% 2.41/1.03      ( k2_funct_1(k2_funct_1(X0_52)) = X0_52
% 2.41/1.03      | v1_funct_1(X0_52) != iProver_top
% 2.41/1.03      | v2_funct_1(X0_52) != iProver_top
% 2.41/1.03      | v1_relat_1(X0_52) != iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_643]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1927,plain,
% 2.41/1.03      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.41/1.03      | v2_funct_1(sK2) != iProver_top
% 2.41/1.03      | v1_relat_1(sK2) != iProver_top ),
% 2.41/1.03      inference(superposition,[status(thm)],[c_1100,c_1091]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_711,plain,
% 2.41/1.03      ( ~ v1_funct_1(sK2)
% 2.41/1.03      | ~ v2_funct_1(sK2)
% 2.41/1.03      | ~ v1_relat_1(sK2)
% 2.41/1.03      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.41/1.03      inference(instantiation,[status(thm)],[c_643]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_2088,plain,
% 2.41/1.03      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.41/1.03      inference(global_propositional_subsumption,
% 2.41/1.03                [status(thm)],
% 2.41/1.03                [c_1927,c_27,c_25,c_23,c_711,c_1451,c_1475]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_2090,plain,
% 2.41/1.03      ( k2_funct_1(k4_relat_1(sK2)) = sK2 ),
% 2.41/1.03      inference(light_normalisation,[status(thm)],[c_2088,c_2054]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_3757,plain,
% 2.41/1.03      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = sK2
% 2.41/1.03      | v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.41/1.03      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.41/1.03      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 2.41/1.03      | v2_funct_1(k4_relat_1(sK2)) != iProver_top ),
% 2.41/1.03      inference(light_normalisation,[status(thm)],[c_3737,c_2090]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_6,plain,
% 2.41/1.03      ( ~ v1_funct_1(X0)
% 2.41/1.03      | v1_funct_1(k2_funct_1(X0))
% 2.41/1.03      | ~ v2_funct_1(X0)
% 2.41/1.03      | ~ v1_relat_1(X0) ),
% 2.41/1.03      inference(cnf_transformation,[],[f55]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_645,plain,
% 2.41/1.03      ( ~ v1_funct_1(X0_52)
% 2.41/1.03      | v1_funct_1(k2_funct_1(X0_52))
% 2.41/1.03      | ~ v2_funct_1(X0_52)
% 2.41/1.03      | ~ v1_relat_1(X0_52) ),
% 2.41/1.03      inference(subtyping,[status(esa)],[c_6]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1089,plain,
% 2.41/1.03      ( v1_funct_1(X0_52) != iProver_top
% 2.41/1.03      | v1_funct_1(k2_funct_1(X0_52)) = iProver_top
% 2.41/1.03      | v2_funct_1(X0_52) != iProver_top
% 2.41/1.03      | v1_relat_1(X0_52) != iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_645]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_2058,plain,
% 2.41/1.03      ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
% 2.41/1.03      | v1_funct_1(sK2) != iProver_top
% 2.41/1.03      | v2_funct_1(sK2) != iProver_top
% 2.41/1.03      | v1_relat_1(sK2) != iProver_top ),
% 2.41/1.03      inference(superposition,[status(thm)],[c_2054,c_1089]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_5,plain,
% 2.41/1.03      ( ~ v1_funct_1(X0)
% 2.41/1.03      | ~ v2_funct_1(X0)
% 2.41/1.03      | v2_funct_1(k2_funct_1(X0))
% 2.41/1.03      | ~ v1_relat_1(X0) ),
% 2.41/1.03      inference(cnf_transformation,[],[f56]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_646,plain,
% 2.41/1.03      ( ~ v1_funct_1(X0_52)
% 2.41/1.03      | ~ v2_funct_1(X0_52)
% 2.41/1.03      | v2_funct_1(k2_funct_1(X0_52))
% 2.41/1.03      | ~ v1_relat_1(X0_52) ),
% 2.41/1.03      inference(subtyping,[status(esa)],[c_5]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1088,plain,
% 2.41/1.03      ( v1_funct_1(X0_52) != iProver_top
% 2.41/1.03      | v2_funct_1(X0_52) != iProver_top
% 2.41/1.03      | v2_funct_1(k2_funct_1(X0_52)) = iProver_top
% 2.41/1.03      | v1_relat_1(X0_52) != iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_646]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_2059,plain,
% 2.41/1.03      ( v1_funct_1(sK2) != iProver_top
% 2.41/1.03      | v2_funct_1(k4_relat_1(sK2)) = iProver_top
% 2.41/1.03      | v2_funct_1(sK2) != iProver_top
% 2.41/1.03      | v1_relat_1(sK2) != iProver_top ),
% 2.41/1.03      inference(superposition,[status(thm)],[c_2054,c_1088]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_17,plain,
% 2.41/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.41/1.03      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.41/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.03      | ~ v1_funct_1(X0)
% 2.41/1.03      | ~ v2_funct_1(X0)
% 2.41/1.03      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.41/1.03      inference(cnf_transformation,[],[f66]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_640,plain,
% 2.41/1.03      ( ~ v1_funct_2(X0_52,X0_53,X1_53)
% 2.41/1.03      | v1_funct_2(k2_funct_1(X0_52),X1_53,X0_53)
% 2.41/1.03      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.41/1.03      | ~ v1_funct_1(X0_52)
% 2.41/1.03      | ~ v2_funct_1(X0_52)
% 2.41/1.03      | k2_relset_1(X0_53,X1_53,X0_52) != X1_53 ),
% 2.41/1.03      inference(subtyping,[status(esa)],[c_17]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1094,plain,
% 2.41/1.03      ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
% 2.41/1.03      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.41/1.03      | v1_funct_2(k2_funct_1(X0_52),X1_53,X0_53) = iProver_top
% 2.41/1.03      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.41/1.03      | v1_funct_1(X0_52) != iProver_top
% 2.41/1.03      | v2_funct_1(X0_52) != iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_640]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_3078,plain,
% 2.41/1.03      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 2.41/1.03      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.41/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.41/1.03      | v1_funct_1(sK2) != iProver_top
% 2.41/1.03      | v2_funct_1(sK2) != iProver_top ),
% 2.41/1.03      inference(superposition,[status(thm)],[c_2325,c_1094]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_3096,plain,
% 2.41/1.03      ( v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 2.41/1.03      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.41/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.41/1.03      | v1_funct_1(sK2) != iProver_top
% 2.41/1.03      | v2_funct_1(sK2) != iProver_top ),
% 2.41/1.03      inference(light_normalisation,[status(thm)],[c_3078,c_2054]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_3862,plain,
% 2.41/1.03      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = sK2 ),
% 2.41/1.03      inference(global_propositional_subsumption,
% 2.41/1.03                [status(thm)],
% 2.41/1.03                [c_3757,c_34,c_36,c_37,c_1452,c_1476,c_2058,c_2059,
% 2.41/1.03                 c_2324,c_2326,c_3085,c_3096]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_3077,plain,
% 2.41/1.03      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 2.41/1.03      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.41/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.41/1.03      | v1_funct_1(sK2) != iProver_top
% 2.41/1.03      | v2_funct_1(sK2) != iProver_top ),
% 2.41/1.03      inference(superposition,[status(thm)],[c_2325,c_1096]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_3107,plain,
% 2.41/1.03      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k4_relat_1(sK2)
% 2.41/1.03      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.41/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.41/1.03      | v1_funct_1(sK2) != iProver_top
% 2.41/1.03      | v2_funct_1(sK2) != iProver_top ),
% 2.41/1.03      inference(light_normalisation,[status(thm)],[c_3077,c_2054]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_3234,plain,
% 2.41/1.03      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k4_relat_1(sK2) ),
% 2.41/1.03      inference(global_propositional_subsumption,
% 2.41/1.03                [status(thm)],
% 2.41/1.03                [c_3107,c_34,c_37,c_2324,c_2326]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_15,plain,
% 2.41/1.03      ( r2_funct_2(X0,X1,X2,X2)
% 2.41/1.03      | ~ v1_funct_2(X2,X0,X1)
% 2.41/1.03      | ~ v1_funct_2(X3,X0,X1)
% 2.41/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.41/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.41/1.03      | ~ v1_funct_1(X2)
% 2.41/1.03      | ~ v1_funct_1(X3) ),
% 2.41/1.03      inference(cnf_transformation,[],[f64]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_22,negated_conjecture,
% 2.41/1.03      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 2.41/1.03      inference(cnf_transformation,[],[f79]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_382,plain,
% 2.41/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.41/1.03      | ~ v1_funct_2(X3,X1,X2)
% 2.41/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.03      | ~ v1_funct_1(X0)
% 2.41/1.03      | ~ v1_funct_1(X3)
% 2.41/1.03      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 2.41/1.03      | u1_struct_0(sK1) != X2
% 2.41/1.03      | u1_struct_0(sK0) != X1
% 2.41/1.03      | sK2 != X0 ),
% 2.41/1.03      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_383,plain,
% 2.41/1.03      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.41/1.03      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.41/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.41/1.03      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.41/1.03      | ~ v1_funct_1(X0)
% 2.41/1.03      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.41/1.03      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.41/1.03      inference(unflattening,[status(thm)],[c_382]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_630,plain,
% 2.41/1.03      ( ~ v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.41/1.03      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.41/1.03      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.41/1.03      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.41/1.03      | ~ v1_funct_1(X0_52)
% 2.41/1.03      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.41/1.03      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.41/1.03      inference(subtyping,[status(esa)],[c_383]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_653,plain,
% 2.41/1.03      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.41/1.03      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.41/1.03      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.41/1.03      | sP0_iProver_split
% 2.41/1.03      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.41/1.03      inference(splitting,
% 2.41/1.03                [splitting(split),new_symbols(definition,[])],
% 2.41/1.03                [c_630]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1101,plain,
% 2.41/1.03      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.41/1.03      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.41/1.03      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.41/1.03      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
% 2.41/1.03      | sP0_iProver_split = iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_653]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1249,plain,
% 2.41/1.03      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.41/1.03      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.41/1.03      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.41/1.03      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
% 2.41/1.03      | sP0_iProver_split = iProver_top ),
% 2.41/1.03      inference(light_normalisation,[status(thm)],[c_1101,c_631,c_632]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_652,plain,
% 2.41/1.03      ( ~ v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.41/1.03      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.41/1.03      | ~ v1_funct_1(X0_52)
% 2.41/1.03      | ~ sP0_iProver_split ),
% 2.41/1.03      inference(splitting,
% 2.41/1.03                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.41/1.03                [c_630]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1102,plain,
% 2.41/1.03      ( v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.41/1.03      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.41/1.03      | v1_funct_1(X0_52) != iProver_top
% 2.41/1.03      | sP0_iProver_split != iProver_top ),
% 2.41/1.03      inference(predicate_to_equality,[status(thm)],[c_652]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1181,plain,
% 2.41/1.03      ( v1_funct_2(X0_52,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.41/1.03      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.41/1.03      | v1_funct_1(X0_52) != iProver_top
% 2.41/1.03      | sP0_iProver_split != iProver_top ),
% 2.41/1.03      inference(light_normalisation,[status(thm)],[c_1102,c_631,c_632]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_1255,plain,
% 2.41/1.03      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.41/1.03      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.41/1.03      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.41/1.03      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.41/1.03      inference(forward_subsumption_resolution,
% 2.41/1.03                [status(thm)],
% 2.41/1.03                [c_1249,c_1181]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_2629,plain,
% 2.41/1.03      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
% 2.41/1.03      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.41/1.03      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.41/1.03      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
% 2.41/1.03      inference(light_normalisation,[status(thm)],[c_1255,c_1580,c_2321]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_3237,plain,
% 2.41/1.03      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) != sK2
% 2.41/1.03      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.41/1.03      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.41/1.03      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))) != iProver_top ),
% 2.41/1.03      inference(demodulation,[status(thm)],[c_3234,c_2629]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_3865,plain,
% 2.41/1.03      ( sK2 != sK2
% 2.41/1.03      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.41/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.41/1.03      | v1_funct_1(sK2) != iProver_top ),
% 2.41/1.03      inference(demodulation,[status(thm)],[c_3862,c_3237]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_655,plain,( X0_52 = X0_52 ),theory(equality) ).
% 2.41/1.03  
% 2.41/1.03  cnf(c_685,plain,
% 2.41/1.03      ( sK2 = sK2 ),
% 2.41/1.03      inference(instantiation,[status(thm)],[c_655]) ).
% 2.41/1.03  
% 2.41/1.03  cnf(contradiction,plain,
% 2.41/1.03      ( $false ),
% 2.41/1.03      inference(minisat,[status(thm)],[c_3865,c_2326,c_2324,c_685,c_34]) ).
% 2.41/1.03  
% 2.41/1.03  
% 2.41/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.41/1.03  
% 2.41/1.03  ------                               Statistics
% 2.41/1.03  
% 2.41/1.03  ------ General
% 2.41/1.03  
% 2.41/1.03  abstr_ref_over_cycles:                  0
% 2.41/1.03  abstr_ref_under_cycles:                 0
% 2.41/1.03  gc_basic_clause_elim:                   0
% 2.41/1.03  forced_gc_time:                         0
% 2.41/1.03  parsing_time:                           0.014
% 2.41/1.03  unif_index_cands_time:                  0.
% 2.41/1.03  unif_index_add_time:                    0.
% 2.41/1.03  orderings_time:                         0.
% 2.41/1.03  out_proof_time:                         0.013
% 2.41/1.03  total_time:                             0.15
% 2.41/1.03  num_of_symbols:                         57
% 2.41/1.03  num_of_terms:                           3638
% 2.41/1.03  
% 2.41/1.03  ------ Preprocessing
% 2.41/1.03  
% 2.41/1.03  num_of_splits:                          1
% 2.41/1.03  num_of_split_atoms:                     1
% 2.41/1.03  num_of_reused_defs:                     0
% 2.41/1.03  num_eq_ax_congr_red:                    7
% 2.41/1.03  num_of_sem_filtered_clauses:            2
% 2.41/1.03  num_of_subtypes:                        4
% 2.41/1.03  monotx_restored_types:                  1
% 2.41/1.03  sat_num_of_epr_types:                   0
% 2.41/1.03  sat_num_of_non_cyclic_types:            0
% 2.41/1.03  sat_guarded_non_collapsed_types:        1
% 2.41/1.03  num_pure_diseq_elim:                    0
% 2.41/1.03  simp_replaced_by:                       0
% 2.41/1.04  res_preprocessed:                       135
% 2.41/1.04  prep_upred:                             0
% 2.41/1.04  prep_unflattend:                        11
% 2.41/1.04  smt_new_axioms:                         0
% 2.41/1.04  pred_elim_cands:                        5
% 2.41/1.04  pred_elim:                              6
% 2.41/1.04  pred_elim_cl:                           7
% 2.41/1.04  pred_elim_cycles:                       9
% 2.41/1.04  merged_defs:                            0
% 2.41/1.04  merged_defs_ncl:                        0
% 2.41/1.04  bin_hyper_res:                          0
% 2.41/1.04  prep_cycles:                            4
% 2.41/1.04  pred_elim_time:                         0.005
% 2.41/1.04  splitting_time:                         0.
% 2.41/1.04  sem_filter_time:                        0.
% 2.41/1.04  monotx_time:                            0.
% 2.41/1.04  subtype_inf_time:                       0.001
% 2.41/1.04  
% 2.41/1.04  ------ Problem properties
% 2.41/1.04  
% 2.41/1.04  clauses:                                24
% 2.41/1.04  conjectures:                            5
% 2.41/1.04  epr:                                    2
% 2.41/1.04  horn:                                   24
% 2.41/1.04  ground:                                 8
% 2.41/1.04  unary:                                  8
% 2.41/1.04  binary:                                 3
% 2.41/1.04  lits:                                   75
% 2.41/1.04  lits_eq:                                15
% 2.41/1.04  fd_pure:                                0
% 2.41/1.04  fd_pseudo:                              0
% 2.41/1.04  fd_cond:                                0
% 2.41/1.04  fd_pseudo_cond:                         1
% 2.41/1.04  ac_symbols:                             0
% 2.41/1.04  
% 2.41/1.04  ------ Propositional Solver
% 2.41/1.04  
% 2.41/1.04  prop_solver_calls:                      29
% 2.41/1.04  prop_fast_solver_calls:                 1012
% 2.41/1.04  smt_solver_calls:                       0
% 2.41/1.04  smt_fast_solver_calls:                  0
% 2.41/1.04  prop_num_of_clauses:                    1455
% 2.41/1.04  prop_preprocess_simplified:             5160
% 2.41/1.04  prop_fo_subsumed:                       46
% 2.41/1.04  prop_solver_time:                       0.
% 2.41/1.04  smt_solver_time:                        0.
% 2.41/1.04  smt_fast_solver_time:                   0.
% 2.41/1.04  prop_fast_solver_time:                  0.
% 2.41/1.04  prop_unsat_core_time:                   0.
% 2.41/1.04  
% 2.41/1.04  ------ QBF
% 2.41/1.04  
% 2.41/1.04  qbf_q_res:                              0
% 2.41/1.04  qbf_num_tautologies:                    0
% 2.41/1.04  qbf_prep_cycles:                        0
% 2.41/1.04  
% 2.41/1.04  ------ BMC1
% 2.41/1.04  
% 2.41/1.04  bmc1_current_bound:                     -1
% 2.41/1.04  bmc1_last_solved_bound:                 -1
% 2.41/1.04  bmc1_unsat_core_size:                   -1
% 2.41/1.04  bmc1_unsat_core_parents_size:           -1
% 2.41/1.04  bmc1_merge_next_fun:                    0
% 2.41/1.04  bmc1_unsat_core_clauses_time:           0.
% 2.41/1.04  
% 2.41/1.04  ------ Instantiation
% 2.41/1.04  
% 2.41/1.04  inst_num_of_clauses:                    545
% 2.41/1.04  inst_num_in_passive:                    72
% 2.41/1.04  inst_num_in_active:                     270
% 2.41/1.04  inst_num_in_unprocessed:                203
% 2.41/1.04  inst_num_of_loops:                      290
% 2.41/1.04  inst_num_of_learning_restarts:          0
% 2.41/1.04  inst_num_moves_active_passive:          16
% 2.41/1.04  inst_lit_activity:                      0
% 2.41/1.04  inst_lit_activity_moves:                0
% 2.41/1.04  inst_num_tautologies:                   0
% 2.41/1.04  inst_num_prop_implied:                  0
% 2.41/1.04  inst_num_existing_simplified:           0
% 2.41/1.04  inst_num_eq_res_simplified:             0
% 2.41/1.04  inst_num_child_elim:                    0
% 2.41/1.04  inst_num_of_dismatching_blockings:      112
% 2.41/1.04  inst_num_of_non_proper_insts:           492
% 2.41/1.04  inst_num_of_duplicates:                 0
% 2.41/1.04  inst_inst_num_from_inst_to_res:         0
% 2.41/1.04  inst_dismatching_checking_time:         0.
% 2.41/1.04  
% 2.41/1.04  ------ Resolution
% 2.41/1.04  
% 2.41/1.04  res_num_of_clauses:                     0
% 2.41/1.04  res_num_in_passive:                     0
% 2.41/1.04  res_num_in_active:                      0
% 2.41/1.04  res_num_of_loops:                       139
% 2.41/1.04  res_forward_subset_subsumed:            52
% 2.41/1.04  res_backward_subset_subsumed:           0
% 2.41/1.04  res_forward_subsumed:                   0
% 2.41/1.04  res_backward_subsumed:                  0
% 2.41/1.04  res_forward_subsumption_resolution:     1
% 2.41/1.04  res_backward_subsumption_resolution:    0
% 2.41/1.04  res_clause_to_clause_subsumption:       111
% 2.41/1.04  res_orphan_elimination:                 0
% 2.41/1.04  res_tautology_del:                      47
% 2.41/1.04  res_num_eq_res_simplified:              0
% 2.41/1.04  res_num_sel_changes:                    0
% 2.41/1.04  res_moves_from_active_to_pass:          0
% 2.41/1.04  
% 2.41/1.04  ------ Superposition
% 2.41/1.04  
% 2.41/1.04  sup_time_total:                         0.
% 2.41/1.04  sup_time_generating:                    0.
% 2.41/1.04  sup_time_sim_full:                      0.
% 2.41/1.04  sup_time_sim_immed:                     0.
% 2.41/1.04  
% 2.41/1.04  sup_num_of_clauses:                     48
% 2.41/1.04  sup_num_in_active:                      42
% 2.41/1.04  sup_num_in_passive:                     6
% 2.41/1.04  sup_num_of_loops:                       56
% 2.41/1.04  sup_fw_superposition:                   14
% 2.41/1.04  sup_bw_superposition:                   30
% 2.41/1.04  sup_immediate_simplified:               20
% 2.41/1.04  sup_given_eliminated:                   0
% 2.41/1.04  comparisons_done:                       0
% 2.41/1.04  comparisons_avoided:                    0
% 2.41/1.04  
% 2.41/1.04  ------ Simplifications
% 2.41/1.04  
% 2.41/1.04  
% 2.41/1.04  sim_fw_subset_subsumed:                 5
% 2.41/1.04  sim_bw_subset_subsumed:                 0
% 2.41/1.04  sim_fw_subsumed:                        4
% 2.41/1.04  sim_bw_subsumed:                        0
% 2.41/1.04  sim_fw_subsumption_res:                 1
% 2.41/1.04  sim_bw_subsumption_res:                 0
% 2.41/1.04  sim_tautology_del:                      0
% 2.41/1.04  sim_eq_tautology_del:                   8
% 2.41/1.04  sim_eq_res_simp:                        0
% 2.41/1.04  sim_fw_demodulated:                     0
% 2.41/1.04  sim_bw_demodulated:                     14
% 2.41/1.04  sim_light_normalised:                   25
% 2.41/1.04  sim_joinable_taut:                      0
% 2.41/1.04  sim_joinable_simp:                      0
% 2.41/1.04  sim_ac_normalised:                      0
% 2.41/1.04  sim_smt_subsumption:                    0
% 2.41/1.04  
%------------------------------------------------------------------------------
