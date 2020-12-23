%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:35 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :  292 (12708 expanded)
%              Number of clauses        :  194 (4188 expanded)
%              Number of leaves         :   27 (3440 expanded)
%              Depth                    :   37
%              Number of atoms          : 1022 (77704 expanded)
%              Number of equality atoms :  408 (12618 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f59,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f64,plain,(
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

fof(f63,plain,(
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

fof(f62,plain,
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

fof(f65,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f60,f64,f63,f62])).

fof(f102,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f65])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f94,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f97,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f99,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f44])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f98,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f100,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f101,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f65])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f103,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f104,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f52])).

fof(f93,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f92,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f57])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f75,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f71,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f69,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f78,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f105,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_801,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_1352,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_801])).

cnf(c_28,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_39,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_446,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_39])).

cnf(c_447,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_797,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_447])).

cnf(c_37,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_441,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_37])).

cnf(c_442,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_798,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_442])).

cnf(c_1361,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1352,c_797,c_798])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_29,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_428,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_38])).

cnf(c_429,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_52,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_431,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_429,c_38,c_37,c_52])).

cnf(c_453,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_431])).

cnf(c_454,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_20,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_567,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_454,c_20])).

cnf(c_15,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_583,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_567,c_15])).

cnf(c_794,plain,
    ( ~ v1_funct_2(X0_56,X0_57,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_56)
    | ~ v1_relat_1(X0_56)
    | k1_relat_1(X0_56) = X0_57 ),
    inference(subtyping,[status(esa)],[c_583])).

cnf(c_1358,plain,
    ( k1_relat_1(X0_56) = X0_57
    | v1_funct_2(X0_56,X0_57,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_794])).

cnf(c_1363,plain,
    ( k1_relat_1(X0_56) = X0_57
    | v1_funct_2(X0_56,X0_57,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_relat_1(X0_56) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1358,c_798])).

cnf(c_1758,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1361,c_1363])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_43,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_45,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_800,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_1353,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_800])).

cnf(c_1359,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1353,c_797,c_798])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_822,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(X1_56))
    | ~ v1_relat_1(X1_56)
    | v1_relat_1(X0_56) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1482,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | v1_relat_1(X0_56)
    | ~ v1_relat_1(k2_zfmisc_1(X0_57,X1_57)) ),
    inference(instantiation,[status(thm)],[c_822])).

cnf(c_1606,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1482])).

cnf(c_1607,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1606])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_821,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_57,X1_57)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1654,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_821])).

cnf(c_1655,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1654])).

cnf(c_1838,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1758,c_43,c_45,c_1359,c_1607,c_1655])).

cnf(c_1841,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1838,c_1361])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_810,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | k2_relset_1(X0_57,X1_57,X0_56) = k2_relat_1(X0_56) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1344,plain,
    ( k2_relset_1(X0_57,X1_57,X0_56) = k2_relat_1(X0_56)
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_810])).

cnf(c_2005,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1841,c_1344])).

cnf(c_33,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_802,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_1360,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_802,c_797,c_798])).

cnf(c_1843,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1838,c_1360])).

cnf(c_2306,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2005,c_1843])).

cnf(c_2402,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2306,c_2005])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_809,plain,
    ( ~ v1_funct_2(X0_56,X0_57,X1_57)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | m1_subset_1(k2_funct_1(X0_56),k1_zfmisc_1(k2_zfmisc_1(X1_57,X0_57)))
    | ~ v2_funct_1(X0_56)
    | ~ v1_funct_1(X0_56)
    | k2_relset_1(X0_57,X1_57,X0_56) != X1_57 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1345,plain,
    ( k2_relset_1(X0_57,X1_57,X0_56) != X1_57
    | v1_funct_2(X0_56,X0_57,X1_57) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_56),k1_zfmisc_1(k2_zfmisc_1(X1_57,X0_57))) = iProver_top
    | v2_funct_1(X0_56) != iProver_top
    | v1_funct_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_809])).

cnf(c_3090,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2402,c_1345])).

cnf(c_32,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_46,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_25,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_806,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_56),k2_relat_1(X0_56))))
    | ~ v1_funct_1(X0_56)
    | ~ v1_relat_1(X0_56) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_912,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_56),k2_relat_1(X0_56)))) = iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_806])).

cnf(c_914,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_912])).

cnf(c_26,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_805,plain,
    ( v1_funct_2(X0_56,k1_relat_1(X0_56),k2_relat_1(X0_56))
    | ~ v1_funct_1(X0_56)
    | ~ v1_relat_1(X0_56) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_915,plain,
    ( v1_funct_2(X0_56,k1_relat_1(X0_56),k2_relat_1(X0_56)) = iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_805])).

cnf(c_917,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_915])).

cnf(c_3649,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3090,c_43,c_45,c_46,c_914,c_917,c_1607,c_1655])).

cnf(c_3654,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3649,c_1344])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_804,plain,
    ( ~ v1_funct_2(X0_56,X0_57,X1_57)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v2_funct_1(X0_56)
    | ~ v1_funct_1(X0_56)
    | k2_relset_1(X0_57,X1_57,X0_56) != X1_57
    | k2_tops_2(X0_57,X1_57,X0_56) = k2_funct_1(X0_56) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1350,plain,
    ( k2_relset_1(X0_57,X1_57,X0_56) != X1_57
    | k2_tops_2(X0_57,X1_57,X0_56) = k2_funct_1(X0_56)
    | v1_funct_2(X0_56,X0_57,X1_57) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v2_funct_1(X0_56) != iProver_top
    | v1_funct_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_804])).

cnf(c_3727,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3654,c_1350])).

cnf(c_44,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_7,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_816,plain,
    ( ~ v2_funct_1(X0_56)
    | v2_funct_1(k2_funct_1(X0_56))
    | ~ v1_funct_1(X0_56)
    | ~ v1_relat_1(X0_56) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_882,plain,
    ( v2_funct_1(X0_56) != iProver_top
    | v2_funct_1(k2_funct_1(X0_56)) = iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_816])).

cnf(c_884,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_882])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_807,plain,
    ( ~ v1_funct_2(X0_56,X0_57,X1_57)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v2_funct_1(X0_56)
    | ~ v1_funct_1(X0_56)
    | v1_funct_1(k2_funct_1(X0_56))
    | k2_relset_1(X0_57,X1_57,X0_56) != X1_57 ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1497,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_807])).

cnf(c_1498,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1497])).

cnf(c_831,plain,
    ( X0_57 != X1_57
    | X2_57 != X1_57
    | X2_57 = X0_57 ),
    theory(equality)).

cnf(c_1512,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_57
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X0_57 ),
    inference(instantiation,[status(thm)],[c_831])).

cnf(c_1555,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1512])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_808,plain,
    ( ~ v1_funct_2(X0_56,X0_57,X1_57)
    | v1_funct_2(k2_funct_1(X0_56),X1_57,X0_57)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v2_funct_1(X0_56)
    | ~ v1_funct_1(X0_56)
    | k2_relset_1(X0_57,X1_57,X0_56) != X1_57 ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1346,plain,
    ( k2_relset_1(X0_57,X1_57,X0_56) != X1_57
    | v1_funct_2(X0_56,X0_57,X1_57) != iProver_top
    | v1_funct_2(k2_funct_1(X0_56),X1_57,X0_57) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v2_funct_1(X0_56) != iProver_top
    | v1_funct_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_808])).

cnf(c_3003,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2402,c_1346])).

cnf(c_4,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_600,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_15,c_4])).

cnf(c_795,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_relat_1(X0_56)
    | k7_relat_1(X0_56,X0_57) = X0_56 ),
    inference(subtyping,[status(esa)],[c_600])).

cnf(c_1357,plain,
    ( k7_relat_1(X0_56,X0_57) = X0_56
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_795])).

cnf(c_867,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_57,X1_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_821])).

cnf(c_929,plain,
    ( k7_relat_1(X0_56,X0_57) = X0_56
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_795])).

cnf(c_1483,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v1_relat_1(X0_56) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0_57,X1_57)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1482])).

cnf(c_3659,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | k7_relat_1(X0_56,X0_57) = X0_56 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1357,c_867,c_929,c_1483])).

cnf(c_3660,plain,
    ( k7_relat_1(X0_56,X0_57) = X0_56
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3659])).

cnf(c_3668,plain,
    ( k7_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_funct_1(sK2) ),
    inference(superposition,[status(thm)],[c_3649,c_3660])).

cnf(c_1332,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(X1_56)) != iProver_top
    | v1_relat_1(X1_56) != iProver_top
    | v1_relat_1(X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_822])).

cnf(c_3655,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3649,c_1332])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_817,plain,
    ( ~ v1_funct_1(X0_56)
    | ~ v1_relat_1(X0_56)
    | v1_relat_1(k2_funct_1(X0_56)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_879,plain,
    ( v1_funct_1(X0_56) != iProver_top
    | v1_relat_1(X0_56) != iProver_top
    | v1_relat_1(k2_funct_1(X0_56)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_817])).

cnf(c_881,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_879])).

cnf(c_3814,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3655,c_43,c_45,c_881,c_1607,c_1655])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_820,plain,
    ( ~ v1_relat_1(X0_56)
    | k2_relat_1(k7_relat_1(X0_56,X0_57)) = k9_relat_1(X0_56,X0_57) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1334,plain,
    ( k2_relat_1(k7_relat_1(X0_56,X0_57)) = k9_relat_1(X0_56,X0_57)
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_820])).

cnf(c_3818,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0_57)) = k9_relat_1(k2_funct_1(sK2),X0_57) ),
    inference(superposition,[status(thm)],[c_3814,c_1334])).

cnf(c_803,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_1351,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_803])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_814,plain,
    ( ~ v2_funct_1(X0_56)
    | ~ v1_funct_1(X0_56)
    | ~ v1_relat_1(X0_56)
    | k9_relat_1(k2_funct_1(X0_56),X0_57) = k10_relat_1(X0_56,X0_57) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1340,plain,
    ( k9_relat_1(k2_funct_1(X0_56),X0_57) = k10_relat_1(X0_56,X0_57)
    | v2_funct_1(X0_56) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_814])).

cnf(c_2502,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0_57) = k10_relat_1(sK2,X0_57)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1351,c_1340])).

cnf(c_2697,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0_57) = k10_relat_1(sK2,X0_57) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2502,c_43,c_45,c_1607,c_1655])).

cnf(c_3820,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0_57)) = k10_relat_1(sK2,X0_57) ),
    inference(light_normalisation,[status(thm)],[c_3818,c_2697])).

cnf(c_5408,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3668,c_3820])).

cnf(c_1665,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1361,c_1332])).

cnf(c_1803,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1665,c_45,c_1607,c_1655])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_819,plain,
    ( ~ v1_relat_1(X0_56)
    | k10_relat_1(X0_56,k2_relat_1(X0_56)) = k1_relat_1(X0_56) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1335,plain,
    ( k10_relat_1(X0_56,k2_relat_1(X0_56)) = k1_relat_1(X0_56)
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_819])).

cnf(c_1808,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1803,c_1335])).

cnf(c_5409,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_5408,c_1808])).

cnf(c_7420,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3727,c_43,c_44,c_45,c_46,c_884,c_914,c_917,c_802,c_798,c_1498,c_1555,c_1607,c_1655,c_3003,c_3090,c_5409])).

cnf(c_10,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_815,plain,
    ( ~ v2_funct_1(X0_56)
    | ~ v1_funct_1(X0_56)
    | ~ v1_relat_1(X0_56)
    | k10_relat_1(k2_funct_1(X0_56),X0_57) = k9_relat_1(X0_56,X0_57) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1339,plain,
    ( k10_relat_1(k2_funct_1(X0_56),X0_57) = k9_relat_1(X0_56,X0_57)
    | v2_funct_1(X0_56) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_815])).

cnf(c_2493,plain,
    ( k10_relat_1(k2_funct_1(sK2),X0_57) = k9_relat_1(sK2,X0_57)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1351,c_1339])).

cnf(c_2662,plain,
    ( k10_relat_1(k2_funct_1(sK2),X0_57) = k9_relat_1(sK2,X0_57) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2493,c_43,c_45,c_1607,c_1655])).

cnf(c_3819,plain,
    ( k10_relat_1(k2_funct_1(sK2),k2_relat_1(k2_funct_1(sK2))) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3814,c_1335])).

cnf(c_3822,plain,
    ( k9_relat_1(sK2,k2_relat_1(k2_funct_1(sK2))) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2662,c_3819])).

cnf(c_6245,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(demodulation,[status(thm)],[c_5409,c_3822])).

cnf(c_2404,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2306,c_1841])).

cnf(c_3666,plain,
    ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_2404,c_3660])).

cnf(c_1807,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0_57)) = k9_relat_1(sK2,X0_57) ),
    inference(superposition,[status(thm)],[c_1803,c_1334])).

cnf(c_4781,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3666,c_1807])).

cnf(c_6250,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_6245,c_4781])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_812,plain,
    ( ~ v2_funct_1(X0_56)
    | ~ v1_funct_1(X0_56)
    | ~ v1_relat_1(X0_56)
    | k5_relat_1(X0_56,k2_funct_1(X0_56)) = k6_relat_1(k1_relat_1(X0_56)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1342,plain,
    ( k5_relat_1(X0_56,k2_funct_1(X0_56)) = k6_relat_1(k1_relat_1(X0_56))
    | v2_funct_1(X0_56) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_812])).

cnf(c_2571,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1351,c_1342])).

cnf(c_895,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_812])).

cnf(c_2824,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2571,c_36,c_34,c_32,c_895,c_1606,c_1654])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_811,plain,
    ( ~ v2_funct_1(X0_56)
    | ~ v1_funct_1(X0_56)
    | ~ v1_funct_1(X1_56)
    | ~ v1_relat_1(X0_56)
    | ~ v1_relat_1(X1_56)
    | k5_relat_1(X1_56,X0_56) != k6_relat_1(k2_relat_1(X0_56))
    | k1_relat_1(X0_56) != k2_relat_1(X1_56)
    | k2_funct_1(X0_56) = X1_56 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1343,plain,
    ( k5_relat_1(X0_56,X1_56) != k6_relat_1(k2_relat_1(X1_56))
    | k1_relat_1(X1_56) != k2_relat_1(X0_56)
    | k2_funct_1(X1_56) = X0_56
    | v2_funct_1(X1_56) != iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_relat_1(X1_56) != iProver_top
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_811])).

cnf(c_3000,plain,
    ( k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2824,c_1343])).

cnf(c_880,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_817])).

cnf(c_883,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_816])).

cnf(c_3001,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3000])).

cnf(c_3209,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k6_relat_1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3000,c_36,c_35,c_34,c_32,c_880,c_883,c_802,c_798,c_1497,c_1555,c_1606,c_1654,c_3001])).

cnf(c_3210,plain,
    ( k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(renaming,[status(thm)],[c_3209])).

cnf(c_6248,plain,
    ( k6_relat_1(k1_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_5409,c_3210])).

cnf(c_6249,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_6248])).

cnf(c_6252,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_6250,c_6249])).

cnf(c_6253,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_6252])).

cnf(c_7422,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_7420,c_6253])).

cnf(c_3087,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2402,c_1350])).

cnf(c_913,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_916,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_805])).

cnf(c_1926,plain,
    ( ~ v1_funct_2(X0_56,k1_relat_1(X0_56),k2_relat_1(X0_56))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_56),k2_relat_1(X0_56))))
    | ~ v2_funct_1(X0_56)
    | ~ v1_funct_1(X0_56)
    | k2_relset_1(k1_relat_1(X0_56),k2_relat_1(X0_56),X0_56) != k2_relat_1(X0_56)
    | k2_tops_2(k1_relat_1(X0_56),k2_relat_1(X0_56),X0_56) = k2_funct_1(X0_56) ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_1928,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
    | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1926])).

cnf(c_1348,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_56),k2_relat_1(X0_56)))) = iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_806])).

cnf(c_2084,plain,
    ( k2_relset_1(k1_relat_1(X0_56),k2_relat_1(X0_56),X0_56) = k2_relat_1(X0_56)
    | v1_funct_1(X0_56) != iProver_top
    | v1_relat_1(X0_56) != iProver_top ),
    inference(superposition,[status(thm)],[c_1348,c_1344])).

cnf(c_2087,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2084])).

cnf(c_3548,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3087,c_36,c_43,c_34,c_45,c_32,c_913,c_916,c_1606,c_1607,c_1654,c_1655,c_1928,c_2087])).

cnf(c_21,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_31,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_476,plain,
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
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_477,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_796,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_56)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_477])).

cnf(c_824,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sP0_iProver_split
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_796])).

cnf(c_1355,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_824])).

cnf(c_1364,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1355,c_797,c_798])).

cnf(c_823,plain,
    ( ~ v1_funct_2(X0_56,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_56)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_796])).

cnf(c_926,plain,
    ( v1_funct_2(X0_56,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_823])).

cnf(c_928,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_926])).

cnf(c_1798,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1364,c_43,c_44,c_45,c_928])).

cnf(c_1799,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1798])).

cnf(c_1840,plain,
    ( k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_relat_1(sK2),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1838,c_1799])).

cnf(c_2403,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2306,c_1840])).

cnf(c_3550,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3548,c_2403])).

cnf(c_7423,plain,
    ( sK2 != sK2
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7422,c_3550])).

cnf(c_826,plain,
    ( X0_56 = X0_56 ),
    theory(equality)).

cnf(c_862,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_826])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7423,c_1655,c_1607,c_917,c_914,c_862,c_45,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:50:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.68/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/0.99  
% 3.68/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.68/0.99  
% 3.68/0.99  ------  iProver source info
% 3.68/0.99  
% 3.68/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.68/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.68/0.99  git: non_committed_changes: false
% 3.68/0.99  git: last_make_outside_of_git: false
% 3.68/0.99  
% 3.68/0.99  ------ 
% 3.68/0.99  
% 3.68/0.99  ------ Input Options
% 3.68/0.99  
% 3.68/0.99  --out_options                           all
% 3.68/0.99  --tptp_safe_out                         true
% 3.68/0.99  --problem_path                          ""
% 3.68/0.99  --include_path                          ""
% 3.68/0.99  --clausifier                            res/vclausify_rel
% 3.68/0.99  --clausifier_options                    ""
% 3.68/0.99  --stdin                                 false
% 3.68/0.99  --stats_out                             all
% 3.68/0.99  
% 3.68/0.99  ------ General Options
% 3.68/0.99  
% 3.68/0.99  --fof                                   false
% 3.68/0.99  --time_out_real                         305.
% 3.68/0.99  --time_out_virtual                      -1.
% 3.68/0.99  --symbol_type_check                     false
% 3.68/0.99  --clausify_out                          false
% 3.68/0.99  --sig_cnt_out                           false
% 3.68/0.99  --trig_cnt_out                          false
% 3.68/0.99  --trig_cnt_out_tolerance                1.
% 3.68/0.99  --trig_cnt_out_sk_spl                   false
% 3.68/0.99  --abstr_cl_out                          false
% 3.68/0.99  
% 3.68/0.99  ------ Global Options
% 3.68/0.99  
% 3.68/0.99  --schedule                              default
% 3.68/0.99  --add_important_lit                     false
% 3.68/0.99  --prop_solver_per_cl                    1000
% 3.68/0.99  --min_unsat_core                        false
% 3.68/0.99  --soft_assumptions                      false
% 3.68/0.99  --soft_lemma_size                       3
% 3.68/0.99  --prop_impl_unit_size                   0
% 3.68/0.99  --prop_impl_unit                        []
% 3.68/0.99  --share_sel_clauses                     true
% 3.68/0.99  --reset_solvers                         false
% 3.68/0.99  --bc_imp_inh                            [conj_cone]
% 3.68/0.99  --conj_cone_tolerance                   3.
% 3.68/0.99  --extra_neg_conj                        none
% 3.68/0.99  --large_theory_mode                     true
% 3.68/0.99  --prolific_symb_bound                   200
% 3.68/0.99  --lt_threshold                          2000
% 3.68/0.99  --clause_weak_htbl                      true
% 3.68/0.99  --gc_record_bc_elim                     false
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing Options
% 3.68/0.99  
% 3.68/0.99  --preprocessing_flag                    true
% 3.68/0.99  --time_out_prep_mult                    0.1
% 3.68/0.99  --splitting_mode                        input
% 3.68/0.99  --splitting_grd                         true
% 3.68/0.99  --splitting_cvd                         false
% 3.68/0.99  --splitting_cvd_svl                     false
% 3.68/0.99  --splitting_nvd                         32
% 3.68/0.99  --sub_typing                            true
% 3.68/0.99  --prep_gs_sim                           true
% 3.68/0.99  --prep_unflatten                        true
% 3.68/0.99  --prep_res_sim                          true
% 3.68/0.99  --prep_upred                            true
% 3.68/0.99  --prep_sem_filter                       exhaustive
% 3.68/0.99  --prep_sem_filter_out                   false
% 3.68/0.99  --pred_elim                             true
% 3.68/0.99  --res_sim_input                         true
% 3.68/0.99  --eq_ax_congr_red                       true
% 3.68/0.99  --pure_diseq_elim                       true
% 3.68/0.99  --brand_transform                       false
% 3.68/0.99  --non_eq_to_eq                          false
% 3.68/0.99  --prep_def_merge                        true
% 3.68/0.99  --prep_def_merge_prop_impl              false
% 3.68/0.99  --prep_def_merge_mbd                    true
% 3.68/0.99  --prep_def_merge_tr_red                 false
% 3.68/0.99  --prep_def_merge_tr_cl                  false
% 3.68/0.99  --smt_preprocessing                     true
% 3.68/0.99  --smt_ac_axioms                         fast
% 3.68/0.99  --preprocessed_out                      false
% 3.68/0.99  --preprocessed_stats                    false
% 3.68/0.99  
% 3.68/0.99  ------ Abstraction refinement Options
% 3.68/0.99  
% 3.68/0.99  --abstr_ref                             []
% 3.68/0.99  --abstr_ref_prep                        false
% 3.68/0.99  --abstr_ref_until_sat                   false
% 3.68/0.99  --abstr_ref_sig_restrict                funpre
% 3.68/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.68/0.99  --abstr_ref_under                       []
% 3.68/0.99  
% 3.68/0.99  ------ SAT Options
% 3.68/0.99  
% 3.68/0.99  --sat_mode                              false
% 3.68/0.99  --sat_fm_restart_options                ""
% 3.68/0.99  --sat_gr_def                            false
% 3.68/0.99  --sat_epr_types                         true
% 3.68/0.99  --sat_non_cyclic_types                  false
% 3.68/0.99  --sat_finite_models                     false
% 3.68/0.99  --sat_fm_lemmas                         false
% 3.68/0.99  --sat_fm_prep                           false
% 3.68/0.99  --sat_fm_uc_incr                        true
% 3.68/0.99  --sat_out_model                         small
% 3.68/0.99  --sat_out_clauses                       false
% 3.68/0.99  
% 3.68/0.99  ------ QBF Options
% 3.68/0.99  
% 3.68/0.99  --qbf_mode                              false
% 3.68/0.99  --qbf_elim_univ                         false
% 3.68/0.99  --qbf_dom_inst                          none
% 3.68/0.99  --qbf_dom_pre_inst                      false
% 3.68/0.99  --qbf_sk_in                             false
% 3.68/0.99  --qbf_pred_elim                         true
% 3.68/0.99  --qbf_split                             512
% 3.68/0.99  
% 3.68/0.99  ------ BMC1 Options
% 3.68/0.99  
% 3.68/0.99  --bmc1_incremental                      false
% 3.68/0.99  --bmc1_axioms                           reachable_all
% 3.68/0.99  --bmc1_min_bound                        0
% 3.68/0.99  --bmc1_max_bound                        -1
% 3.68/0.99  --bmc1_max_bound_default                -1
% 3.68/0.99  --bmc1_symbol_reachability              true
% 3.68/0.99  --bmc1_property_lemmas                  false
% 3.68/0.99  --bmc1_k_induction                      false
% 3.68/0.99  --bmc1_non_equiv_states                 false
% 3.68/0.99  --bmc1_deadlock                         false
% 3.68/0.99  --bmc1_ucm                              false
% 3.68/0.99  --bmc1_add_unsat_core                   none
% 3.68/0.99  --bmc1_unsat_core_children              false
% 3.68/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.68/0.99  --bmc1_out_stat                         full
% 3.68/0.99  --bmc1_ground_init                      false
% 3.68/0.99  --bmc1_pre_inst_next_state              false
% 3.68/0.99  --bmc1_pre_inst_state                   false
% 3.68/0.99  --bmc1_pre_inst_reach_state             false
% 3.68/0.99  --bmc1_out_unsat_core                   false
% 3.68/0.99  --bmc1_aig_witness_out                  false
% 3.68/0.99  --bmc1_verbose                          false
% 3.68/0.99  --bmc1_dump_clauses_tptp                false
% 3.68/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.68/0.99  --bmc1_dump_file                        -
% 3.68/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.68/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.68/0.99  --bmc1_ucm_extend_mode                  1
% 3.68/0.99  --bmc1_ucm_init_mode                    2
% 3.68/0.99  --bmc1_ucm_cone_mode                    none
% 3.68/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.68/0.99  --bmc1_ucm_relax_model                  4
% 3.68/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.68/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.68/0.99  --bmc1_ucm_layered_model                none
% 3.68/0.99  --bmc1_ucm_max_lemma_size               10
% 3.68/0.99  
% 3.68/0.99  ------ AIG Options
% 3.68/0.99  
% 3.68/0.99  --aig_mode                              false
% 3.68/0.99  
% 3.68/0.99  ------ Instantiation Options
% 3.68/0.99  
% 3.68/0.99  --instantiation_flag                    true
% 3.68/0.99  --inst_sos_flag                         true
% 3.68/0.99  --inst_sos_phase                        true
% 3.68/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.68/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.68/0.99  --inst_lit_sel_side                     num_symb
% 3.68/0.99  --inst_solver_per_active                1400
% 3.68/0.99  --inst_solver_calls_frac                1.
% 3.68/0.99  --inst_passive_queue_type               priority_queues
% 3.68/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.68/0.99  --inst_passive_queues_freq              [25;2]
% 3.68/0.99  --inst_dismatching                      true
% 3.68/0.99  --inst_eager_unprocessed_to_passive     true
% 3.68/0.99  --inst_prop_sim_given                   true
% 3.68/0.99  --inst_prop_sim_new                     false
% 3.68/0.99  --inst_subs_new                         false
% 3.68/0.99  --inst_eq_res_simp                      false
% 3.68/0.99  --inst_subs_given                       false
% 3.68/0.99  --inst_orphan_elimination               true
% 3.68/0.99  --inst_learning_loop_flag               true
% 3.68/0.99  --inst_learning_start                   3000
% 3.68/0.99  --inst_learning_factor                  2
% 3.68/0.99  --inst_start_prop_sim_after_learn       3
% 3.68/0.99  --inst_sel_renew                        solver
% 3.68/0.99  --inst_lit_activity_flag                true
% 3.68/0.99  --inst_restr_to_given                   false
% 3.68/0.99  --inst_activity_threshold               500
% 3.68/0.99  --inst_out_proof                        true
% 3.68/0.99  
% 3.68/0.99  ------ Resolution Options
% 3.68/0.99  
% 3.68/0.99  --resolution_flag                       true
% 3.68/0.99  --res_lit_sel                           adaptive
% 3.68/0.99  --res_lit_sel_side                      none
% 3.68/0.99  --res_ordering                          kbo
% 3.68/0.99  --res_to_prop_solver                    active
% 3.68/0.99  --res_prop_simpl_new                    false
% 3.68/0.99  --res_prop_simpl_given                  true
% 3.68/0.99  --res_passive_queue_type                priority_queues
% 3.68/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.68/0.99  --res_passive_queues_freq               [15;5]
% 3.68/0.99  --res_forward_subs                      full
% 3.68/0.99  --res_backward_subs                     full
% 3.68/0.99  --res_forward_subs_resolution           true
% 3.68/0.99  --res_backward_subs_resolution          true
% 3.68/0.99  --res_orphan_elimination                true
% 3.68/0.99  --res_time_limit                        2.
% 3.68/0.99  --res_out_proof                         true
% 3.68/0.99  
% 3.68/0.99  ------ Superposition Options
% 3.68/0.99  
% 3.68/0.99  --superposition_flag                    true
% 3.68/0.99  --sup_passive_queue_type                priority_queues
% 3.68/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.68/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.68/0.99  --demod_completeness_check              fast
% 3.68/0.99  --demod_use_ground                      true
% 3.68/0.99  --sup_to_prop_solver                    passive
% 3.68/0.99  --sup_prop_simpl_new                    true
% 3.68/0.99  --sup_prop_simpl_given                  true
% 3.68/0.99  --sup_fun_splitting                     true
% 3.68/0.99  --sup_smt_interval                      50000
% 3.68/0.99  
% 3.68/0.99  ------ Superposition Simplification Setup
% 3.68/0.99  
% 3.68/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.68/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.68/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.68/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.68/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.68/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.68/0.99  --sup_immed_triv                        [TrivRules]
% 3.68/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.99  --sup_immed_bw_main                     []
% 3.68/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.68/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.68/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.99  --sup_input_bw                          []
% 3.68/0.99  
% 3.68/0.99  ------ Combination Options
% 3.68/0.99  
% 3.68/0.99  --comb_res_mult                         3
% 3.68/0.99  --comb_sup_mult                         2
% 3.68/0.99  --comb_inst_mult                        10
% 3.68/0.99  
% 3.68/0.99  ------ Debug Options
% 3.68/0.99  
% 3.68/0.99  --dbg_backtrace                         false
% 3.68/0.99  --dbg_dump_prop_clauses                 false
% 3.68/0.99  --dbg_dump_prop_clauses_file            -
% 3.68/0.99  --dbg_out_stat                          false
% 3.68/0.99  ------ Parsing...
% 3.68/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.68/0.99  ------ Proving...
% 3.68/0.99  ------ Problem Properties 
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  clauses                                 30
% 3.68/0.99  conjectures                             5
% 3.68/0.99  EPR                                     2
% 3.68/0.99  Horn                                    30
% 3.68/0.99  unary                                   8
% 3.68/0.99  binary                                  3
% 3.68/0.99  lits                                    98
% 3.68/0.99  lits eq                                 21
% 3.68/0.99  fd_pure                                 0
% 3.68/0.99  fd_pseudo                               0
% 3.68/0.99  fd_cond                                 0
% 3.68/0.99  fd_pseudo_cond                          2
% 3.68/0.99  AC symbols                              0
% 3.68/0.99  
% 3.68/0.99  ------ Schedule dynamic 5 is on 
% 3.68/0.99  
% 3.68/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  ------ 
% 3.68/0.99  Current options:
% 3.68/0.99  ------ 
% 3.68/0.99  
% 3.68/0.99  ------ Input Options
% 3.68/0.99  
% 3.68/0.99  --out_options                           all
% 3.68/0.99  --tptp_safe_out                         true
% 3.68/0.99  --problem_path                          ""
% 3.68/0.99  --include_path                          ""
% 3.68/0.99  --clausifier                            res/vclausify_rel
% 3.68/0.99  --clausifier_options                    ""
% 3.68/0.99  --stdin                                 false
% 3.68/0.99  --stats_out                             all
% 3.68/0.99  
% 3.68/0.99  ------ General Options
% 3.68/0.99  
% 3.68/0.99  --fof                                   false
% 3.68/0.99  --time_out_real                         305.
% 3.68/0.99  --time_out_virtual                      -1.
% 3.68/0.99  --symbol_type_check                     false
% 3.68/0.99  --clausify_out                          false
% 3.68/0.99  --sig_cnt_out                           false
% 3.68/0.99  --trig_cnt_out                          false
% 3.68/0.99  --trig_cnt_out_tolerance                1.
% 3.68/0.99  --trig_cnt_out_sk_spl                   false
% 3.68/0.99  --abstr_cl_out                          false
% 3.68/0.99  
% 3.68/0.99  ------ Global Options
% 3.68/0.99  
% 3.68/0.99  --schedule                              default
% 3.68/0.99  --add_important_lit                     false
% 3.68/0.99  --prop_solver_per_cl                    1000
% 3.68/0.99  --min_unsat_core                        false
% 3.68/0.99  --soft_assumptions                      false
% 3.68/0.99  --soft_lemma_size                       3
% 3.68/0.99  --prop_impl_unit_size                   0
% 3.68/0.99  --prop_impl_unit                        []
% 3.68/0.99  --share_sel_clauses                     true
% 3.68/0.99  --reset_solvers                         false
% 3.68/0.99  --bc_imp_inh                            [conj_cone]
% 3.68/0.99  --conj_cone_tolerance                   3.
% 3.68/0.99  --extra_neg_conj                        none
% 3.68/0.99  --large_theory_mode                     true
% 3.68/0.99  --prolific_symb_bound                   200
% 3.68/0.99  --lt_threshold                          2000
% 3.68/0.99  --clause_weak_htbl                      true
% 3.68/0.99  --gc_record_bc_elim                     false
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing Options
% 3.68/0.99  
% 3.68/0.99  --preprocessing_flag                    true
% 3.68/0.99  --time_out_prep_mult                    0.1
% 3.68/0.99  --splitting_mode                        input
% 3.68/0.99  --splitting_grd                         true
% 3.68/0.99  --splitting_cvd                         false
% 3.68/0.99  --splitting_cvd_svl                     false
% 3.68/0.99  --splitting_nvd                         32
% 3.68/0.99  --sub_typing                            true
% 3.68/0.99  --prep_gs_sim                           true
% 3.68/0.99  --prep_unflatten                        true
% 3.68/0.99  --prep_res_sim                          true
% 3.68/0.99  --prep_upred                            true
% 3.68/0.99  --prep_sem_filter                       exhaustive
% 3.68/0.99  --prep_sem_filter_out                   false
% 3.68/0.99  --pred_elim                             true
% 3.68/0.99  --res_sim_input                         true
% 3.68/0.99  --eq_ax_congr_red                       true
% 3.68/0.99  --pure_diseq_elim                       true
% 3.68/0.99  --brand_transform                       false
% 3.68/0.99  --non_eq_to_eq                          false
% 3.68/0.99  --prep_def_merge                        true
% 3.68/0.99  --prep_def_merge_prop_impl              false
% 3.68/0.99  --prep_def_merge_mbd                    true
% 3.68/0.99  --prep_def_merge_tr_red                 false
% 3.68/0.99  --prep_def_merge_tr_cl                  false
% 3.68/0.99  --smt_preprocessing                     true
% 3.68/0.99  --smt_ac_axioms                         fast
% 3.68/0.99  --preprocessed_out                      false
% 3.68/0.99  --preprocessed_stats                    false
% 3.68/0.99  
% 3.68/0.99  ------ Abstraction refinement Options
% 3.68/0.99  
% 3.68/0.99  --abstr_ref                             []
% 3.68/0.99  --abstr_ref_prep                        false
% 3.68/0.99  --abstr_ref_until_sat                   false
% 3.68/0.99  --abstr_ref_sig_restrict                funpre
% 3.68/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.68/0.99  --abstr_ref_under                       []
% 3.68/0.99  
% 3.68/0.99  ------ SAT Options
% 3.68/0.99  
% 3.68/0.99  --sat_mode                              false
% 3.68/0.99  --sat_fm_restart_options                ""
% 3.68/0.99  --sat_gr_def                            false
% 3.68/0.99  --sat_epr_types                         true
% 3.68/0.99  --sat_non_cyclic_types                  false
% 3.68/0.99  --sat_finite_models                     false
% 3.68/0.99  --sat_fm_lemmas                         false
% 3.68/0.99  --sat_fm_prep                           false
% 3.68/0.99  --sat_fm_uc_incr                        true
% 3.68/0.99  --sat_out_model                         small
% 3.68/0.99  --sat_out_clauses                       false
% 3.68/0.99  
% 3.68/0.99  ------ QBF Options
% 3.68/0.99  
% 3.68/0.99  --qbf_mode                              false
% 3.68/0.99  --qbf_elim_univ                         false
% 3.68/0.99  --qbf_dom_inst                          none
% 3.68/0.99  --qbf_dom_pre_inst                      false
% 3.68/0.99  --qbf_sk_in                             false
% 3.68/0.99  --qbf_pred_elim                         true
% 3.68/0.99  --qbf_split                             512
% 3.68/0.99  
% 3.68/0.99  ------ BMC1 Options
% 3.68/0.99  
% 3.68/0.99  --bmc1_incremental                      false
% 3.68/0.99  --bmc1_axioms                           reachable_all
% 3.68/0.99  --bmc1_min_bound                        0
% 3.68/0.99  --bmc1_max_bound                        -1
% 3.68/0.99  --bmc1_max_bound_default                -1
% 3.68/0.99  --bmc1_symbol_reachability              true
% 3.68/0.99  --bmc1_property_lemmas                  false
% 3.68/0.99  --bmc1_k_induction                      false
% 3.68/0.99  --bmc1_non_equiv_states                 false
% 3.68/0.99  --bmc1_deadlock                         false
% 3.68/0.99  --bmc1_ucm                              false
% 3.68/0.99  --bmc1_add_unsat_core                   none
% 3.68/0.99  --bmc1_unsat_core_children              false
% 3.68/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.68/0.99  --bmc1_out_stat                         full
% 3.68/0.99  --bmc1_ground_init                      false
% 3.68/0.99  --bmc1_pre_inst_next_state              false
% 3.68/0.99  --bmc1_pre_inst_state                   false
% 3.68/0.99  --bmc1_pre_inst_reach_state             false
% 3.68/0.99  --bmc1_out_unsat_core                   false
% 3.68/0.99  --bmc1_aig_witness_out                  false
% 3.68/0.99  --bmc1_verbose                          false
% 3.68/0.99  --bmc1_dump_clauses_tptp                false
% 3.68/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.68/0.99  --bmc1_dump_file                        -
% 3.68/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.68/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.68/0.99  --bmc1_ucm_extend_mode                  1
% 3.68/0.99  --bmc1_ucm_init_mode                    2
% 3.68/0.99  --bmc1_ucm_cone_mode                    none
% 3.68/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.68/0.99  --bmc1_ucm_relax_model                  4
% 3.68/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.68/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.68/0.99  --bmc1_ucm_layered_model                none
% 3.68/0.99  --bmc1_ucm_max_lemma_size               10
% 3.68/0.99  
% 3.68/0.99  ------ AIG Options
% 3.68/0.99  
% 3.68/0.99  --aig_mode                              false
% 3.68/0.99  
% 3.68/0.99  ------ Instantiation Options
% 3.68/0.99  
% 3.68/0.99  --instantiation_flag                    true
% 3.68/0.99  --inst_sos_flag                         true
% 3.68/0.99  --inst_sos_phase                        true
% 3.68/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.68/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.68/0.99  --inst_lit_sel_side                     none
% 3.68/0.99  --inst_solver_per_active                1400
% 3.68/0.99  --inst_solver_calls_frac                1.
% 3.68/0.99  --inst_passive_queue_type               priority_queues
% 3.68/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.68/0.99  --inst_passive_queues_freq              [25;2]
% 3.68/0.99  --inst_dismatching                      true
% 3.68/0.99  --inst_eager_unprocessed_to_passive     true
% 3.68/0.99  --inst_prop_sim_given                   true
% 3.68/0.99  --inst_prop_sim_new                     false
% 3.68/0.99  --inst_subs_new                         false
% 3.68/0.99  --inst_eq_res_simp                      false
% 3.68/0.99  --inst_subs_given                       false
% 3.68/0.99  --inst_orphan_elimination               true
% 3.68/0.99  --inst_learning_loop_flag               true
% 3.68/0.99  --inst_learning_start                   3000
% 3.68/0.99  --inst_learning_factor                  2
% 3.68/0.99  --inst_start_prop_sim_after_learn       3
% 3.68/0.99  --inst_sel_renew                        solver
% 3.68/0.99  --inst_lit_activity_flag                true
% 3.68/0.99  --inst_restr_to_given                   false
% 3.68/0.99  --inst_activity_threshold               500
% 3.68/0.99  --inst_out_proof                        true
% 3.68/0.99  
% 3.68/0.99  ------ Resolution Options
% 3.68/0.99  
% 3.68/0.99  --resolution_flag                       false
% 3.68/0.99  --res_lit_sel                           adaptive
% 3.68/0.99  --res_lit_sel_side                      none
% 3.68/0.99  --res_ordering                          kbo
% 3.68/0.99  --res_to_prop_solver                    active
% 3.68/0.99  --res_prop_simpl_new                    false
% 3.68/0.99  --res_prop_simpl_given                  true
% 3.68/0.99  --res_passive_queue_type                priority_queues
% 3.68/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.68/0.99  --res_passive_queues_freq               [15;5]
% 3.68/0.99  --res_forward_subs                      full
% 3.68/0.99  --res_backward_subs                     full
% 3.68/0.99  --res_forward_subs_resolution           true
% 3.68/0.99  --res_backward_subs_resolution          true
% 3.68/0.99  --res_orphan_elimination                true
% 3.68/0.99  --res_time_limit                        2.
% 3.68/0.99  --res_out_proof                         true
% 3.68/0.99  
% 3.68/0.99  ------ Superposition Options
% 3.68/0.99  
% 3.68/0.99  --superposition_flag                    true
% 3.68/0.99  --sup_passive_queue_type                priority_queues
% 3.68/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.68/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.68/0.99  --demod_completeness_check              fast
% 3.68/0.99  --demod_use_ground                      true
% 3.68/0.99  --sup_to_prop_solver                    passive
% 3.68/0.99  --sup_prop_simpl_new                    true
% 3.68/0.99  --sup_prop_simpl_given                  true
% 3.68/0.99  --sup_fun_splitting                     true
% 3.68/0.99  --sup_smt_interval                      50000
% 3.68/0.99  
% 3.68/0.99  ------ Superposition Simplification Setup
% 3.68/0.99  
% 3.68/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.68/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.68/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.68/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.68/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.68/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.68/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.68/0.99  --sup_immed_triv                        [TrivRules]
% 3.68/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.99  --sup_immed_bw_main                     []
% 3.68/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.68/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.68/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.68/0.99  --sup_input_bw                          []
% 3.68/0.99  
% 3.68/0.99  ------ Combination Options
% 3.68/0.99  
% 3.68/0.99  --comb_res_mult                         3
% 3.68/0.99  --comb_sup_mult                         2
% 3.68/0.99  --comb_inst_mult                        10
% 3.68/0.99  
% 3.68/0.99  ------ Debug Options
% 3.68/0.99  
% 3.68/0.99  --dbg_backtrace                         false
% 3.68/0.99  --dbg_dump_prop_clauses                 false
% 3.68/0.99  --dbg_dump_prop_clauses_file            -
% 3.68/0.99  --dbg_out_stat                          false
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  ------ Proving...
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  % SZS status Theorem for theBenchmark.p
% 3.68/0.99  
% 3.68/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.68/0.99  
% 3.68/0.99  fof(f22,conjecture,(
% 3.68/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f23,negated_conjecture,(
% 3.68/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 3.68/0.99    inference(negated_conjecture,[],[f22])).
% 3.68/0.99  
% 3.68/0.99  fof(f59,plain,(
% 3.68/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 3.68/0.99    inference(ennf_transformation,[],[f23])).
% 3.68/0.99  
% 3.68/0.99  fof(f60,plain,(
% 3.68/0.99    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 3.68/0.99    inference(flattening,[],[f59])).
% 3.68/0.99  
% 3.68/0.99  fof(f64,plain,(
% 3.68/0.99    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 3.68/0.99    introduced(choice_axiom,[])).
% 3.68/0.99  
% 3.68/0.99  fof(f63,plain,(
% 3.68/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 3.68/0.99    introduced(choice_axiom,[])).
% 3.68/0.99  
% 3.68/0.99  fof(f62,plain,(
% 3.68/0.99    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 3.68/0.99    introduced(choice_axiom,[])).
% 3.68/0.99  
% 3.68/0.99  fof(f65,plain,(
% 3.68/0.99    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 3.68/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f60,f64,f63,f62])).
% 3.68/0.99  
% 3.68/0.99  fof(f102,plain,(
% 3.68/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.68/0.99    inference(cnf_transformation,[],[f65])).
% 3.68/0.99  
% 3.68/0.99  fof(f19,axiom,(
% 3.68/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f54,plain,(
% 3.68/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.68/0.99    inference(ennf_transformation,[],[f19])).
% 3.68/0.99  
% 3.68/0.99  fof(f94,plain,(
% 3.68/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f54])).
% 3.68/0.99  
% 3.68/0.99  fof(f97,plain,(
% 3.68/0.99    l1_struct_0(sK0)),
% 3.68/0.99    inference(cnf_transformation,[],[f65])).
% 3.68/0.99  
% 3.68/0.99  fof(f99,plain,(
% 3.68/0.99    l1_struct_0(sK1)),
% 3.68/0.99    inference(cnf_transformation,[],[f65])).
% 3.68/0.99  
% 3.68/0.99  fof(f14,axiom,(
% 3.68/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f44,plain,(
% 3.68/0.99    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.68/0.99    inference(ennf_transformation,[],[f14])).
% 3.68/0.99  
% 3.68/0.99  fof(f45,plain,(
% 3.68/0.99    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.68/0.99    inference(flattening,[],[f44])).
% 3.68/0.99  
% 3.68/0.99  fof(f84,plain,(
% 3.68/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f45])).
% 3.68/0.99  
% 3.68/0.99  fof(f20,axiom,(
% 3.68/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f55,plain,(
% 3.68/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.68/0.99    inference(ennf_transformation,[],[f20])).
% 3.68/0.99  
% 3.68/0.99  fof(f56,plain,(
% 3.68/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.68/0.99    inference(flattening,[],[f55])).
% 3.68/0.99  
% 3.68/0.99  fof(f95,plain,(
% 3.68/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f56])).
% 3.68/0.99  
% 3.68/0.99  fof(f98,plain,(
% 3.68/0.99    ~v2_struct_0(sK1)),
% 3.68/0.99    inference(cnf_transformation,[],[f65])).
% 3.68/0.99  
% 3.68/0.99  fof(f15,axiom,(
% 3.68/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f46,plain,(
% 3.68/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.68/0.99    inference(ennf_transformation,[],[f15])).
% 3.68/0.99  
% 3.68/0.99  fof(f47,plain,(
% 3.68/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.68/0.99    inference(flattening,[],[f46])).
% 3.68/0.99  
% 3.68/0.99  fof(f61,plain,(
% 3.68/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.68/0.99    inference(nnf_transformation,[],[f47])).
% 3.68/0.99  
% 3.68/0.99  fof(f85,plain,(
% 3.68/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f61])).
% 3.68/0.99  
% 3.68/0.99  fof(f12,axiom,(
% 3.68/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f24,plain,(
% 3.68/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.68/0.99    inference(pure_predicate_removal,[],[f12])).
% 3.68/0.99  
% 3.68/0.99  fof(f42,plain,(
% 3.68/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/0.99    inference(ennf_transformation,[],[f24])).
% 3.68/0.99  
% 3.68/0.99  fof(f81,plain,(
% 3.68/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.68/0.99    inference(cnf_transformation,[],[f42])).
% 3.68/0.99  
% 3.68/0.99  fof(f100,plain,(
% 3.68/0.99    v1_funct_1(sK2)),
% 3.68/0.99    inference(cnf_transformation,[],[f65])).
% 3.68/0.99  
% 3.68/0.99  fof(f101,plain,(
% 3.68/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.68/0.99    inference(cnf_transformation,[],[f65])).
% 3.68/0.99  
% 3.68/0.99  fof(f1,axiom,(
% 3.68/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f25,plain,(
% 3.68/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.68/0.99    inference(ennf_transformation,[],[f1])).
% 3.68/0.99  
% 3.68/0.99  fof(f66,plain,(
% 3.68/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f25])).
% 3.68/0.99  
% 3.68/0.99  fof(f2,axiom,(
% 3.68/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f67,plain,(
% 3.68/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.68/0.99    inference(cnf_transformation,[],[f2])).
% 3.68/0.99  
% 3.68/0.99  fof(f13,axiom,(
% 3.68/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f43,plain,(
% 3.68/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.68/0.99    inference(ennf_transformation,[],[f13])).
% 3.68/0.99  
% 3.68/0.99  fof(f82,plain,(
% 3.68/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.68/0.99    inference(cnf_transformation,[],[f43])).
% 3.68/0.99  
% 3.68/0.99  fof(f103,plain,(
% 3.68/0.99    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 3.68/0.99    inference(cnf_transformation,[],[f65])).
% 3.68/0.99  
% 3.68/0.99  fof(f17,axiom,(
% 3.68/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f50,plain,(
% 3.68/0.99    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.68/0.99    inference(ennf_transformation,[],[f17])).
% 3.68/0.99  
% 3.68/0.99  fof(f51,plain,(
% 3.68/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.68/0.99    inference(flattening,[],[f50])).
% 3.68/0.99  
% 3.68/0.99  fof(f90,plain,(
% 3.68/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f51])).
% 3.68/0.99  
% 3.68/0.99  fof(f104,plain,(
% 3.68/0.99    v2_funct_1(sK2)),
% 3.68/0.99    inference(cnf_transformation,[],[f65])).
% 3.68/0.99  
% 3.68/0.99  fof(f18,axiom,(
% 3.68/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f52,plain,(
% 3.68/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.68/0.99    inference(ennf_transformation,[],[f18])).
% 3.68/0.99  
% 3.68/0.99  fof(f53,plain,(
% 3.68/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.68/0.99    inference(flattening,[],[f52])).
% 3.68/0.99  
% 3.68/0.99  fof(f93,plain,(
% 3.68/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f53])).
% 3.68/0.99  
% 3.68/0.99  fof(f92,plain,(
% 3.68/0.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f53])).
% 3.68/0.99  
% 3.68/0.99  fof(f21,axiom,(
% 3.68/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f57,plain,(
% 3.68/0.99    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.68/0.99    inference(ennf_transformation,[],[f21])).
% 3.68/0.99  
% 3.68/0.99  fof(f58,plain,(
% 3.68/0.99    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.68/0.99    inference(flattening,[],[f57])).
% 3.68/0.99  
% 3.68/0.99  fof(f96,plain,(
% 3.68/0.99    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f58])).
% 3.68/0.99  
% 3.68/0.99  fof(f7,axiom,(
% 3.68/0.99    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f32,plain,(
% 3.68/0.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.68/0.99    inference(ennf_transformation,[],[f7])).
% 3.68/0.99  
% 3.68/0.99  fof(f33,plain,(
% 3.68/0.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.68/0.99    inference(flattening,[],[f32])).
% 3.68/0.99  
% 3.68/0.99  fof(f75,plain,(
% 3.68/0.99    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f33])).
% 3.68/0.99  
% 3.68/0.99  fof(f88,plain,(
% 3.68/0.99    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f51])).
% 3.68/0.99  
% 3.68/0.99  fof(f89,plain,(
% 3.68/0.99    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f51])).
% 3.68/0.99  
% 3.68/0.99  fof(f5,axiom,(
% 3.68/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f28,plain,(
% 3.68/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.68/0.99    inference(ennf_transformation,[],[f5])).
% 3.68/0.99  
% 3.68/0.99  fof(f29,plain,(
% 3.68/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.68/0.99    inference(flattening,[],[f28])).
% 3.68/0.99  
% 3.68/0.99  fof(f70,plain,(
% 3.68/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f29])).
% 3.68/0.99  
% 3.68/0.99  fof(f6,axiom,(
% 3.68/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f30,plain,(
% 3.68/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.68/0.99    inference(ennf_transformation,[],[f6])).
% 3.68/0.99  
% 3.68/0.99  fof(f31,plain,(
% 3.68/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.68/0.99    inference(flattening,[],[f30])).
% 3.68/0.99  
% 3.68/0.99  fof(f71,plain,(
% 3.68/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f31])).
% 3.68/0.99  
% 3.68/0.99  fof(f3,axiom,(
% 3.68/0.99    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f26,plain,(
% 3.68/0.99    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.68/0.99    inference(ennf_transformation,[],[f3])).
% 3.68/0.99  
% 3.68/0.99  fof(f68,plain,(
% 3.68/0.99    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f26])).
% 3.68/0.99  
% 3.68/0.99  fof(f9,axiom,(
% 3.68/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f36,plain,(
% 3.68/0.99    ! [X0,X1] : ((k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.68/0.99    inference(ennf_transformation,[],[f9])).
% 3.68/0.99  
% 3.68/0.99  fof(f37,plain,(
% 3.68/0.99    ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.68/0.99    inference(flattening,[],[f36])).
% 3.68/0.99  
% 3.68/0.99  fof(f77,plain,(
% 3.68/0.99    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f37])).
% 3.68/0.99  
% 3.68/0.99  fof(f4,axiom,(
% 3.68/0.99    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f27,plain,(
% 3.68/0.99    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 3.68/0.99    inference(ennf_transformation,[],[f4])).
% 3.68/0.99  
% 3.68/0.99  fof(f69,plain,(
% 3.68/0.99    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f27])).
% 3.68/0.99  
% 3.68/0.99  fof(f8,axiom,(
% 3.68/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f34,plain,(
% 3.68/0.99    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.68/0.99    inference(ennf_transformation,[],[f8])).
% 3.68/0.99  
% 3.68/0.99  fof(f35,plain,(
% 3.68/0.99    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.68/0.99    inference(flattening,[],[f34])).
% 3.68/0.99  
% 3.68/0.99  fof(f76,plain,(
% 3.68/0.99    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f35])).
% 3.68/0.99  
% 3.68/0.99  fof(f10,axiom,(
% 3.68/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f38,plain,(
% 3.68/0.99    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.68/0.99    inference(ennf_transformation,[],[f10])).
% 3.68/0.99  
% 3.68/0.99  fof(f39,plain,(
% 3.68/0.99    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.68/0.99    inference(flattening,[],[f38])).
% 3.68/0.99  
% 3.68/0.99  fof(f78,plain,(
% 3.68/0.99    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f39])).
% 3.68/0.99  
% 3.68/0.99  fof(f11,axiom,(
% 3.68/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f40,plain,(
% 3.68/0.99    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.68/0.99    inference(ennf_transformation,[],[f11])).
% 3.68/0.99  
% 3.68/0.99  fof(f41,plain,(
% 3.68/0.99    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.68/0.99    inference(flattening,[],[f40])).
% 3.68/0.99  
% 3.68/0.99  fof(f80,plain,(
% 3.68/0.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f41])).
% 3.68/0.99  
% 3.68/0.99  fof(f16,axiom,(
% 3.68/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 3.68/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.68/0.99  
% 3.68/0.99  fof(f48,plain,(
% 3.68/0.99    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.68/0.99    inference(ennf_transformation,[],[f16])).
% 3.68/0.99  
% 3.68/0.99  fof(f49,plain,(
% 3.68/0.99    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.68/0.99    inference(flattening,[],[f48])).
% 3.68/0.99  
% 3.68/0.99  fof(f87,plain,(
% 3.68/0.99    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.68/0.99    inference(cnf_transformation,[],[f49])).
% 3.68/0.99  
% 3.68/0.99  fof(f105,plain,(
% 3.68/0.99    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 3.68/0.99    inference(cnf_transformation,[],[f65])).
% 3.68/0.99  
% 3.68/0.99  cnf(c_34,negated_conjecture,
% 3.68/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.68/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_801,negated_conjecture,
% 3.68/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.68/0.99      inference(subtyping,[status(esa)],[c_34]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1352,plain,
% 3.68/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_801]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_28,plain,
% 3.68/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_39,negated_conjecture,
% 3.68/0.99      ( l1_struct_0(sK0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_446,plain,
% 3.68/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 3.68/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_39]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_447,plain,
% 3.68/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.68/0.99      inference(unflattening,[status(thm)],[c_446]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_797,plain,
% 3.68/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.68/0.99      inference(subtyping,[status(esa)],[c_447]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_37,negated_conjecture,
% 3.68/0.99      ( l1_struct_0(sK1) ),
% 3.68/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_441,plain,
% 3.68/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 3.68/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_37]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_442,plain,
% 3.68/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.68/0.99      inference(unflattening,[status(thm)],[c_441]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_798,plain,
% 3.68/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.68/0.99      inference(subtyping,[status(esa)],[c_442]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1361,plain,
% 3.68/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 3.68/0.99      inference(light_normalisation,[status(thm)],[c_1352,c_797,c_798]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_17,plain,
% 3.68/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.68/0.99      | v1_partfun1(X0,X1)
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.99      | v1_xboole_0(X2)
% 3.68/0.99      | ~ v1_funct_1(X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_29,plain,
% 3.68/0.99      ( v2_struct_0(X0)
% 3.68/0.99      | ~ l1_struct_0(X0)
% 3.68/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.68/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_38,negated_conjecture,
% 3.68/0.99      ( ~ v2_struct_0(sK1) ),
% 3.68/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_428,plain,
% 3.68/0.99      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 3.68/0.99      inference(resolution_lifted,[status(thm)],[c_29,c_38]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_429,plain,
% 3.68/0.99      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 3.68/0.99      inference(unflattening,[status(thm)],[c_428]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_52,plain,
% 3.68/0.99      ( v2_struct_0(sK1)
% 3.68/0.99      | ~ l1_struct_0(sK1)
% 3.68/0.99      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_29]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_431,plain,
% 3.68/0.99      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_429,c_38,c_37,c_52]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_453,plain,
% 3.68/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.68/0.99      | v1_partfun1(X0,X1)
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.99      | ~ v1_funct_1(X0)
% 3.68/0.99      | u1_struct_0(sK1) != X2 ),
% 3.68/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_431]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_454,plain,
% 3.68/0.99      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 3.68/0.99      | v1_partfun1(X0,X1)
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 3.68/0.99      | ~ v1_funct_1(X0) ),
% 3.68/0.99      inference(unflattening,[status(thm)],[c_453]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_20,plain,
% 3.68/0.99      ( ~ v1_partfun1(X0,X1)
% 3.68/0.99      | ~ v4_relat_1(X0,X1)
% 3.68/0.99      | ~ v1_relat_1(X0)
% 3.68/0.99      | k1_relat_1(X0) = X1 ),
% 3.68/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_567,plain,
% 3.68/0.99      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 3.68/0.99      | ~ v4_relat_1(X0,X1)
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 3.68/0.99      | ~ v1_funct_1(X0)
% 3.68/0.99      | ~ v1_relat_1(X0)
% 3.68/0.99      | k1_relat_1(X0) = X1 ),
% 3.68/0.99      inference(resolution,[status(thm)],[c_454,c_20]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_15,plain,
% 3.68/0.99      ( v4_relat_1(X0,X1)
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.68/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_583,plain,
% 3.68/0.99      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 3.68/0.99      | ~ v1_funct_1(X0)
% 3.68/0.99      | ~ v1_relat_1(X0)
% 3.68/0.99      | k1_relat_1(X0) = X1 ),
% 3.68/0.99      inference(forward_subsumption_resolution,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_567,c_15]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_794,plain,
% 3.68/0.99      ( ~ v1_funct_2(X0_56,X0_57,u1_struct_0(sK1))
% 3.68/0.99      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,u1_struct_0(sK1))))
% 3.68/0.99      | ~ v1_funct_1(X0_56)
% 3.68/0.99      | ~ v1_relat_1(X0_56)
% 3.68/0.99      | k1_relat_1(X0_56) = X0_57 ),
% 3.68/0.99      inference(subtyping,[status(esa)],[c_583]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1358,plain,
% 3.68/0.99      ( k1_relat_1(X0_56) = X0_57
% 3.68/0.99      | v1_funct_2(X0_56,X0_57,u1_struct_0(sK1)) != iProver_top
% 3.68/0.99      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,u1_struct_0(sK1)))) != iProver_top
% 3.68/0.99      | v1_funct_1(X0_56) != iProver_top
% 3.68/0.99      | v1_relat_1(X0_56) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_794]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1363,plain,
% 3.68/0.99      ( k1_relat_1(X0_56) = X0_57
% 3.68/0.99      | v1_funct_2(X0_56,X0_57,k2_struct_0(sK1)) != iProver_top
% 3.68/0.99      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,k2_struct_0(sK1)))) != iProver_top
% 3.68/0.99      | v1_funct_1(X0_56) != iProver_top
% 3.68/0.99      | v1_relat_1(X0_56) != iProver_top ),
% 3.68/0.99      inference(light_normalisation,[status(thm)],[c_1358,c_798]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1758,plain,
% 3.68/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 3.68/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.68/0.99      | v1_funct_1(sK2) != iProver_top
% 3.68/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1361,c_1363]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_36,negated_conjecture,
% 3.68/0.99      ( v1_funct_1(sK2) ),
% 3.68/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_43,plain,
% 3.68/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_45,plain,
% 3.68/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_35,negated_conjecture,
% 3.68/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.68/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_800,negated_conjecture,
% 3.68/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.68/0.99      inference(subtyping,[status(esa)],[c_35]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1353,plain,
% 3.68/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_800]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1359,plain,
% 3.68/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 3.68/0.99      inference(light_normalisation,[status(thm)],[c_1353,c_797,c_798]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_0,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.68/0.99      | ~ v1_relat_1(X1)
% 3.68/0.99      | v1_relat_1(X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_822,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(X1_56))
% 3.68/0.99      | ~ v1_relat_1(X1_56)
% 3.68/0.99      | v1_relat_1(X0_56) ),
% 3.68/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1482,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 3.68/0.99      | v1_relat_1(X0_56)
% 3.68/0.99      | ~ v1_relat_1(k2_zfmisc_1(X0_57,X1_57)) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_822]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1606,plain,
% 3.68/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.68/0.99      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 3.68/0.99      | v1_relat_1(sK2) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_1482]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1607,plain,
% 3.68/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.68/0.99      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 3.68/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1606]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1,plain,
% 3.68/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.68/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_821,plain,
% 3.68/0.99      ( v1_relat_1(k2_zfmisc_1(X0_57,X1_57)) ),
% 3.68/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1654,plain,
% 3.68/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_821]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1655,plain,
% 3.68/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1654]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1838,plain,
% 3.68/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_1758,c_43,c_45,c_1359,c_1607,c_1655]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1841,plain,
% 3.68/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) = iProver_top ),
% 3.68/0.99      inference(demodulation,[status(thm)],[c_1838,c_1361]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_16,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_810,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 3.68/0.99      | k2_relset_1(X0_57,X1_57,X0_56) = k2_relat_1(X0_56) ),
% 3.68/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1344,plain,
% 3.68/0.99      ( k2_relset_1(X0_57,X1_57,X0_56) = k2_relat_1(X0_56)
% 3.68/0.99      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_810]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2005,plain,
% 3.68/0.99      ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1841,c_1344]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_33,negated_conjecture,
% 3.68/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.68/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_802,negated_conjecture,
% 3.68/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.68/0.99      inference(subtyping,[status(esa)],[c_33]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1360,plain,
% 3.68/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.68/0.99      inference(light_normalisation,[status(thm)],[c_802,c_797,c_798]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1843,plain,
% 3.68/0.99      ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.68/0.99      inference(demodulation,[status(thm)],[c_1838,c_1360]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2306,plain,
% 3.68/0.99      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 3.68/0.99      inference(demodulation,[status(thm)],[c_2005,c_1843]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2402,plain,
% 3.68/0.99      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 3.68/0.99      inference(demodulation,[status(thm)],[c_2306,c_2005]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_22,plain,
% 3.68/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.68/0.99      | ~ v2_funct_1(X0)
% 3.68/0.99      | ~ v1_funct_1(X0)
% 3.68/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.68/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_809,plain,
% 3.68/0.99      ( ~ v1_funct_2(X0_56,X0_57,X1_57)
% 3.68/0.99      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 3.68/0.99      | m1_subset_1(k2_funct_1(X0_56),k1_zfmisc_1(k2_zfmisc_1(X1_57,X0_57)))
% 3.68/0.99      | ~ v2_funct_1(X0_56)
% 3.68/0.99      | ~ v1_funct_1(X0_56)
% 3.68/0.99      | k2_relset_1(X0_57,X1_57,X0_56) != X1_57 ),
% 3.68/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1345,plain,
% 3.68/0.99      ( k2_relset_1(X0_57,X1_57,X0_56) != X1_57
% 3.68/0.99      | v1_funct_2(X0_56,X0_57,X1_57) != iProver_top
% 3.68/0.99      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 3.68/0.99      | m1_subset_1(k2_funct_1(X0_56),k1_zfmisc_1(k2_zfmisc_1(X1_57,X0_57))) = iProver_top
% 3.68/0.99      | v2_funct_1(X0_56) != iProver_top
% 3.68/0.99      | v1_funct_1(X0_56) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_809]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3090,plain,
% 3.68/0.99      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.68/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 3.68/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.68/0.99      | v2_funct_1(sK2) != iProver_top
% 3.68/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_2402,c_1345]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_32,negated_conjecture,
% 3.68/0.99      ( v2_funct_1(sK2) ),
% 3.68/0.99      inference(cnf_transformation,[],[f104]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_46,plain,
% 3.68/0.99      ( v2_funct_1(sK2) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_25,plain,
% 3.68/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.68/0.99      | ~ v1_funct_1(X0)
% 3.68/0.99      | ~ v1_relat_1(X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_806,plain,
% 3.68/0.99      ( m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_56),k2_relat_1(X0_56))))
% 3.68/0.99      | ~ v1_funct_1(X0_56)
% 3.68/0.99      | ~ v1_relat_1(X0_56) ),
% 3.68/0.99      inference(subtyping,[status(esa)],[c_25]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_912,plain,
% 3.68/0.99      ( m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_56),k2_relat_1(X0_56)))) = iProver_top
% 3.68/0.99      | v1_funct_1(X0_56) != iProver_top
% 3.68/0.99      | v1_relat_1(X0_56) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_806]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_914,plain,
% 3.68/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
% 3.68/0.99      | v1_funct_1(sK2) != iProver_top
% 3.68/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_912]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_26,plain,
% 3.68/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.68/0.99      | ~ v1_funct_1(X0)
% 3.68/0.99      | ~ v1_relat_1(X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_805,plain,
% 3.68/0.99      ( v1_funct_2(X0_56,k1_relat_1(X0_56),k2_relat_1(X0_56))
% 3.68/0.99      | ~ v1_funct_1(X0_56)
% 3.68/0.99      | ~ v1_relat_1(X0_56) ),
% 3.68/0.99      inference(subtyping,[status(esa)],[c_26]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_915,plain,
% 3.68/0.99      ( v1_funct_2(X0_56,k1_relat_1(X0_56),k2_relat_1(X0_56)) = iProver_top
% 3.68/0.99      | v1_funct_1(X0_56) != iProver_top
% 3.68/0.99      | v1_relat_1(X0_56) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_805]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_917,plain,
% 3.68/0.99      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top
% 3.68/0.99      | v1_funct_1(sK2) != iProver_top
% 3.68/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_915]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3649,plain,
% 3.68/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_3090,c_43,c_45,c_46,c_914,c_917,c_1607,c_1655]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3654,plain,
% 3.68/0.99      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_3649,c_1344]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_30,plain,
% 3.68/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.99      | ~ v2_funct_1(X0)
% 3.68/0.99      | ~ v1_funct_1(X0)
% 3.68/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.68/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.68/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_804,plain,
% 3.68/0.99      ( ~ v1_funct_2(X0_56,X0_57,X1_57)
% 3.68/0.99      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 3.68/0.99      | ~ v2_funct_1(X0_56)
% 3.68/0.99      | ~ v1_funct_1(X0_56)
% 3.68/0.99      | k2_relset_1(X0_57,X1_57,X0_56) != X1_57
% 3.68/0.99      | k2_tops_2(X0_57,X1_57,X0_56) = k2_funct_1(X0_56) ),
% 3.68/0.99      inference(subtyping,[status(esa)],[c_30]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1350,plain,
% 3.68/0.99      ( k2_relset_1(X0_57,X1_57,X0_56) != X1_57
% 3.68/0.99      | k2_tops_2(X0_57,X1_57,X0_56) = k2_funct_1(X0_56)
% 3.68/0.99      | v1_funct_2(X0_56,X0_57,X1_57) != iProver_top
% 3.68/0.99      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 3.68/0.99      | v2_funct_1(X0_56) != iProver_top
% 3.68/0.99      | v1_funct_1(X0_56) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_804]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3727,plain,
% 3.68/0.99      ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
% 3.68/0.99      | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 3.68/0.99      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.68/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.68/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.68/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_3654,c_1350]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_44,plain,
% 3.68/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7,plain,
% 3.68/0.99      ( ~ v2_funct_1(X0)
% 3.68/0.99      | v2_funct_1(k2_funct_1(X0))
% 3.68/0.99      | ~ v1_funct_1(X0)
% 3.68/0.99      | ~ v1_relat_1(X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_816,plain,
% 3.68/0.99      ( ~ v2_funct_1(X0_56)
% 3.68/0.99      | v2_funct_1(k2_funct_1(X0_56))
% 3.68/0.99      | ~ v1_funct_1(X0_56)
% 3.68/0.99      | ~ v1_relat_1(X0_56) ),
% 3.68/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_882,plain,
% 3.68/0.99      ( v2_funct_1(X0_56) != iProver_top
% 3.68/0.99      | v2_funct_1(k2_funct_1(X0_56)) = iProver_top
% 3.68/0.99      | v1_funct_1(X0_56) != iProver_top
% 3.68/0.99      | v1_relat_1(X0_56) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_816]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_884,plain,
% 3.68/0.99      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.68/0.99      | v2_funct_1(sK2) != iProver_top
% 3.68/0.99      | v1_funct_1(sK2) != iProver_top
% 3.68/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_882]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_24,plain,
% 3.68/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.99      | ~ v2_funct_1(X0)
% 3.68/0.99      | ~ v1_funct_1(X0)
% 3.68/0.99      | v1_funct_1(k2_funct_1(X0))
% 3.68/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.68/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_807,plain,
% 3.68/0.99      ( ~ v1_funct_2(X0_56,X0_57,X1_57)
% 3.68/0.99      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 3.68/0.99      | ~ v2_funct_1(X0_56)
% 3.68/0.99      | ~ v1_funct_1(X0_56)
% 3.68/0.99      | v1_funct_1(k2_funct_1(X0_56))
% 3.68/0.99      | k2_relset_1(X0_57,X1_57,X0_56) != X1_57 ),
% 3.68/0.99      inference(subtyping,[status(esa)],[c_24]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1497,plain,
% 3.68/0.99      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.68/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.68/0.99      | ~ v2_funct_1(sK2)
% 3.68/0.99      | v1_funct_1(k2_funct_1(sK2))
% 3.68/0.99      | ~ v1_funct_1(sK2)
% 3.68/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_807]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1498,plain,
% 3.68/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 3.68/0.99      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.68/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.68/0.99      | v2_funct_1(sK2) != iProver_top
% 3.68/0.99      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.68/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1497]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_831,plain,
% 3.68/0.99      ( X0_57 != X1_57 | X2_57 != X1_57 | X2_57 = X0_57 ),
% 3.68/0.99      theory(equality) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1512,plain,
% 3.68/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_57
% 3.68/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 3.68/0.99      | u1_struct_0(sK1) != X0_57 ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_831]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1555,plain,
% 3.68/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 3.68/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 3.68/0.99      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_1512]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_23,plain,
% 3.68/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.68/0.99      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.99      | ~ v2_funct_1(X0)
% 3.68/0.99      | ~ v1_funct_1(X0)
% 3.68/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.68/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_808,plain,
% 3.68/0.99      ( ~ v1_funct_2(X0_56,X0_57,X1_57)
% 3.68/0.99      | v1_funct_2(k2_funct_1(X0_56),X1_57,X0_57)
% 3.68/0.99      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 3.68/0.99      | ~ v2_funct_1(X0_56)
% 3.68/0.99      | ~ v1_funct_1(X0_56)
% 3.68/0.99      | k2_relset_1(X0_57,X1_57,X0_56) != X1_57 ),
% 3.68/0.99      inference(subtyping,[status(esa)],[c_23]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1346,plain,
% 3.68/0.99      ( k2_relset_1(X0_57,X1_57,X0_56) != X1_57
% 3.68/0.99      | v1_funct_2(X0_56,X0_57,X1_57) != iProver_top
% 3.68/0.99      | v1_funct_2(k2_funct_1(X0_56),X1_57,X0_57) = iProver_top
% 3.68/0.99      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 3.68/0.99      | v2_funct_1(X0_56) != iProver_top
% 3.68/0.99      | v1_funct_1(X0_56) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_808]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3003,plain,
% 3.68/0.99      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 3.68/0.99      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.68/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.68/0.99      | v2_funct_1(sK2) != iProver_top
% 3.68/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_2402,c_1346]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4,plain,
% 3.68/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.68/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_600,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.99      | ~ v1_relat_1(X0)
% 3.68/0.99      | k7_relat_1(X0,X1) = X0 ),
% 3.68/0.99      inference(resolution,[status(thm)],[c_15,c_4]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_795,plain,
% 3.68/0.99      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 3.68/0.99      | ~ v1_relat_1(X0_56)
% 3.68/0.99      | k7_relat_1(X0_56,X0_57) = X0_56 ),
% 3.68/0.99      inference(subtyping,[status(esa)],[c_600]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1357,plain,
% 3.68/0.99      ( k7_relat_1(X0_56,X0_57) = X0_56
% 3.68/0.99      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 3.68/0.99      | v1_relat_1(X0_56) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_795]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_867,plain,
% 3.68/0.99      ( v1_relat_1(k2_zfmisc_1(X0_57,X1_57)) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_821]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_929,plain,
% 3.68/0.99      ( k7_relat_1(X0_56,X0_57) = X0_56
% 3.68/0.99      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 3.68/0.99      | v1_relat_1(X0_56) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_795]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1483,plain,
% 3.68/0.99      ( m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 3.68/0.99      | v1_relat_1(X0_56) = iProver_top
% 3.68/0.99      | v1_relat_1(k2_zfmisc_1(X0_57,X1_57)) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_1482]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3659,plain,
% 3.68/0.99      ( m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 3.68/0.99      | k7_relat_1(X0_56,X0_57) = X0_56 ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_1357,c_867,c_929,c_1483]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3660,plain,
% 3.68/0.99      ( k7_relat_1(X0_56,X0_57) = X0_56
% 3.68/0.99      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
% 3.68/0.99      inference(renaming,[status(thm)],[c_3659]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3668,plain,
% 3.68/0.99      ( k7_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_funct_1(sK2) ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_3649,c_3660]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1332,plain,
% 3.68/0.99      ( m1_subset_1(X0_56,k1_zfmisc_1(X1_56)) != iProver_top
% 3.68/0.99      | v1_relat_1(X1_56) != iProver_top
% 3.68/0.99      | v1_relat_1(X0_56) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_822]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3655,plain,
% 3.68/0.99      ( v1_relat_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))) != iProver_top
% 3.68/0.99      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_3649,c_1332]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_6,plain,
% 3.68/0.99      ( ~ v1_funct_1(X0)
% 3.68/0.99      | ~ v1_relat_1(X0)
% 3.68/0.99      | v1_relat_1(k2_funct_1(X0)) ),
% 3.68/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_817,plain,
% 3.68/0.99      ( ~ v1_funct_1(X0_56)
% 3.68/0.99      | ~ v1_relat_1(X0_56)
% 3.68/0.99      | v1_relat_1(k2_funct_1(X0_56)) ),
% 3.68/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_879,plain,
% 3.68/0.99      ( v1_funct_1(X0_56) != iProver_top
% 3.68/0.99      | v1_relat_1(X0_56) != iProver_top
% 3.68/0.99      | v1_relat_1(k2_funct_1(X0_56)) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_817]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_881,plain,
% 3.68/0.99      ( v1_funct_1(sK2) != iProver_top
% 3.68/0.99      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 3.68/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_879]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3814,plain,
% 3.68/0.99      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_3655,c_43,c_45,c_881,c_1607,c_1655]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2,plain,
% 3.68/0.99      ( ~ v1_relat_1(X0)
% 3.68/0.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.68/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_820,plain,
% 3.68/0.99      ( ~ v1_relat_1(X0_56)
% 3.68/0.99      | k2_relat_1(k7_relat_1(X0_56,X0_57)) = k9_relat_1(X0_56,X0_57) ),
% 3.68/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1334,plain,
% 3.68/0.99      ( k2_relat_1(k7_relat_1(X0_56,X0_57)) = k9_relat_1(X0_56,X0_57)
% 3.68/0.99      | v1_relat_1(X0_56) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_820]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3818,plain,
% 3.68/0.99      ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0_57)) = k9_relat_1(k2_funct_1(sK2),X0_57) ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_3814,c_1334]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_803,negated_conjecture,
% 3.68/0.99      ( v2_funct_1(sK2) ),
% 3.68/0.99      inference(subtyping,[status(esa)],[c_32]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1351,plain,
% 3.68/0.99      ( v2_funct_1(sK2) = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_803]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_11,plain,
% 3.68/0.99      ( ~ v2_funct_1(X0)
% 3.68/0.99      | ~ v1_funct_1(X0)
% 3.68/0.99      | ~ v1_relat_1(X0)
% 3.68/0.99      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
% 3.68/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_814,plain,
% 3.68/0.99      ( ~ v2_funct_1(X0_56)
% 3.68/0.99      | ~ v1_funct_1(X0_56)
% 3.68/0.99      | ~ v1_relat_1(X0_56)
% 3.68/0.99      | k9_relat_1(k2_funct_1(X0_56),X0_57) = k10_relat_1(X0_56,X0_57) ),
% 3.68/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1340,plain,
% 3.68/0.99      ( k9_relat_1(k2_funct_1(X0_56),X0_57) = k10_relat_1(X0_56,X0_57)
% 3.68/0.99      | v2_funct_1(X0_56) != iProver_top
% 3.68/0.99      | v1_funct_1(X0_56) != iProver_top
% 3.68/0.99      | v1_relat_1(X0_56) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_814]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2502,plain,
% 3.68/0.99      ( k9_relat_1(k2_funct_1(sK2),X0_57) = k10_relat_1(sK2,X0_57)
% 3.68/0.99      | v1_funct_1(sK2) != iProver_top
% 3.68/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1351,c_1340]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2697,plain,
% 3.68/0.99      ( k9_relat_1(k2_funct_1(sK2),X0_57) = k10_relat_1(sK2,X0_57) ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_2502,c_43,c_45,c_1607,c_1655]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3820,plain,
% 3.68/0.99      ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0_57)) = k10_relat_1(sK2,X0_57) ),
% 3.68/0.99      inference(light_normalisation,[status(thm)],[c_3818,c_2697]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5408,plain,
% 3.68/0.99      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_3668,c_3820]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1665,plain,
% 3.68/0.99      ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != iProver_top
% 3.68/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1361,c_1332]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1803,plain,
% 3.68/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_1665,c_45,c_1607,c_1655]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3,plain,
% 3.68/0.99      ( ~ v1_relat_1(X0)
% 3.68/0.99      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 3.68/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_819,plain,
% 3.68/0.99      ( ~ v1_relat_1(X0_56)
% 3.68/0.99      | k10_relat_1(X0_56,k2_relat_1(X0_56)) = k1_relat_1(X0_56) ),
% 3.68/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1335,plain,
% 3.68/0.99      ( k10_relat_1(X0_56,k2_relat_1(X0_56)) = k1_relat_1(X0_56)
% 3.68/0.99      | v1_relat_1(X0_56) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_819]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1808,plain,
% 3.68/0.99      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1803,c_1335]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_5409,plain,
% 3.68/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.68/0.99      inference(light_normalisation,[status(thm)],[c_5408,c_1808]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7420,plain,
% 3.68/0.99      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2)) ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_3727,c_43,c_44,c_45,c_46,c_884,c_914,c_917,c_802,
% 3.68/0.99                 c_798,c_1498,c_1555,c_1607,c_1655,c_3003,c_3090,c_5409]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_10,plain,
% 3.68/0.99      ( ~ v2_funct_1(X0)
% 3.68/0.99      | ~ v1_funct_1(X0)
% 3.68/0.99      | ~ v1_relat_1(X0)
% 3.68/0.99      | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
% 3.68/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_815,plain,
% 3.68/0.99      ( ~ v2_funct_1(X0_56)
% 3.68/0.99      | ~ v1_funct_1(X0_56)
% 3.68/0.99      | ~ v1_relat_1(X0_56)
% 3.68/0.99      | k10_relat_1(k2_funct_1(X0_56),X0_57) = k9_relat_1(X0_56,X0_57) ),
% 3.68/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1339,plain,
% 3.68/0.99      ( k10_relat_1(k2_funct_1(X0_56),X0_57) = k9_relat_1(X0_56,X0_57)
% 3.68/0.99      | v2_funct_1(X0_56) != iProver_top
% 3.68/0.99      | v1_funct_1(X0_56) != iProver_top
% 3.68/0.99      | v1_relat_1(X0_56) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_815]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2493,plain,
% 3.68/0.99      ( k10_relat_1(k2_funct_1(sK2),X0_57) = k9_relat_1(sK2,X0_57)
% 3.68/0.99      | v1_funct_1(sK2) != iProver_top
% 3.68/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1351,c_1339]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2662,plain,
% 3.68/0.99      ( k10_relat_1(k2_funct_1(sK2),X0_57) = k9_relat_1(sK2,X0_57) ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_2493,c_43,c_45,c_1607,c_1655]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3819,plain,
% 3.68/0.99      ( k10_relat_1(k2_funct_1(sK2),k2_relat_1(k2_funct_1(sK2))) = k1_relat_1(k2_funct_1(sK2)) ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_3814,c_1335]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3822,plain,
% 3.68/0.99      ( k9_relat_1(sK2,k2_relat_1(k2_funct_1(sK2))) = k1_relat_1(k2_funct_1(sK2)) ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_2662,c_3819]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_6245,plain,
% 3.68/0.99      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 3.68/0.99      inference(demodulation,[status(thm)],[c_5409,c_3822]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2404,plain,
% 3.68/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 3.68/0.99      inference(demodulation,[status(thm)],[c_2306,c_1841]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3666,plain,
% 3.68/0.99      ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_2404,c_3660]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1807,plain,
% 3.68/0.99      ( k2_relat_1(k7_relat_1(sK2,X0_57)) = k9_relat_1(sK2,X0_57) ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1803,c_1334]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_4781,plain,
% 3.68/0.99      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_3666,c_1807]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_6250,plain,
% 3.68/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.68/0.99      inference(light_normalisation,[status(thm)],[c_6245,c_4781]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_13,plain,
% 3.68/0.99      ( ~ v2_funct_1(X0)
% 3.68/0.99      | ~ v1_funct_1(X0)
% 3.68/0.99      | ~ v1_relat_1(X0)
% 3.68/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
% 3.68/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_812,plain,
% 3.68/0.99      ( ~ v2_funct_1(X0_56)
% 3.68/0.99      | ~ v1_funct_1(X0_56)
% 3.68/0.99      | ~ v1_relat_1(X0_56)
% 3.68/0.99      | k5_relat_1(X0_56,k2_funct_1(X0_56)) = k6_relat_1(k1_relat_1(X0_56)) ),
% 3.68/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1342,plain,
% 3.68/0.99      ( k5_relat_1(X0_56,k2_funct_1(X0_56)) = k6_relat_1(k1_relat_1(X0_56))
% 3.68/0.99      | v2_funct_1(X0_56) != iProver_top
% 3.68/0.99      | v1_funct_1(X0_56) != iProver_top
% 3.68/0.99      | v1_relat_1(X0_56) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_812]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2571,plain,
% 3.68/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
% 3.68/0.99      | v1_funct_1(sK2) != iProver_top
% 3.68/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1351,c_1342]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_895,plain,
% 3.68/0.99      ( ~ v2_funct_1(sK2)
% 3.68/0.99      | ~ v1_funct_1(sK2)
% 3.68/0.99      | ~ v1_relat_1(sK2)
% 3.68/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_812]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2824,plain,
% 3.68/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_2571,c_36,c_34,c_32,c_895,c_1606,c_1654]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_14,plain,
% 3.68/0.99      ( ~ v2_funct_1(X0)
% 3.68/0.99      | ~ v1_funct_1(X0)
% 3.68/0.99      | ~ v1_funct_1(X1)
% 3.68/0.99      | ~ v1_relat_1(X0)
% 3.68/0.99      | ~ v1_relat_1(X1)
% 3.68/0.99      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
% 3.68/0.99      | k2_funct_1(X0) = X1
% 3.68/0.99      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 3.68/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_811,plain,
% 3.68/0.99      ( ~ v2_funct_1(X0_56)
% 3.68/0.99      | ~ v1_funct_1(X0_56)
% 3.68/0.99      | ~ v1_funct_1(X1_56)
% 3.68/0.99      | ~ v1_relat_1(X0_56)
% 3.68/0.99      | ~ v1_relat_1(X1_56)
% 3.68/0.99      | k5_relat_1(X1_56,X0_56) != k6_relat_1(k2_relat_1(X0_56))
% 3.68/0.99      | k1_relat_1(X0_56) != k2_relat_1(X1_56)
% 3.68/0.99      | k2_funct_1(X0_56) = X1_56 ),
% 3.68/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1343,plain,
% 3.68/0.99      ( k5_relat_1(X0_56,X1_56) != k6_relat_1(k2_relat_1(X1_56))
% 3.68/0.99      | k1_relat_1(X1_56) != k2_relat_1(X0_56)
% 3.68/0.99      | k2_funct_1(X1_56) = X0_56
% 3.68/0.99      | v2_funct_1(X1_56) != iProver_top
% 3.68/0.99      | v1_funct_1(X1_56) != iProver_top
% 3.68/0.99      | v1_funct_1(X0_56) != iProver_top
% 3.68/0.99      | v1_relat_1(X1_56) != iProver_top
% 3.68/0.99      | v1_relat_1(X0_56) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_811]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3000,plain,
% 3.68/0.99      ( k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k6_relat_1(k1_relat_1(sK2))
% 3.68/0.99      | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
% 3.68/0.99      | k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.68/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.68/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.68/0.99      | v1_funct_1(sK2) != iProver_top
% 3.68/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.68/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_2824,c_1343]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_880,plain,
% 3.68/0.99      ( ~ v1_funct_1(sK2)
% 3.68/0.99      | v1_relat_1(k2_funct_1(sK2))
% 3.68/0.99      | ~ v1_relat_1(sK2) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_817]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_883,plain,
% 3.68/0.99      ( v2_funct_1(k2_funct_1(sK2))
% 3.68/0.99      | ~ v2_funct_1(sK2)
% 3.68/0.99      | ~ v1_funct_1(sK2)
% 3.68/0.99      | ~ v1_relat_1(sK2) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_816]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3001,plain,
% 3.68/0.99      ( ~ v2_funct_1(k2_funct_1(sK2))
% 3.68/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.68/0.99      | ~ v1_funct_1(sK2)
% 3.68/0.99      | ~ v1_relat_1(k2_funct_1(sK2))
% 3.68/0.99      | ~ v1_relat_1(sK2)
% 3.68/0.99      | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k6_relat_1(k1_relat_1(sK2))
% 3.68/0.99      | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
% 3.68/0.99      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.68/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3000]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3209,plain,
% 3.68/0.99      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.68/0.99      | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
% 3.68/0.99      | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k6_relat_1(k1_relat_1(sK2)) ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_3000,c_36,c_35,c_34,c_32,c_880,c_883,c_802,c_798,
% 3.68/0.99                 c_1497,c_1555,c_1606,c_1654,c_3001]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3210,plain,
% 3.68/0.99      ( k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k6_relat_1(k1_relat_1(sK2))
% 3.68/0.99      | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
% 3.68/0.99      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.68/0.99      inference(renaming,[status(thm)],[c_3209]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_6248,plain,
% 3.68/0.99      ( k6_relat_1(k1_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
% 3.68/0.99      | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
% 3.68/0.99      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.68/0.99      inference(demodulation,[status(thm)],[c_5409,c_3210]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_6249,plain,
% 3.68/0.99      ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
% 3.68/0.99      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.68/0.99      inference(equality_resolution_simp,[status(thm)],[c_6248]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_6252,plain,
% 3.68/0.99      ( k2_relat_1(sK2) != k2_relat_1(sK2)
% 3.68/0.99      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.68/0.99      inference(demodulation,[status(thm)],[c_6250,c_6249]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_6253,plain,
% 3.68/0.99      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.68/0.99      inference(equality_resolution_simp,[status(thm)],[c_6252]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7422,plain,
% 3.68/0.99      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 3.68/0.99      inference(light_normalisation,[status(thm)],[c_7420,c_6253]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3087,plain,
% 3.68/0.99      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 3.68/0.99      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.68/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.68/0.99      | v2_funct_1(sK2) != iProver_top
% 3.68/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_2402,c_1350]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_913,plain,
% 3.68/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 3.68/0.99      | ~ v1_funct_1(sK2)
% 3.68/0.99      | ~ v1_relat_1(sK2) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_806]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_916,plain,
% 3.68/0.99      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
% 3.68/0.99      | ~ v1_funct_1(sK2)
% 3.68/0.99      | ~ v1_relat_1(sK2) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_805]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1926,plain,
% 3.68/0.99      ( ~ v1_funct_2(X0_56,k1_relat_1(X0_56),k2_relat_1(X0_56))
% 3.68/0.99      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_56),k2_relat_1(X0_56))))
% 3.68/0.99      | ~ v2_funct_1(X0_56)
% 3.68/0.99      | ~ v1_funct_1(X0_56)
% 3.68/0.99      | k2_relset_1(k1_relat_1(X0_56),k2_relat_1(X0_56),X0_56) != k2_relat_1(X0_56)
% 3.68/0.99      | k2_tops_2(k1_relat_1(X0_56),k2_relat_1(X0_56),X0_56) = k2_funct_1(X0_56) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_804]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1928,plain,
% 3.68/0.99      ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
% 3.68/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 3.68/0.99      | ~ v2_funct_1(sK2)
% 3.68/0.99      | ~ v1_funct_1(sK2)
% 3.68/0.99      | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
% 3.68/0.99      | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_1926]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1348,plain,
% 3.68/0.99      ( m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_56),k2_relat_1(X0_56)))) = iProver_top
% 3.68/0.99      | v1_funct_1(X0_56) != iProver_top
% 3.68/0.99      | v1_relat_1(X0_56) != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_806]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2084,plain,
% 3.68/0.99      ( k2_relset_1(k1_relat_1(X0_56),k2_relat_1(X0_56),X0_56) = k2_relat_1(X0_56)
% 3.68/0.99      | v1_funct_1(X0_56) != iProver_top
% 3.68/0.99      | v1_relat_1(X0_56) != iProver_top ),
% 3.68/0.99      inference(superposition,[status(thm)],[c_1348,c_1344]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2087,plain,
% 3.68/0.99      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2)
% 3.68/0.99      | v1_funct_1(sK2) != iProver_top
% 3.68/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_2084]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3548,plain,
% 3.68/0.99      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_3087,c_36,c_43,c_34,c_45,c_32,c_913,c_916,c_1606,
% 3.68/0.99                 c_1607,c_1654,c_1655,c_1928,c_2087]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_21,plain,
% 3.68/0.99      ( r2_funct_2(X0,X1,X2,X2)
% 3.68/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.68/0.99      | ~ v1_funct_2(X3,X0,X1)
% 3.68/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.68/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.68/0.99      | ~ v1_funct_1(X2)
% 3.68/0.99      | ~ v1_funct_1(X3) ),
% 3.68/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_31,negated_conjecture,
% 3.68/0.99      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 3.68/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_476,plain,
% 3.68/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.68/0.99      | ~ v1_funct_2(X3,X1,X2)
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.68/0.99      | ~ v1_funct_1(X0)
% 3.68/0.99      | ~ v1_funct_1(X3)
% 3.68/0.99      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 3.68/0.99      | u1_struct_0(sK1) != X2
% 3.68/0.99      | u1_struct_0(sK0) != X1
% 3.68/0.99      | sK2 != X0 ),
% 3.68/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_477,plain,
% 3.68/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.68/0.99      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.68/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.68/0.99      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.68/0.99      | ~ v1_funct_1(X0)
% 3.68/0.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.68/0.99      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.68/0.99      inference(unflattening,[status(thm)],[c_476]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_796,plain,
% 3.68/0.99      ( ~ v1_funct_2(X0_56,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.68/0.99      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.68/0.99      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.68/0.99      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.68/0.99      | ~ v1_funct_1(X0_56)
% 3.68/0.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.68/0.99      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.68/0.99      inference(subtyping,[status(esa)],[c_477]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_824,plain,
% 3.68/0.99      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.68/0.99      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.68/0.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.68/0.99      | sP0_iProver_split
% 3.68/0.99      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.68/0.99      inference(splitting,
% 3.68/0.99                [splitting(split),new_symbols(definition,[])],
% 3.68/0.99                [c_796]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1355,plain,
% 3.68/0.99      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.68/0.99      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.68/0.99      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.68/0.99      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
% 3.68/0.99      | sP0_iProver_split = iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_824]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1364,plain,
% 3.68/0.99      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 3.68/0.99      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.68/0.99      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.68/0.99      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
% 3.68/0.99      | sP0_iProver_split = iProver_top ),
% 3.68/0.99      inference(light_normalisation,[status(thm)],[c_1355,c_797,c_798]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_823,plain,
% 3.68/0.99      ( ~ v1_funct_2(X0_56,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.68/0.99      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.68/0.99      | ~ v1_funct_1(X0_56)
% 3.68/0.99      | ~ sP0_iProver_split ),
% 3.68/0.99      inference(splitting,
% 3.68/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.68/0.99                [c_796]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_926,plain,
% 3.68/0.99      ( v1_funct_2(X0_56,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.68/0.99      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.68/0.99      | v1_funct_1(X0_56) != iProver_top
% 3.68/0.99      | sP0_iProver_split != iProver_top ),
% 3.68/0.99      inference(predicate_to_equality,[status(thm)],[c_823]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_928,plain,
% 3.68/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.68/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.68/0.99      | v1_funct_1(sK2) != iProver_top
% 3.68/0.99      | sP0_iProver_split != iProver_top ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_926]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1798,plain,
% 3.68/0.99      ( v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
% 3.68/0.99      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.68/0.99      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.68/0.99      | k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2 ),
% 3.68/0.99      inference(global_propositional_subsumption,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_1364,c_43,c_44,c_45,c_928]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1799,plain,
% 3.68/0.99      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 3.68/0.99      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.68/0.99      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.68/0.99      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 3.68/0.99      inference(renaming,[status(thm)],[c_1798]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_1840,plain,
% 3.68/0.99      ( k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) != sK2
% 3.68/0.99      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_relat_1(sK2),k2_struct_0(sK1)) != iProver_top
% 3.68/0.99      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) != iProver_top
% 3.68/0.99      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))) != iProver_top ),
% 3.68/0.99      inference(demodulation,[status(thm)],[c_1838,c_1799]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_2403,plain,
% 3.68/0.99      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
% 3.68/0.99      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.68/0.99      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.68/0.99      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
% 3.68/0.99      inference(demodulation,[status(thm)],[c_2306,c_1840]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_3550,plain,
% 3.68/0.99      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 3.68/0.99      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.68/0.99      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.68/0.99      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 3.68/0.99      inference(demodulation,[status(thm)],[c_3548,c_2403]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_7423,plain,
% 3.68/0.99      ( sK2 != sK2
% 3.68/0.99      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.68/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.68/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.68/0.99      inference(demodulation,[status(thm)],[c_7422,c_3550]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_826,plain,( X0_56 = X0_56 ),theory(equality) ).
% 3.68/0.99  
% 3.68/0.99  cnf(c_862,plain,
% 3.68/0.99      ( sK2 = sK2 ),
% 3.68/0.99      inference(instantiation,[status(thm)],[c_826]) ).
% 3.68/0.99  
% 3.68/0.99  cnf(contradiction,plain,
% 3.68/0.99      ( $false ),
% 3.68/0.99      inference(minisat,
% 3.68/0.99                [status(thm)],
% 3.68/0.99                [c_7423,c_1655,c_1607,c_917,c_914,c_862,c_45,c_43]) ).
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.68/0.99  
% 3.68/0.99  ------                               Statistics
% 3.68/0.99  
% 3.68/0.99  ------ General
% 3.68/0.99  
% 3.68/0.99  abstr_ref_over_cycles:                  0
% 3.68/0.99  abstr_ref_under_cycles:                 0
% 3.68/0.99  gc_basic_clause_elim:                   0
% 3.68/0.99  forced_gc_time:                         0
% 3.68/0.99  parsing_time:                           0.01
% 3.68/0.99  unif_index_cands_time:                  0.
% 3.68/0.99  unif_index_add_time:                    0.
% 3.68/0.99  orderings_time:                         0.
% 3.68/0.99  out_proof_time:                         0.016
% 3.68/0.99  total_time:                             0.307
% 3.68/0.99  num_of_symbols:                         62
% 3.68/0.99  num_of_terms:                           8032
% 3.68/0.99  
% 3.68/0.99  ------ Preprocessing
% 3.68/0.99  
% 3.68/0.99  num_of_splits:                          1
% 3.68/0.99  num_of_split_atoms:                     1
% 3.68/0.99  num_of_reused_defs:                     0
% 3.68/0.99  num_eq_ax_congr_red:                    19
% 3.68/0.99  num_of_sem_filtered_clauses:            2
% 3.68/0.99  num_of_subtypes:                        5
% 3.68/0.99  monotx_restored_types:                  1
% 3.68/0.99  sat_num_of_epr_types:                   0
% 3.68/0.99  sat_num_of_non_cyclic_types:            0
% 3.68/0.99  sat_guarded_non_collapsed_types:        1
% 3.68/0.99  num_pure_diseq_elim:                    0
% 3.68/0.99  simp_replaced_by:                       0
% 3.68/0.99  res_preprocessed:                       167
% 3.68/0.99  prep_upred:                             0
% 3.68/0.99  prep_unflattend:                        11
% 3.68/0.99  smt_new_axioms:                         0
% 3.68/0.99  pred_elim_cands:                        5
% 3.68/0.99  pred_elim:                              6
% 3.68/0.99  pred_elim_cl:                           7
% 3.68/0.99  pred_elim_cycles:                       9
% 3.68/0.99  merged_defs:                            0
% 3.68/0.99  merged_defs_ncl:                        0
% 3.68/0.99  bin_hyper_res:                          0
% 3.68/0.99  prep_cycles:                            4
% 3.68/0.99  pred_elim_time:                         0.005
% 3.68/0.99  splitting_time:                         0.
% 3.68/0.99  sem_filter_time:                        0.
% 3.68/0.99  monotx_time:                            0.001
% 3.68/0.99  subtype_inf_time:                       0.002
% 3.68/0.99  
% 3.68/0.99  ------ Problem properties
% 3.68/0.99  
% 3.68/0.99  clauses:                                30
% 3.68/0.99  conjectures:                            5
% 3.68/0.99  epr:                                    2
% 3.68/0.99  horn:                                   30
% 3.68/0.99  ground:                                 8
% 3.68/0.99  unary:                                  8
% 3.68/0.99  binary:                                 3
% 3.68/0.99  lits:                                   98
% 3.68/0.99  lits_eq:                                21
% 3.68/0.99  fd_pure:                                0
% 3.68/0.99  fd_pseudo:                              0
% 3.68/0.99  fd_cond:                                0
% 3.68/0.99  fd_pseudo_cond:                         2
% 3.68/0.99  ac_symbols:                             0
% 3.68/0.99  
% 3.68/0.99  ------ Propositional Solver
% 3.68/0.99  
% 3.68/0.99  prop_solver_calls:                      33
% 3.68/0.99  prop_fast_solver_calls:                 1502
% 3.68/0.99  smt_solver_calls:                       0
% 3.68/0.99  smt_fast_solver_calls:                  0
% 3.68/0.99  prop_num_of_clauses:                    3317
% 3.68/0.99  prop_preprocess_simplified:             8886
% 3.68/0.99  prop_fo_subsumed:                       89
% 3.68/0.99  prop_solver_time:                       0.
% 3.68/0.99  smt_solver_time:                        0.
% 3.68/0.99  smt_fast_solver_time:                   0.
% 3.68/0.99  prop_fast_solver_time:                  0.
% 3.68/0.99  prop_unsat_core_time:                   0.
% 3.68/0.99  
% 3.68/0.99  ------ QBF
% 3.68/0.99  
% 3.68/0.99  qbf_q_res:                              0
% 3.68/0.99  qbf_num_tautologies:                    0
% 3.68/0.99  qbf_prep_cycles:                        0
% 3.68/0.99  
% 3.68/0.99  ------ BMC1
% 3.68/0.99  
% 3.68/0.99  bmc1_current_bound:                     -1
% 3.68/0.99  bmc1_last_solved_bound:                 -1
% 3.68/0.99  bmc1_unsat_core_size:                   -1
% 3.68/0.99  bmc1_unsat_core_parents_size:           -1
% 3.68/0.99  bmc1_merge_next_fun:                    0
% 3.68/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.68/0.99  
% 3.68/0.99  ------ Instantiation
% 3.68/0.99  
% 3.68/0.99  inst_num_of_clauses:                    1161
% 3.68/0.99  inst_num_in_passive:                    253
% 3.68/0.99  inst_num_in_active:                     505
% 3.68/0.99  inst_num_in_unprocessed:                405
% 3.68/0.99  inst_num_of_loops:                      550
% 3.68/0.99  inst_num_of_learning_restarts:          0
% 3.68/0.99  inst_num_moves_active_passive:          39
% 3.68/0.99  inst_lit_activity:                      0
% 3.68/0.99  inst_lit_activity_moves:                0
% 3.68/0.99  inst_num_tautologies:                   0
% 3.68/0.99  inst_num_prop_implied:                  0
% 3.68/0.99  inst_num_existing_simplified:           0
% 3.68/0.99  inst_num_eq_res_simplified:             0
% 3.68/0.99  inst_num_child_elim:                    0
% 3.68/0.99  inst_num_of_dismatching_blockings:      835
% 3.68/0.99  inst_num_of_non_proper_insts:           1433
% 3.68/0.99  inst_num_of_duplicates:                 0
% 3.68/0.99  inst_inst_num_from_inst_to_res:         0
% 3.68/0.99  inst_dismatching_checking_time:         0.
% 3.68/0.99  
% 3.68/0.99  ------ Resolution
% 3.68/0.99  
% 3.68/0.99  res_num_of_clauses:                     0
% 3.68/0.99  res_num_in_passive:                     0
% 3.68/0.99  res_num_in_active:                      0
% 3.68/0.99  res_num_of_loops:                       171
% 3.68/0.99  res_forward_subset_subsumed:            111
% 3.68/0.99  res_backward_subset_subsumed:           10
% 3.68/0.99  res_forward_subsumed:                   0
% 3.68/0.99  res_backward_subsumed:                  0
% 3.68/0.99  res_forward_subsumption_resolution:     1
% 3.68/0.99  res_backward_subsumption_resolution:    0
% 3.68/0.99  res_clause_to_clause_subsumption:       359
% 3.68/0.99  res_orphan_elimination:                 0
% 3.68/0.99  res_tautology_del:                      105
% 3.68/0.99  res_num_eq_res_simplified:              0
% 3.68/0.99  res_num_sel_changes:                    0
% 3.68/0.99  res_moves_from_active_to_pass:          0
% 3.68/0.99  
% 3.68/0.99  ------ Superposition
% 3.68/0.99  
% 3.68/0.99  sup_time_total:                         0.
% 3.68/0.99  sup_time_generating:                    0.
% 3.68/0.99  sup_time_sim_full:                      0.
% 3.68/0.99  sup_time_sim_immed:                     0.
% 3.68/0.99  
% 3.68/0.99  sup_num_of_clauses:                     94
% 3.68/0.99  sup_num_in_active:                      78
% 3.68/0.99  sup_num_in_passive:                     16
% 3.68/0.99  sup_num_of_loops:                       108
% 3.68/0.99  sup_fw_superposition:                   86
% 3.68/0.99  sup_bw_superposition:                   80
% 3.68/0.99  sup_immediate_simplified:               85
% 3.68/0.99  sup_given_eliminated:                   0
% 3.68/0.99  comparisons_done:                       0
% 3.68/0.99  comparisons_avoided:                    0
% 3.68/0.99  
% 3.68/0.99  ------ Simplifications
% 3.68/0.99  
% 3.68/0.99  
% 3.68/0.99  sim_fw_subset_subsumed:                 8
% 3.68/0.99  sim_bw_subset_subsumed:                 4
% 3.68/0.99  sim_fw_subsumed:                        22
% 3.68/0.99  sim_bw_subsumed:                        1
% 3.68/0.99  sim_fw_subsumption_res:                 0
% 3.68/0.99  sim_bw_subsumption_res:                 0
% 3.68/0.99  sim_tautology_del:                      5
% 3.68/0.99  sim_eq_tautology_del:                   30
% 3.68/0.99  sim_eq_res_simp:                        2
% 3.68/0.99  sim_fw_demodulated:                     15
% 3.68/0.99  sim_bw_demodulated:                     32
% 3.68/0.99  sim_light_normalised:                   64
% 3.68/0.99  sim_joinable_taut:                      0
% 3.68/0.99  sim_joinable_simp:                      0
% 3.68/0.99  sim_ac_normalised:                      0
% 3.68/0.99  sim_smt_subsumption:                    0
% 3.68/0.99  
%------------------------------------------------------------------------------
