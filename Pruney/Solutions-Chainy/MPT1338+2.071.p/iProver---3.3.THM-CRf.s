%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:14 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :  247 (3977 expanded)
%              Number of clauses        :  166 (1296 expanded)
%              Number of leaves         :   25 (1109 expanded)
%              Depth                    :   21
%              Number of atoms          :  751 (27152 expanded)
%              Number of equality atoms :  311 (9149 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   3 average)
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
               => ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                  & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ) ) ) ),
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
                 => ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                    & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
            | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0)
          | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1) )
        & v2_funct_1(sK2)
        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1)
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0)
              | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1) )
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_struct_0(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
                  | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
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
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) )
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f53,f58,f57,f56])).

fof(f92,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f59])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f84,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f87,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f89,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f93,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f18,axiom,(
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

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f94,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f90,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f91,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f59])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f41])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f88,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f66,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f70,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f61,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f95,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1005,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1539,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1005])).

cnf(c_24,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_35,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_400,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_35])).

cnf(c_401,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_1000,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_401])).

cnf(c_33,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_395,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_33])).

cnf(c_396,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_1001,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_396])).

cnf(c_1572,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1539,c_1000,c_1001])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1009,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | k2_relset_1(X0_57,X1_57,X0_56) = k2_relat_1(X0_56) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1537,plain,
    ( k2_relset_1(X0_57,X1_57,X0_56) = k2_relat_1(X0_56)
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1009])).

cnf(c_2623,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1572,c_1537])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1006,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1569,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_1006,c_1000,c_1001])).

cnf(c_2734,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2623,c_1569])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_28,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_674,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_675,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_674])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_679,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_675,c_32])).

cnf(c_680,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_679])).

cnf(c_995,plain,
    ( ~ v1_funct_2(sK2,X0_57,X1_57)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_57,X0_57)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | k2_relset_1(X0_57,X1_57,sK2) != X1_57 ),
    inference(subtyping,[status(esa)],[c_680])).

cnf(c_1547,plain,
    ( k2_relset_1(X0_57,X1_57,sK2) != X1_57
    | v1_funct_2(sK2,X0_57,X1_57) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_57,X0_57))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_995])).

cnf(c_2303,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1569,c_1547])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1004,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1540,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1004])).

cnf(c_1562,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1540,c_1000,c_1001])).

cnf(c_2306,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2303,c_1562,c_1572])).

cnf(c_2778,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2734,c_2306])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_20,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_501,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_17,c_20])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_505,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_501,c_12])).

cnf(c_999,plain,
    ( ~ v1_funct_2(X0_56,X0_57,X1_57)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(X0_56)
    | ~ v1_relat_1(X0_56)
    | v1_xboole_0(X1_57)
    | k1_relat_1(X0_56) = X0_57 ),
    inference(subtyping,[status(esa)],[c_505])).

cnf(c_1543,plain,
    ( k1_relat_1(X0_56) = X0_57
    | v1_funct_2(X0_56,X0_57,X1_57) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_relat_1(X0_56) != iProver_top
    | v1_xboole_0(X1_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_999])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1018,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_57,X1_57)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1063,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_57,X1_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1018])).

cnf(c_1100,plain,
    ( k1_relat_1(X0_56) = X0_57
    | v1_funct_2(X0_56,X0_57,X1_57) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_relat_1(X0_56) != iProver_top
    | v1_xboole_0(X1_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_999])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1019,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(X1_56))
    | ~ v1_relat_1(X1_56)
    | v1_relat_1(X0_56) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1798,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | v1_relat_1(X0_56)
    | ~ v1_relat_1(k2_zfmisc_1(X0_57,X1_57)) ),
    inference(instantiation,[status(thm)],[c_1019])).

cnf(c_1799,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v1_relat_1(X0_56) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0_57,X1_57)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1798])).

cnf(c_3038,plain,
    ( v1_funct_1(X0_56) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v1_funct_2(X0_56,X0_57,X1_57) != iProver_top
    | k1_relat_1(X0_56) = X0_57
    | v1_xboole_0(X1_57) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1543,c_1063,c_1100,c_1799])).

cnf(c_3039,plain,
    ( k1_relat_1(X0_56) = X0_57
    | v1_funct_2(X0_56,X0_57,X1_57) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_xboole_0(X1_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_3038])).

cnf(c_3536,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2778,c_3039])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_25,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_47,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1014,plain,
    ( ~ v1_relat_1(X0_56)
    | k2_relat_1(X0_56) = k1_xboole_0
    | k1_relat_1(X0_56) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1076,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1014])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1013,plain,
    ( ~ v1_funct_1(X0_56)
    | v1_funct_1(k2_funct_1(X0_56))
    | ~ v1_relat_1(X0_56) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1079,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1013])).

cnf(c_1859,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1798])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1020,plain,
    ( ~ v1_xboole_0(X0_57)
    | k1_xboole_0 = X0_57 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1902,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1020])).

cnf(c_1938,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1018])).

cnf(c_1024,plain,
    ( X0_57 = X0_57 ),
    theory(equality)).

cnf(c_2103,plain,
    ( k2_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1024])).

cnf(c_1028,plain,
    ( ~ v1_xboole_0(X0_57)
    | v1_xboole_0(X1_57)
    | X1_57 != X0_57 ),
    theory(equality)).

cnf(c_1974,plain,
    ( ~ v1_xboole_0(X0_57)
    | v1_xboole_0(u1_struct_0(sK0))
    | u1_struct_0(sK0) != X0_57 ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_2208,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(k2_struct_0(sK0))
    | u1_struct_0(sK0) != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1974])).

cnf(c_1027,plain,
    ( X0_57 != X1_57
    | X2_57 != X1_57
    | X2_57 = X0_57 ),
    theory(equality)).

cnf(c_1916,plain,
    ( X0_57 != X1_57
    | k2_struct_0(sK1) != X1_57
    | k2_struct_0(sK1) = X0_57 ),
    inference(instantiation,[status(thm)],[c_1027])).

cnf(c_2102,plain,
    ( X0_57 != k2_struct_0(sK1)
    | k2_struct_0(sK1) = X0_57
    | k2_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1916])).

cnf(c_2383,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK1) = u1_struct_0(sK1)
    | k2_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2102])).

cnf(c_1788,plain,
    ( ~ v1_xboole_0(X0_57)
    | v1_xboole_0(k2_struct_0(sK1))
    | k2_struct_0(sK1) != X0_57 ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_2492,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(k2_struct_0(sK1))
    | k2_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1788])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_650,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_28])).

cnf(c_651,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(unflattening,[status(thm)],[c_650])).

cnf(c_655,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X1,X0)
    | v1_funct_2(k2_funct_1(sK2),X0,X1)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_651,c_32])).

cnf(c_656,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(renaming,[status(thm)],[c_655])).

cnf(c_996,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0_57,X1_57)
    | ~ v1_funct_2(sK2,X1_57,X0_57)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1_57,X0_57)))
    | k2_relset_1(X1_57,X0_57,sK2) != X0_57 ),
    inference(subtyping,[status(esa)],[c_656])).

cnf(c_1546,plain,
    ( k2_relset_1(X0_57,X1_57,sK2) != X1_57
    | v1_funct_2(k2_funct_1(sK2),X1_57,X0_57) = iProver_top
    | v1_funct_2(sK2,X0_57,X1_57) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_996])).

cnf(c_2100,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1569,c_1546])).

cnf(c_2116,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2100,c_1562,c_1572])).

cnf(c_2779,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2734,c_2116])).

cnf(c_2809,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2779])).

cnf(c_382,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_34])).

cnf(c_383,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_385,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_383,c_34,c_33,c_47])).

cnf(c_1002,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_385])).

cnf(c_1542,plain,
    ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1002])).

cnf(c_2784,plain,
    ( v1_xboole_0(k2_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2734,c_1542])).

cnf(c_2812,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2784])).

cnf(c_2196,plain,
    ( ~ v1_funct_2(X0_56,X0_57,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_56)
    | ~ v1_relat_1(X0_56)
    | v1_xboole_0(u1_struct_0(sK1))
    | k1_relat_1(X0_56) = X0_57 ),
    inference(instantiation,[status(thm)],[c_999])).

cnf(c_2839,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | v1_xboole_0(u1_struct_0(sK1))
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2196])).

cnf(c_2114,plain,
    ( k1_relat_1(X0_56) != X0_57
    | k1_relat_1(X0_56) = k1_xboole_0
    | k1_xboole_0 != X0_57 ),
    inference(instantiation,[status(thm)],[c_1027])).

cnf(c_3002,plain,
    ( k1_relat_1(sK2) != u1_struct_0(sK0)
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2114])).

cnf(c_3549,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | v1_xboole_0(k2_struct_0(sK0))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3536])).

cnf(c_3639,plain,
    ( ~ v1_xboole_0(X0_57)
    | v1_xboole_0(k2_relat_1(sK2))
    | k2_relat_1(sK2) != X0_57 ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_3641,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_relat_1(sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3639])).

cnf(c_5620,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3536,c_34,c_33,c_32,c_31,c_30,c_47,c_0,c_1076,c_1079,c_1001,c_1000,c_1859,c_1902,c_1938,c_2103,c_2208,c_2383,c_2492,c_2809,c_2812,c_2839,c_3002,c_3549,c_3641])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_698,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_28])).

cnf(c_699,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_698])).

cnf(c_703,plain,
    ( ~ v1_relat_1(sK2)
    | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_699,c_32])).

cnf(c_994,plain,
    ( ~ v1_relat_1(sK2)
    | k9_relat_1(k2_funct_1(sK2),X0_57) = k10_relat_1(sK2,X0_57) ),
    inference(subtyping,[status(esa)],[c_703])).

cnf(c_1548,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0_57) = k10_relat_1(sK2,X0_57)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_994])).

cnf(c_1985,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0_57) = k10_relat_1(sK2,X0_57) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1548,c_30,c_994,c_1859,c_1938])).

cnf(c_1527,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(X1_56)) != iProver_top
    | v1_relat_1(X1_56) != iProver_top
    | v1_relat_1(X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1019])).

cnf(c_2311,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2306,c_1527])).

cnf(c_39,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1012,plain,
    ( ~ v1_funct_1(X0_56)
    | ~ v1_relat_1(X0_56)
    | v1_relat_1(k2_funct_1(X0_56)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1081,plain,
    ( v1_funct_1(X0_56) != iProver_top
    | v1_relat_1(X0_56) != iProver_top
    | v1_relat_1(k2_funct_1(X0_56)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1012])).

cnf(c_1083,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1081])).

cnf(c_1860,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1859])).

cnf(c_1939,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1938])).

cnf(c_2405,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2311,c_39,c_41,c_1083,c_1860,c_1939])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1017,plain,
    ( ~ v1_relat_1(X0_56)
    | k9_relat_1(X0_56,k1_relat_1(X0_56)) = k2_relat_1(X0_56) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1529,plain,
    ( k9_relat_1(X0_56,k1_relat_1(X0_56)) = k2_relat_1(X0_56)
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1017])).

cnf(c_2411,plain,
    ( k9_relat_1(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2))) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2405,c_1529])).

cnf(c_3050,plain,
    ( k10_relat_1(sK2,k1_relat_1(k2_funct_1(sK2))) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_1985,c_2411])).

cnf(c_5624,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(demodulation,[status(thm)],[c_5620,c_3050])).

cnf(c_1846,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1572,c_1527])).

cnf(c_2360,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1846,c_41,c_1860,c_1939])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1016,plain,
    ( ~ v1_relat_1(X0_56)
    | k10_relat_1(X0_56,k2_relat_1(X0_56)) = k1_relat_1(X0_56) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1530,plain,
    ( k10_relat_1(X0_56,k2_relat_1(X0_56)) = k1_relat_1(X0_56)
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1016])).

cnf(c_2366,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2360,c_1530])).

cnf(c_5632,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_5624,c_2366])).

cnf(c_2782,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2734,c_1572])).

cnf(c_3517,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_xboole_0(k2_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2782,c_3039])).

cnf(c_2783,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2734,c_1562])).

cnf(c_4187,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3517,c_39,c_2783,c_2784])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_602,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_28])).

cnf(c_603,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_602])).

cnf(c_607,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_603,c_32])).

cnf(c_608,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_607])).

cnf(c_998,plain,
    ( ~ v1_funct_2(sK2,X0_57,X1_57)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | k2_relset_1(X0_57,X1_57,sK2) != X1_57
    | k2_tops_2(X0_57,X1_57,sK2) = k2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_608])).

cnf(c_1544,plain,
    ( k2_relset_1(X0_57,X1_57,sK2) != X1_57
    | k2_tops_2(X0_57,X1_57,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,X0_57,X1_57) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_998])).

cnf(c_2027,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1569,c_1544])).

cnf(c_2030,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2027,c_1562,c_1572])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1007,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1637,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_1007,c_1000,c_1001])).

cnf(c_2033,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_2030,c_1637])).

cnf(c_2780,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2734,c_2033])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1010,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | k1_relset_1(X0_57,X1_57,X0_56) = k1_relat_1(X0_56) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1536,plain,
    ( k1_relset_1(X0_57,X1_57,X0_56) = k1_relat_1(X0_56)
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1010])).

cnf(c_2529,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2306,c_1536])).

cnf(c_3088,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(light_normalisation,[status(thm)],[c_2529,c_2734])).

cnf(c_2624,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2306,c_1537])).

cnf(c_3090,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(light_normalisation,[status(thm)],[c_2624,c_2734])).

cnf(c_3632,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2780,c_3088,c_3090])).

cnf(c_4193,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4187,c_3632])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5632,c_4193,c_3641,c_3549,c_3002,c_2839,c_2812,c_2809,c_2492,c_2383,c_2208,c_2103,c_1938,c_1902,c_1859,c_1000,c_1001,c_1079,c_1076,c_0,c_47,c_30,c_31,c_32,c_33,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:40:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.87/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/0.99  
% 2.87/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.87/0.99  
% 2.87/0.99  ------  iProver source info
% 2.87/0.99  
% 2.87/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.87/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.87/0.99  git: non_committed_changes: false
% 2.87/0.99  git: last_make_outside_of_git: false
% 2.87/0.99  
% 2.87/0.99  ------ 
% 2.87/0.99  
% 2.87/0.99  ------ Input Options
% 2.87/0.99  
% 2.87/0.99  --out_options                           all
% 2.87/0.99  --tptp_safe_out                         true
% 2.87/0.99  --problem_path                          ""
% 2.87/0.99  --include_path                          ""
% 2.87/0.99  --clausifier                            res/vclausify_rel
% 2.87/0.99  --clausifier_options                    --mode clausify
% 2.87/0.99  --stdin                                 false
% 2.87/0.99  --stats_out                             all
% 2.87/0.99  
% 2.87/0.99  ------ General Options
% 2.87/0.99  
% 2.87/0.99  --fof                                   false
% 2.87/0.99  --time_out_real                         305.
% 2.87/0.99  --time_out_virtual                      -1.
% 2.87/0.99  --symbol_type_check                     false
% 2.87/0.99  --clausify_out                          false
% 2.87/0.99  --sig_cnt_out                           false
% 2.87/0.99  --trig_cnt_out                          false
% 2.87/0.99  --trig_cnt_out_tolerance                1.
% 2.87/0.99  --trig_cnt_out_sk_spl                   false
% 2.87/0.99  --abstr_cl_out                          false
% 2.87/0.99  
% 2.87/0.99  ------ Global Options
% 2.87/0.99  
% 2.87/0.99  --schedule                              default
% 2.87/0.99  --add_important_lit                     false
% 2.87/0.99  --prop_solver_per_cl                    1000
% 2.87/0.99  --min_unsat_core                        false
% 2.87/0.99  --soft_assumptions                      false
% 2.87/0.99  --soft_lemma_size                       3
% 2.87/0.99  --prop_impl_unit_size                   0
% 2.87/0.99  --prop_impl_unit                        []
% 2.87/0.99  --share_sel_clauses                     true
% 2.87/0.99  --reset_solvers                         false
% 2.87/0.99  --bc_imp_inh                            [conj_cone]
% 2.87/0.99  --conj_cone_tolerance                   3.
% 2.87/0.99  --extra_neg_conj                        none
% 2.87/0.99  --large_theory_mode                     true
% 2.87/0.99  --prolific_symb_bound                   200
% 2.87/0.99  --lt_threshold                          2000
% 2.87/0.99  --clause_weak_htbl                      true
% 2.87/0.99  --gc_record_bc_elim                     false
% 2.87/0.99  
% 2.87/0.99  ------ Preprocessing Options
% 2.87/0.99  
% 2.87/0.99  --preprocessing_flag                    true
% 2.87/0.99  --time_out_prep_mult                    0.1
% 2.87/0.99  --splitting_mode                        input
% 2.87/0.99  --splitting_grd                         true
% 2.87/0.99  --splitting_cvd                         false
% 2.87/0.99  --splitting_cvd_svl                     false
% 2.87/0.99  --splitting_nvd                         32
% 2.87/0.99  --sub_typing                            true
% 2.87/0.99  --prep_gs_sim                           true
% 2.87/0.99  --prep_unflatten                        true
% 2.87/0.99  --prep_res_sim                          true
% 2.87/0.99  --prep_upred                            true
% 2.87/0.99  --prep_sem_filter                       exhaustive
% 2.87/0.99  --prep_sem_filter_out                   false
% 2.87/0.99  --pred_elim                             true
% 2.87/0.99  --res_sim_input                         true
% 2.87/0.99  --eq_ax_congr_red                       true
% 2.87/0.99  --pure_diseq_elim                       true
% 2.87/0.99  --brand_transform                       false
% 2.87/0.99  --non_eq_to_eq                          false
% 2.87/0.99  --prep_def_merge                        true
% 2.87/0.99  --prep_def_merge_prop_impl              false
% 2.87/0.99  --prep_def_merge_mbd                    true
% 2.87/0.99  --prep_def_merge_tr_red                 false
% 2.87/0.99  --prep_def_merge_tr_cl                  false
% 2.87/0.99  --smt_preprocessing                     true
% 2.87/0.99  --smt_ac_axioms                         fast
% 2.87/0.99  --preprocessed_out                      false
% 2.87/0.99  --preprocessed_stats                    false
% 2.87/0.99  
% 2.87/0.99  ------ Abstraction refinement Options
% 2.87/0.99  
% 2.87/0.99  --abstr_ref                             []
% 2.87/0.99  --abstr_ref_prep                        false
% 2.87/0.99  --abstr_ref_until_sat                   false
% 2.87/0.99  --abstr_ref_sig_restrict                funpre
% 2.87/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.87/0.99  --abstr_ref_under                       []
% 2.87/0.99  
% 2.87/0.99  ------ SAT Options
% 2.87/0.99  
% 2.87/0.99  --sat_mode                              false
% 2.87/0.99  --sat_fm_restart_options                ""
% 2.87/0.99  --sat_gr_def                            false
% 2.87/0.99  --sat_epr_types                         true
% 2.87/0.99  --sat_non_cyclic_types                  false
% 2.87/0.99  --sat_finite_models                     false
% 2.87/0.99  --sat_fm_lemmas                         false
% 2.87/0.99  --sat_fm_prep                           false
% 2.87/0.99  --sat_fm_uc_incr                        true
% 2.87/0.99  --sat_out_model                         small
% 2.87/0.99  --sat_out_clauses                       false
% 2.87/0.99  
% 2.87/0.99  ------ QBF Options
% 2.87/0.99  
% 2.87/0.99  --qbf_mode                              false
% 2.87/0.99  --qbf_elim_univ                         false
% 2.87/0.99  --qbf_dom_inst                          none
% 2.87/0.99  --qbf_dom_pre_inst                      false
% 2.87/0.99  --qbf_sk_in                             false
% 2.87/0.99  --qbf_pred_elim                         true
% 2.87/0.99  --qbf_split                             512
% 2.87/0.99  
% 2.87/0.99  ------ BMC1 Options
% 2.87/0.99  
% 2.87/0.99  --bmc1_incremental                      false
% 2.87/0.99  --bmc1_axioms                           reachable_all
% 2.87/0.99  --bmc1_min_bound                        0
% 2.87/0.99  --bmc1_max_bound                        -1
% 2.87/0.99  --bmc1_max_bound_default                -1
% 2.87/0.99  --bmc1_symbol_reachability              true
% 2.87/0.99  --bmc1_property_lemmas                  false
% 2.87/0.99  --bmc1_k_induction                      false
% 2.87/0.99  --bmc1_non_equiv_states                 false
% 2.87/0.99  --bmc1_deadlock                         false
% 2.87/0.99  --bmc1_ucm                              false
% 2.87/0.99  --bmc1_add_unsat_core                   none
% 2.87/0.99  --bmc1_unsat_core_children              false
% 2.87/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.87/0.99  --bmc1_out_stat                         full
% 2.87/0.99  --bmc1_ground_init                      false
% 2.87/0.99  --bmc1_pre_inst_next_state              false
% 2.87/0.99  --bmc1_pre_inst_state                   false
% 2.87/0.99  --bmc1_pre_inst_reach_state             false
% 2.87/0.99  --bmc1_out_unsat_core                   false
% 2.87/0.99  --bmc1_aig_witness_out                  false
% 2.87/0.99  --bmc1_verbose                          false
% 2.87/0.99  --bmc1_dump_clauses_tptp                false
% 2.87/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.87/0.99  --bmc1_dump_file                        -
% 2.87/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.87/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.87/0.99  --bmc1_ucm_extend_mode                  1
% 2.87/0.99  --bmc1_ucm_init_mode                    2
% 2.87/0.99  --bmc1_ucm_cone_mode                    none
% 2.87/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.87/0.99  --bmc1_ucm_relax_model                  4
% 2.87/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.87/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.87/0.99  --bmc1_ucm_layered_model                none
% 2.87/0.99  --bmc1_ucm_max_lemma_size               10
% 2.87/0.99  
% 2.87/0.99  ------ AIG Options
% 2.87/0.99  
% 2.87/0.99  --aig_mode                              false
% 2.87/0.99  
% 2.87/0.99  ------ Instantiation Options
% 2.87/0.99  
% 2.87/0.99  --instantiation_flag                    true
% 2.87/0.99  --inst_sos_flag                         false
% 2.87/0.99  --inst_sos_phase                        true
% 2.87/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.87/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.87/0.99  --inst_lit_sel_side                     num_symb
% 2.87/0.99  --inst_solver_per_active                1400
% 2.87/0.99  --inst_solver_calls_frac                1.
% 2.87/0.99  --inst_passive_queue_type               priority_queues
% 2.87/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.87/0.99  --inst_passive_queues_freq              [25;2]
% 2.87/0.99  --inst_dismatching                      true
% 2.87/0.99  --inst_eager_unprocessed_to_passive     true
% 2.87/0.99  --inst_prop_sim_given                   true
% 2.87/0.99  --inst_prop_sim_new                     false
% 2.87/0.99  --inst_subs_new                         false
% 2.87/0.99  --inst_eq_res_simp                      false
% 2.87/0.99  --inst_subs_given                       false
% 2.87/0.99  --inst_orphan_elimination               true
% 2.87/0.99  --inst_learning_loop_flag               true
% 2.87/0.99  --inst_learning_start                   3000
% 2.87/0.99  --inst_learning_factor                  2
% 2.87/0.99  --inst_start_prop_sim_after_learn       3
% 2.87/0.99  --inst_sel_renew                        solver
% 2.87/0.99  --inst_lit_activity_flag                true
% 2.87/0.99  --inst_restr_to_given                   false
% 2.87/0.99  --inst_activity_threshold               500
% 2.87/0.99  --inst_out_proof                        true
% 2.87/0.99  
% 2.87/0.99  ------ Resolution Options
% 2.87/0.99  
% 2.87/0.99  --resolution_flag                       true
% 2.87/0.99  --res_lit_sel                           adaptive
% 2.87/0.99  --res_lit_sel_side                      none
% 2.87/0.99  --res_ordering                          kbo
% 2.87/0.99  --res_to_prop_solver                    active
% 2.87/0.99  --res_prop_simpl_new                    false
% 2.87/0.99  --res_prop_simpl_given                  true
% 2.87/0.99  --res_passive_queue_type                priority_queues
% 2.87/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.87/0.99  --res_passive_queues_freq               [15;5]
% 2.87/0.99  --res_forward_subs                      full
% 2.87/0.99  --res_backward_subs                     full
% 2.87/0.99  --res_forward_subs_resolution           true
% 2.87/0.99  --res_backward_subs_resolution          true
% 2.87/0.99  --res_orphan_elimination                true
% 2.87/0.99  --res_time_limit                        2.
% 2.87/0.99  --res_out_proof                         true
% 2.87/0.99  
% 2.87/0.99  ------ Superposition Options
% 2.87/0.99  
% 2.87/0.99  --superposition_flag                    true
% 2.87/0.99  --sup_passive_queue_type                priority_queues
% 2.87/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.87/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.87/0.99  --demod_completeness_check              fast
% 2.87/0.99  --demod_use_ground                      true
% 2.87/0.99  --sup_to_prop_solver                    passive
% 2.87/0.99  --sup_prop_simpl_new                    true
% 2.87/0.99  --sup_prop_simpl_given                  true
% 2.87/0.99  --sup_fun_splitting                     false
% 2.87/0.99  --sup_smt_interval                      50000
% 2.87/0.99  
% 2.87/0.99  ------ Superposition Simplification Setup
% 2.87/0.99  
% 2.87/0.99  --sup_indices_passive                   []
% 2.87/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.87/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.99  --sup_full_bw                           [BwDemod]
% 2.87/0.99  --sup_immed_triv                        [TrivRules]
% 2.87/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.87/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.99  --sup_immed_bw_main                     []
% 2.87/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.87/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/0.99  
% 2.87/0.99  ------ Combination Options
% 2.87/0.99  
% 2.87/0.99  --comb_res_mult                         3
% 2.87/0.99  --comb_sup_mult                         2
% 2.87/0.99  --comb_inst_mult                        10
% 2.87/0.99  
% 2.87/0.99  ------ Debug Options
% 2.87/0.99  
% 2.87/0.99  --dbg_backtrace                         false
% 2.87/0.99  --dbg_dump_prop_clauses                 false
% 2.87/0.99  --dbg_dump_prop_clauses_file            -
% 2.87/0.99  --dbg_out_stat                          false
% 2.87/0.99  ------ Parsing...
% 2.87/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.87/0.99  
% 2.87/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.87/0.99  
% 2.87/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.87/0.99  
% 2.87/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.87/0.99  ------ Proving...
% 2.87/0.99  ------ Problem Properties 
% 2.87/0.99  
% 2.87/0.99  
% 2.87/0.99  clauses                                 29
% 2.87/0.99  conjectures                             5
% 2.87/0.99  EPR                                     3
% 2.87/0.99  Horn                                    28
% 2.87/0.99  unary                                   9
% 2.87/0.99  binary                                  10
% 2.87/0.99  lits                                    66
% 2.87/0.99  lits eq                                 23
% 2.87/0.99  fd_pure                                 0
% 2.87/0.99  fd_pseudo                               0
% 2.87/0.99  fd_cond                                 1
% 2.87/0.99  fd_pseudo_cond                          1
% 2.87/0.99  AC symbols                              0
% 2.87/0.99  
% 2.87/0.99  ------ Schedule dynamic 5 is on 
% 2.87/0.99  
% 2.87/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.87/0.99  
% 2.87/0.99  
% 2.87/0.99  ------ 
% 2.87/0.99  Current options:
% 2.87/0.99  ------ 
% 2.87/0.99  
% 2.87/0.99  ------ Input Options
% 2.87/0.99  
% 2.87/0.99  --out_options                           all
% 2.87/0.99  --tptp_safe_out                         true
% 2.87/0.99  --problem_path                          ""
% 2.87/0.99  --include_path                          ""
% 2.87/0.99  --clausifier                            res/vclausify_rel
% 2.87/0.99  --clausifier_options                    --mode clausify
% 2.87/0.99  --stdin                                 false
% 2.87/0.99  --stats_out                             all
% 2.87/0.99  
% 2.87/0.99  ------ General Options
% 2.87/0.99  
% 2.87/0.99  --fof                                   false
% 2.87/0.99  --time_out_real                         305.
% 2.87/0.99  --time_out_virtual                      -1.
% 2.87/0.99  --symbol_type_check                     false
% 2.87/0.99  --clausify_out                          false
% 2.87/0.99  --sig_cnt_out                           false
% 2.87/0.99  --trig_cnt_out                          false
% 2.87/0.99  --trig_cnt_out_tolerance                1.
% 2.87/0.99  --trig_cnt_out_sk_spl                   false
% 2.87/0.99  --abstr_cl_out                          false
% 2.87/0.99  
% 2.87/0.99  ------ Global Options
% 2.87/0.99  
% 2.87/0.99  --schedule                              default
% 2.87/0.99  --add_important_lit                     false
% 2.87/0.99  --prop_solver_per_cl                    1000
% 2.87/0.99  --min_unsat_core                        false
% 2.87/0.99  --soft_assumptions                      false
% 2.87/0.99  --soft_lemma_size                       3
% 2.87/0.99  --prop_impl_unit_size                   0
% 2.87/0.99  --prop_impl_unit                        []
% 2.87/0.99  --share_sel_clauses                     true
% 2.87/0.99  --reset_solvers                         false
% 2.87/0.99  --bc_imp_inh                            [conj_cone]
% 2.87/0.99  --conj_cone_tolerance                   3.
% 2.87/0.99  --extra_neg_conj                        none
% 2.87/0.99  --large_theory_mode                     true
% 2.87/0.99  --prolific_symb_bound                   200
% 2.87/0.99  --lt_threshold                          2000
% 2.87/0.99  --clause_weak_htbl                      true
% 2.87/0.99  --gc_record_bc_elim                     false
% 2.87/0.99  
% 2.87/0.99  ------ Preprocessing Options
% 2.87/0.99  
% 2.87/0.99  --preprocessing_flag                    true
% 2.87/0.99  --time_out_prep_mult                    0.1
% 2.87/0.99  --splitting_mode                        input
% 2.87/0.99  --splitting_grd                         true
% 2.87/0.99  --splitting_cvd                         false
% 2.87/0.99  --splitting_cvd_svl                     false
% 2.87/0.99  --splitting_nvd                         32
% 2.87/0.99  --sub_typing                            true
% 2.87/0.99  --prep_gs_sim                           true
% 2.87/0.99  --prep_unflatten                        true
% 2.87/0.99  --prep_res_sim                          true
% 2.87/0.99  --prep_upred                            true
% 2.87/0.99  --prep_sem_filter                       exhaustive
% 2.87/0.99  --prep_sem_filter_out                   false
% 2.87/0.99  --pred_elim                             true
% 2.87/0.99  --res_sim_input                         true
% 2.87/0.99  --eq_ax_congr_red                       true
% 2.87/0.99  --pure_diseq_elim                       true
% 2.87/0.99  --brand_transform                       false
% 2.87/0.99  --non_eq_to_eq                          false
% 2.87/0.99  --prep_def_merge                        true
% 2.87/0.99  --prep_def_merge_prop_impl              false
% 2.87/0.99  --prep_def_merge_mbd                    true
% 2.87/0.99  --prep_def_merge_tr_red                 false
% 2.87/0.99  --prep_def_merge_tr_cl                  false
% 2.87/0.99  --smt_preprocessing                     true
% 2.87/0.99  --smt_ac_axioms                         fast
% 2.87/0.99  --preprocessed_out                      false
% 2.87/0.99  --preprocessed_stats                    false
% 2.87/0.99  
% 2.87/0.99  ------ Abstraction refinement Options
% 2.87/0.99  
% 2.87/0.99  --abstr_ref                             []
% 2.87/0.99  --abstr_ref_prep                        false
% 2.87/0.99  --abstr_ref_until_sat                   false
% 2.87/0.99  --abstr_ref_sig_restrict                funpre
% 2.87/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.87/0.99  --abstr_ref_under                       []
% 2.87/0.99  
% 2.87/0.99  ------ SAT Options
% 2.87/0.99  
% 2.87/0.99  --sat_mode                              false
% 2.87/0.99  --sat_fm_restart_options                ""
% 2.87/0.99  --sat_gr_def                            false
% 2.87/0.99  --sat_epr_types                         true
% 2.87/0.99  --sat_non_cyclic_types                  false
% 2.87/0.99  --sat_finite_models                     false
% 2.87/0.99  --sat_fm_lemmas                         false
% 2.87/0.99  --sat_fm_prep                           false
% 2.87/0.99  --sat_fm_uc_incr                        true
% 2.87/0.99  --sat_out_model                         small
% 2.87/0.99  --sat_out_clauses                       false
% 2.87/0.99  
% 2.87/0.99  ------ QBF Options
% 2.87/0.99  
% 2.87/0.99  --qbf_mode                              false
% 2.87/0.99  --qbf_elim_univ                         false
% 2.87/0.99  --qbf_dom_inst                          none
% 2.87/0.99  --qbf_dom_pre_inst                      false
% 2.87/0.99  --qbf_sk_in                             false
% 2.87/0.99  --qbf_pred_elim                         true
% 2.87/0.99  --qbf_split                             512
% 2.87/0.99  
% 2.87/0.99  ------ BMC1 Options
% 2.87/0.99  
% 2.87/0.99  --bmc1_incremental                      false
% 2.87/0.99  --bmc1_axioms                           reachable_all
% 2.87/0.99  --bmc1_min_bound                        0
% 2.87/0.99  --bmc1_max_bound                        -1
% 2.87/0.99  --bmc1_max_bound_default                -1
% 2.87/0.99  --bmc1_symbol_reachability              true
% 2.87/0.99  --bmc1_property_lemmas                  false
% 2.87/0.99  --bmc1_k_induction                      false
% 2.87/0.99  --bmc1_non_equiv_states                 false
% 2.87/0.99  --bmc1_deadlock                         false
% 2.87/0.99  --bmc1_ucm                              false
% 2.87/0.99  --bmc1_add_unsat_core                   none
% 2.87/0.99  --bmc1_unsat_core_children              false
% 2.87/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.87/0.99  --bmc1_out_stat                         full
% 2.87/0.99  --bmc1_ground_init                      false
% 2.87/0.99  --bmc1_pre_inst_next_state              false
% 2.87/0.99  --bmc1_pre_inst_state                   false
% 2.87/0.99  --bmc1_pre_inst_reach_state             false
% 2.87/0.99  --bmc1_out_unsat_core                   false
% 2.87/0.99  --bmc1_aig_witness_out                  false
% 2.87/0.99  --bmc1_verbose                          false
% 2.87/0.99  --bmc1_dump_clauses_tptp                false
% 2.87/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.87/0.99  --bmc1_dump_file                        -
% 2.87/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.87/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.87/0.99  --bmc1_ucm_extend_mode                  1
% 2.87/0.99  --bmc1_ucm_init_mode                    2
% 2.87/0.99  --bmc1_ucm_cone_mode                    none
% 2.87/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.87/0.99  --bmc1_ucm_relax_model                  4
% 2.87/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.87/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.87/0.99  --bmc1_ucm_layered_model                none
% 2.87/0.99  --bmc1_ucm_max_lemma_size               10
% 2.87/0.99  
% 2.87/0.99  ------ AIG Options
% 2.87/0.99  
% 2.87/0.99  --aig_mode                              false
% 2.87/0.99  
% 2.87/0.99  ------ Instantiation Options
% 2.87/0.99  
% 2.87/0.99  --instantiation_flag                    true
% 2.87/0.99  --inst_sos_flag                         false
% 2.87/0.99  --inst_sos_phase                        true
% 2.87/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.87/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.87/0.99  --inst_lit_sel_side                     none
% 2.87/0.99  --inst_solver_per_active                1400
% 2.87/0.99  --inst_solver_calls_frac                1.
% 2.87/0.99  --inst_passive_queue_type               priority_queues
% 2.87/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.87/0.99  --inst_passive_queues_freq              [25;2]
% 2.87/0.99  --inst_dismatching                      true
% 2.87/0.99  --inst_eager_unprocessed_to_passive     true
% 2.87/0.99  --inst_prop_sim_given                   true
% 2.87/0.99  --inst_prop_sim_new                     false
% 2.87/0.99  --inst_subs_new                         false
% 2.87/0.99  --inst_eq_res_simp                      false
% 2.87/0.99  --inst_subs_given                       false
% 2.87/0.99  --inst_orphan_elimination               true
% 2.87/0.99  --inst_learning_loop_flag               true
% 2.87/0.99  --inst_learning_start                   3000
% 2.87/0.99  --inst_learning_factor                  2
% 2.87/0.99  --inst_start_prop_sim_after_learn       3
% 2.87/0.99  --inst_sel_renew                        solver
% 2.87/0.99  --inst_lit_activity_flag                true
% 2.87/0.99  --inst_restr_to_given                   false
% 2.87/0.99  --inst_activity_threshold               500
% 2.87/0.99  --inst_out_proof                        true
% 2.87/0.99  
% 2.87/0.99  ------ Resolution Options
% 2.87/0.99  
% 2.87/0.99  --resolution_flag                       false
% 2.87/0.99  --res_lit_sel                           adaptive
% 2.87/0.99  --res_lit_sel_side                      none
% 2.87/0.99  --res_ordering                          kbo
% 2.87/0.99  --res_to_prop_solver                    active
% 2.87/0.99  --res_prop_simpl_new                    false
% 2.87/0.99  --res_prop_simpl_given                  true
% 2.87/0.99  --res_passive_queue_type                priority_queues
% 2.87/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.87/0.99  --res_passive_queues_freq               [15;5]
% 2.87/0.99  --res_forward_subs                      full
% 2.87/0.99  --res_backward_subs                     full
% 2.87/0.99  --res_forward_subs_resolution           true
% 2.87/0.99  --res_backward_subs_resolution          true
% 2.87/0.99  --res_orphan_elimination                true
% 2.87/0.99  --res_time_limit                        2.
% 2.87/0.99  --res_out_proof                         true
% 2.87/0.99  
% 2.87/0.99  ------ Superposition Options
% 2.87/0.99  
% 2.87/0.99  --superposition_flag                    true
% 2.87/0.99  --sup_passive_queue_type                priority_queues
% 2.87/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.87/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.87/0.99  --demod_completeness_check              fast
% 2.87/0.99  --demod_use_ground                      true
% 2.87/0.99  --sup_to_prop_solver                    passive
% 2.87/0.99  --sup_prop_simpl_new                    true
% 2.87/0.99  --sup_prop_simpl_given                  true
% 2.87/0.99  --sup_fun_splitting                     false
% 2.87/0.99  --sup_smt_interval                      50000
% 2.87/0.99  
% 2.87/0.99  ------ Superposition Simplification Setup
% 2.87/0.99  
% 2.87/0.99  --sup_indices_passive                   []
% 2.87/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.87/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.99  --sup_full_bw                           [BwDemod]
% 2.87/0.99  --sup_immed_triv                        [TrivRules]
% 2.87/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.87/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.99  --sup_immed_bw_main                     []
% 2.87/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.87/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/0.99  
% 2.87/0.99  ------ Combination Options
% 2.87/0.99  
% 2.87/0.99  --comb_res_mult                         3
% 2.87/0.99  --comb_sup_mult                         2
% 2.87/0.99  --comb_inst_mult                        10
% 2.87/0.99  
% 2.87/0.99  ------ Debug Options
% 2.87/0.99  
% 2.87/0.99  --dbg_backtrace                         false
% 2.87/0.99  --dbg_dump_prop_clauses                 false
% 2.87/0.99  --dbg_dump_prop_clauses_file            -
% 2.87/0.99  --dbg_out_stat                          false
% 2.87/0.99  
% 2.87/0.99  
% 2.87/0.99  
% 2.87/0.99  
% 2.87/0.99  ------ Proving...
% 2.87/0.99  
% 2.87/0.99  
% 2.87/0.99  % SZS status Theorem for theBenchmark.p
% 2.87/0.99  
% 2.87/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.87/0.99  
% 2.87/0.99  fof(f22,conjecture,(
% 2.87/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f23,negated_conjecture,(
% 2.87/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.87/0.99    inference(negated_conjecture,[],[f22])).
% 2.87/0.99  
% 2.87/0.99  fof(f52,plain,(
% 2.87/0.99    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.87/0.99    inference(ennf_transformation,[],[f23])).
% 2.87/0.99  
% 2.87/0.99  fof(f53,plain,(
% 2.87/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.87/0.99    inference(flattening,[],[f52])).
% 2.87/0.99  
% 2.87/0.99  fof(f58,plain,(
% 2.87/0.99    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.87/0.99    introduced(choice_axiom,[])).
% 2.87/0.99  
% 2.87/0.99  fof(f57,plain,(
% 2.87/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.87/0.99    introduced(choice_axiom,[])).
% 2.87/0.99  
% 2.87/0.99  fof(f56,plain,(
% 2.87/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.87/0.99    introduced(choice_axiom,[])).
% 2.87/0.99  
% 2.87/0.99  fof(f59,plain,(
% 2.87/0.99    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f53,f58,f57,f56])).
% 2.87/0.99  
% 2.87/0.99  fof(f92,plain,(
% 2.87/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.87/0.99    inference(cnf_transformation,[],[f59])).
% 2.87/0.99  
% 2.87/0.99  fof(f19,axiom,(
% 2.87/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f47,plain,(
% 2.87/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.87/0.99    inference(ennf_transformation,[],[f19])).
% 2.87/0.99  
% 2.87/0.99  fof(f84,plain,(
% 2.87/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f47])).
% 2.87/0.99  
% 2.87/0.99  fof(f87,plain,(
% 2.87/0.99    l1_struct_0(sK0)),
% 2.87/0.99    inference(cnf_transformation,[],[f59])).
% 2.87/0.99  
% 2.87/0.99  fof(f89,plain,(
% 2.87/0.99    l1_struct_0(sK1)),
% 2.87/0.99    inference(cnf_transformation,[],[f59])).
% 2.87/0.99  
% 2.87/0.99  fof(f14,axiom,(
% 2.87/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f39,plain,(
% 2.87/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/0.99    inference(ennf_transformation,[],[f14])).
% 2.87/0.99  
% 2.87/0.99  fof(f75,plain,(
% 2.87/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/0.99    inference(cnf_transformation,[],[f39])).
% 2.87/0.99  
% 2.87/0.99  fof(f93,plain,(
% 2.87/0.99    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.87/0.99    inference(cnf_transformation,[],[f59])).
% 2.87/0.99  
% 2.87/0.99  fof(f18,axiom,(
% 2.87/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f45,plain,(
% 2.87/0.99    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.87/0.99    inference(ennf_transformation,[],[f18])).
% 2.87/0.99  
% 2.87/0.99  fof(f46,plain,(
% 2.87/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.87/0.99    inference(flattening,[],[f45])).
% 2.87/0.99  
% 2.87/0.99  fof(f83,plain,(
% 2.87/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f46])).
% 2.87/0.99  
% 2.87/0.99  fof(f94,plain,(
% 2.87/0.99    v2_funct_1(sK2)),
% 2.87/0.99    inference(cnf_transformation,[],[f59])).
% 2.87/0.99  
% 2.87/0.99  fof(f90,plain,(
% 2.87/0.99    v1_funct_1(sK2)),
% 2.87/0.99    inference(cnf_transformation,[],[f59])).
% 2.87/0.99  
% 2.87/0.99  fof(f91,plain,(
% 2.87/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.87/0.99    inference(cnf_transformation,[],[f59])).
% 2.87/0.99  
% 2.87/0.99  fof(f16,axiom,(
% 2.87/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f41,plain,(
% 2.87/0.99    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.87/0.99    inference(ennf_transformation,[],[f16])).
% 2.87/0.99  
% 2.87/0.99  fof(f42,plain,(
% 2.87/0.99    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.87/0.99    inference(flattening,[],[f41])).
% 2.87/0.99  
% 2.87/0.99  fof(f78,plain,(
% 2.87/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f42])).
% 2.87/0.99  
% 2.87/0.99  fof(f17,axiom,(
% 2.87/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f43,plain,(
% 2.87/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.87/0.99    inference(ennf_transformation,[],[f17])).
% 2.87/0.99  
% 2.87/0.99  fof(f44,plain,(
% 2.87/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.87/0.99    inference(flattening,[],[f43])).
% 2.87/0.99  
% 2.87/0.99  fof(f55,plain,(
% 2.87/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.87/0.99    inference(nnf_transformation,[],[f44])).
% 2.87/0.99  
% 2.87/0.99  fof(f79,plain,(
% 2.87/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f55])).
% 2.87/0.99  
% 2.87/0.99  fof(f11,axiom,(
% 2.87/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f24,plain,(
% 2.87/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.87/0.99    inference(pure_predicate_removal,[],[f11])).
% 2.87/0.99  
% 2.87/0.99  fof(f36,plain,(
% 2.87/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/0.99    inference(ennf_transformation,[],[f24])).
% 2.87/0.99  
% 2.87/0.99  fof(f72,plain,(
% 2.87/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/0.99    inference(cnf_transformation,[],[f36])).
% 2.87/0.99  
% 2.87/0.99  fof(f4,axiom,(
% 2.87/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f63,plain,(
% 2.87/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.87/0.99    inference(cnf_transformation,[],[f4])).
% 2.87/0.99  
% 2.87/0.99  fof(f3,axiom,(
% 2.87/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f26,plain,(
% 2.87/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.87/0.99    inference(ennf_transformation,[],[f3])).
% 2.87/0.99  
% 2.87/0.99  fof(f62,plain,(
% 2.87/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f26])).
% 2.87/0.99  
% 2.87/0.99  fof(f88,plain,(
% 2.87/0.99    ~v2_struct_0(sK1)),
% 2.87/0.99    inference(cnf_transformation,[],[f59])).
% 2.87/0.99  
% 2.87/0.99  fof(f20,axiom,(
% 2.87/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f48,plain,(
% 2.87/0.99    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.87/0.99    inference(ennf_transformation,[],[f20])).
% 2.87/0.99  
% 2.87/0.99  fof(f49,plain,(
% 2.87/0.99    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.87/0.99    inference(flattening,[],[f48])).
% 2.87/0.99  
% 2.87/0.99  fof(f85,plain,(
% 2.87/0.99    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f49])).
% 2.87/0.99  
% 2.87/0.99  fof(f1,axiom,(
% 2.87/0.99    v1_xboole_0(k1_xboole_0)),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f60,plain,(
% 2.87/0.99    v1_xboole_0(k1_xboole_0)),
% 2.87/0.99    inference(cnf_transformation,[],[f1])).
% 2.87/0.99  
% 2.87/0.99  fof(f7,axiom,(
% 2.87/0.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f29,plain,(
% 2.87/0.99    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.87/0.99    inference(ennf_transformation,[],[f7])).
% 2.87/0.99  
% 2.87/0.99  fof(f54,plain,(
% 2.87/0.99    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.87/0.99    inference(nnf_transformation,[],[f29])).
% 2.87/0.99  
% 2.87/0.99  fof(f66,plain,(
% 2.87/0.99    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f54])).
% 2.87/0.99  
% 2.87/0.99  fof(f9,axiom,(
% 2.87/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f32,plain,(
% 2.87/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.87/0.99    inference(ennf_transformation,[],[f9])).
% 2.87/0.99  
% 2.87/0.99  fof(f33,plain,(
% 2.87/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.87/0.99    inference(flattening,[],[f32])).
% 2.87/0.99  
% 2.87/0.99  fof(f70,plain,(
% 2.87/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f33])).
% 2.87/0.99  
% 2.87/0.99  fof(f2,axiom,(
% 2.87/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f25,plain,(
% 2.87/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.87/0.99    inference(ennf_transformation,[],[f2])).
% 2.87/0.99  
% 2.87/0.99  fof(f61,plain,(
% 2.87/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f25])).
% 2.87/0.99  
% 2.87/0.99  fof(f82,plain,(
% 2.87/0.99    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f46])).
% 2.87/0.99  
% 2.87/0.99  fof(f10,axiom,(
% 2.87/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f34,plain,(
% 2.87/0.99    ! [X0,X1] : ((k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.87/0.99    inference(ennf_transformation,[],[f10])).
% 2.87/0.99  
% 2.87/0.99  fof(f35,plain,(
% 2.87/0.99    ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.87/0.99    inference(flattening,[],[f34])).
% 2.87/0.99  
% 2.87/0.99  fof(f71,plain,(
% 2.87/0.99    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f35])).
% 2.87/0.99  
% 2.87/0.99  fof(f69,plain,(
% 2.87/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f33])).
% 2.87/0.99  
% 2.87/0.99  fof(f5,axiom,(
% 2.87/0.99    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f27,plain,(
% 2.87/0.99    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.87/0.99    inference(ennf_transformation,[],[f5])).
% 2.87/0.99  
% 2.87/0.99  fof(f64,plain,(
% 2.87/0.99    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f27])).
% 2.87/0.99  
% 2.87/0.99  fof(f6,axiom,(
% 2.87/0.99    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f28,plain,(
% 2.87/0.99    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.87/0.99    inference(ennf_transformation,[],[f6])).
% 2.87/0.99  
% 2.87/0.99  fof(f65,plain,(
% 2.87/0.99    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f28])).
% 2.87/0.99  
% 2.87/0.99  fof(f21,axiom,(
% 2.87/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f50,plain,(
% 2.87/0.99    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.87/0.99    inference(ennf_transformation,[],[f21])).
% 2.87/0.99  
% 2.87/0.99  fof(f51,plain,(
% 2.87/0.99    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.87/0.99    inference(flattening,[],[f50])).
% 2.87/0.99  
% 2.87/0.99  fof(f86,plain,(
% 2.87/0.99    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f51])).
% 2.87/0.99  
% 2.87/0.99  fof(f95,plain,(
% 2.87/0.99    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 2.87/0.99    inference(cnf_transformation,[],[f59])).
% 2.87/0.99  
% 2.87/0.99  fof(f13,axiom,(
% 2.87/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f38,plain,(
% 2.87/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/0.99    inference(ennf_transformation,[],[f13])).
% 2.87/0.99  
% 2.87/0.99  fof(f74,plain,(
% 2.87/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/0.99    inference(cnf_transformation,[],[f38])).
% 2.87/0.99  
% 2.87/0.99  cnf(c_30,negated_conjecture,
% 2.87/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.87/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1005,negated_conjecture,
% 2.87/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.87/0.99      inference(subtyping,[status(esa)],[c_30]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1539,plain,
% 2.87/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.87/0.99      inference(predicate_to_equality,[status(thm)],[c_1005]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_24,plain,
% 2.87/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.87/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_35,negated_conjecture,
% 2.87/0.99      ( l1_struct_0(sK0) ),
% 2.87/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_400,plain,
% 2.87/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.87/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_35]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_401,plain,
% 2.87/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.87/0.99      inference(unflattening,[status(thm)],[c_400]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1000,plain,
% 2.87/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.87/0.99      inference(subtyping,[status(esa)],[c_401]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_33,negated_conjecture,
% 2.87/0.99      ( l1_struct_0(sK1) ),
% 2.87/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_395,plain,
% 2.87/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.87/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_33]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_396,plain,
% 2.87/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.87/0.99      inference(unflattening,[status(thm)],[c_395]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1001,plain,
% 2.87/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.87/0.99      inference(subtyping,[status(esa)],[c_396]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1572,plain,
% 2.87/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.87/0.99      inference(light_normalisation,[status(thm)],[c_1539,c_1000,c_1001]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_15,plain,
% 2.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.87/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1009,plain,
% 2.87/0.99      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 2.87/0.99      | k2_relset_1(X0_57,X1_57,X0_56) = k2_relat_1(X0_56) ),
% 2.87/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1537,plain,
% 2.87/0.99      ( k2_relset_1(X0_57,X1_57,X0_56) = k2_relat_1(X0_56)
% 2.87/0.99      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
% 2.87/0.99      inference(predicate_to_equality,[status(thm)],[c_1009]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_2623,plain,
% 2.87/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.87/0.99      inference(superposition,[status(thm)],[c_1572,c_1537]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_29,negated_conjecture,
% 2.87/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.87/0.99      inference(cnf_transformation,[],[f93]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1006,negated_conjecture,
% 2.87/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.87/0.99      inference(subtyping,[status(esa)],[c_29]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1569,plain,
% 2.87/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.87/0.99      inference(light_normalisation,[status(thm)],[c_1006,c_1000,c_1001]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_2734,plain,
% 2.87/0.99      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.87/0.99      inference(demodulation,[status(thm)],[c_2623,c_1569]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_21,plain,
% 2.87/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.87/0.99      | ~ v1_funct_1(X0)
% 2.87/0.99      | ~ v2_funct_1(X0)
% 2.87/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.87/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_28,negated_conjecture,
% 2.87/0.99      ( v2_funct_1(sK2) ),
% 2.87/0.99      inference(cnf_transformation,[],[f94]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_674,plain,
% 2.87/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.87/0.99      | ~ v1_funct_1(X0)
% 2.87/0.99      | k2_relset_1(X1,X2,X0) != X2
% 2.87/0.99      | sK2 != X0 ),
% 2.87/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_675,plain,
% 2.87/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.87/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.87/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.87/0.99      | ~ v1_funct_1(sK2)
% 2.87/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.87/0.99      inference(unflattening,[status(thm)],[c_674]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_32,negated_conjecture,
% 2.87/0.99      ( v1_funct_1(sK2) ),
% 2.87/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_679,plain,
% 2.87/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.87/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.87/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 2.87/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.87/0.99      inference(global_propositional_subsumption,
% 2.87/0.99                [status(thm)],
% 2.87/0.99                [c_675,c_32]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_680,plain,
% 2.87/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.87/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.87/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.87/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.87/0.99      inference(renaming,[status(thm)],[c_679]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_995,plain,
% 2.87/0.99      ( ~ v1_funct_2(sK2,X0_57,X1_57)
% 2.87/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_57,X0_57)))
% 2.87/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 2.87/0.99      | k2_relset_1(X0_57,X1_57,sK2) != X1_57 ),
% 2.87/0.99      inference(subtyping,[status(esa)],[c_680]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1547,plain,
% 2.87/0.99      ( k2_relset_1(X0_57,X1_57,sK2) != X1_57
% 2.87/0.99      | v1_funct_2(sK2,X0_57,X1_57) != iProver_top
% 2.87/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1_57,X0_57))) = iProver_top
% 2.87/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
% 2.87/0.99      inference(predicate_to_equality,[status(thm)],[c_995]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_2303,plain,
% 2.87/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.87/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 2.87/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.87/0.99      inference(superposition,[status(thm)],[c_1569,c_1547]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_31,negated_conjecture,
% 2.87/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.87/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1004,negated_conjecture,
% 2.87/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.87/0.99      inference(subtyping,[status(esa)],[c_31]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1540,plain,
% 2.87/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.87/0.99      inference(predicate_to_equality,[status(thm)],[c_1004]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1562,plain,
% 2.87/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.87/0.99      inference(light_normalisation,[status(thm)],[c_1540,c_1000,c_1001]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_2306,plain,
% 2.87/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
% 2.87/0.99      inference(global_propositional_subsumption,
% 2.87/0.99                [status(thm)],
% 2.87/0.99                [c_2303,c_1562,c_1572]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_2778,plain,
% 2.87/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 2.87/0.99      inference(demodulation,[status(thm)],[c_2734,c_2306]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_17,plain,
% 2.87/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.87/0.99      | v1_partfun1(X0,X1)
% 2.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/0.99      | ~ v1_funct_1(X0)
% 2.87/0.99      | v1_xboole_0(X2) ),
% 2.87/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_20,plain,
% 2.87/0.99      ( ~ v1_partfun1(X0,X1)
% 2.87/0.99      | ~ v4_relat_1(X0,X1)
% 2.87/0.99      | ~ v1_relat_1(X0)
% 2.87/0.99      | k1_relat_1(X0) = X1 ),
% 2.87/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_501,plain,
% 2.87/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.87/0.99      | ~ v4_relat_1(X0,X1)
% 2.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/0.99      | ~ v1_funct_1(X0)
% 2.87/0.99      | ~ v1_relat_1(X0)
% 2.87/0.99      | v1_xboole_0(X2)
% 2.87/0.99      | k1_relat_1(X0) = X1 ),
% 2.87/0.99      inference(resolution,[status(thm)],[c_17,c_20]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_12,plain,
% 2.87/0.99      ( v4_relat_1(X0,X1)
% 2.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.87/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_505,plain,
% 2.87/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/0.99      | ~ v1_funct_1(X0)
% 2.87/0.99      | ~ v1_relat_1(X0)
% 2.87/0.99      | v1_xboole_0(X2)
% 2.87/0.99      | k1_relat_1(X0) = X1 ),
% 2.87/0.99      inference(global_propositional_subsumption,
% 2.87/0.99                [status(thm)],
% 2.87/0.99                [c_501,c_12]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_999,plain,
% 2.87/0.99      ( ~ v1_funct_2(X0_56,X0_57,X1_57)
% 2.87/0.99      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 2.87/0.99      | ~ v1_funct_1(X0_56)
% 2.87/0.99      | ~ v1_relat_1(X0_56)
% 2.87/0.99      | v1_xboole_0(X1_57)
% 2.87/0.99      | k1_relat_1(X0_56) = X0_57 ),
% 2.87/0.99      inference(subtyping,[status(esa)],[c_505]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1543,plain,
% 2.87/0.99      ( k1_relat_1(X0_56) = X0_57
% 2.87/0.99      | v1_funct_2(X0_56,X0_57,X1_57) != iProver_top
% 2.87/0.99      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 2.87/0.99      | v1_funct_1(X0_56) != iProver_top
% 2.87/0.99      | v1_relat_1(X0_56) != iProver_top
% 2.87/0.99      | v1_xboole_0(X1_57) = iProver_top ),
% 2.87/0.99      inference(predicate_to_equality,[status(thm)],[c_999]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_3,plain,
% 2.87/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.87/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1018,plain,
% 2.87/0.99      ( v1_relat_1(k2_zfmisc_1(X0_57,X1_57)) ),
% 2.87/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1063,plain,
% 2.87/0.99      ( v1_relat_1(k2_zfmisc_1(X0_57,X1_57)) = iProver_top ),
% 2.87/0.99      inference(predicate_to_equality,[status(thm)],[c_1018]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1100,plain,
% 2.87/0.99      ( k1_relat_1(X0_56) = X0_57
% 2.87/0.99      | v1_funct_2(X0_56,X0_57,X1_57) != iProver_top
% 2.87/0.99      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 2.87/0.99      | v1_funct_1(X0_56) != iProver_top
% 2.87/0.99      | v1_relat_1(X0_56) != iProver_top
% 2.87/0.99      | v1_xboole_0(X1_57) = iProver_top ),
% 2.87/0.99      inference(predicate_to_equality,[status(thm)],[c_999]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_2,plain,
% 2.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.87/0.99      | ~ v1_relat_1(X1)
% 2.87/0.99      | v1_relat_1(X0) ),
% 2.87/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1019,plain,
% 2.87/0.99      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(X1_56))
% 2.87/0.99      | ~ v1_relat_1(X1_56)
% 2.87/0.99      | v1_relat_1(X0_56) ),
% 2.87/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1798,plain,
% 2.87/0.99      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 2.87/0.99      | v1_relat_1(X0_56)
% 2.87/0.99      | ~ v1_relat_1(k2_zfmisc_1(X0_57,X1_57)) ),
% 2.87/0.99      inference(instantiation,[status(thm)],[c_1019]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1799,plain,
% 2.87/0.99      ( m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 2.87/0.99      | v1_relat_1(X0_56) = iProver_top
% 2.87/0.99      | v1_relat_1(k2_zfmisc_1(X0_57,X1_57)) != iProver_top ),
% 2.87/0.99      inference(predicate_to_equality,[status(thm)],[c_1798]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_3038,plain,
% 2.87/0.99      ( v1_funct_1(X0_56) != iProver_top
% 2.87/0.99      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 2.87/0.99      | v1_funct_2(X0_56,X0_57,X1_57) != iProver_top
% 2.87/0.99      | k1_relat_1(X0_56) = X0_57
% 2.87/0.99      | v1_xboole_0(X1_57) = iProver_top ),
% 2.87/0.99      inference(global_propositional_subsumption,
% 2.87/0.99                [status(thm)],
% 2.87/0.99                [c_1543,c_1063,c_1100,c_1799]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_3039,plain,
% 2.87/0.99      ( k1_relat_1(X0_56) = X0_57
% 2.87/0.99      | v1_funct_2(X0_56,X0_57,X1_57) != iProver_top
% 2.87/0.99      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 2.87/0.99      | v1_funct_1(X0_56) != iProver_top
% 2.87/0.99      | v1_xboole_0(X1_57) = iProver_top ),
% 2.87/0.99      inference(renaming,[status(thm)],[c_3038]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_3536,plain,
% 2.87/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.87/0.99      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 2.87/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.87/0.99      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
% 2.87/0.99      inference(superposition,[status(thm)],[c_2778,c_3039]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_34,negated_conjecture,
% 2.87/0.99      ( ~ v2_struct_0(sK1) ),
% 2.87/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_25,plain,
% 2.87/0.99      ( v2_struct_0(X0)
% 2.87/0.99      | ~ l1_struct_0(X0)
% 2.87/0.99      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 2.87/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_47,plain,
% 2.87/0.99      ( v2_struct_0(sK1)
% 2.87/0.99      | ~ l1_struct_0(sK1)
% 2.87/0.99      | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.87/0.99      inference(instantiation,[status(thm)],[c_25]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_0,plain,
% 2.87/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.87/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_7,plain,
% 2.87/0.99      ( ~ v1_relat_1(X0)
% 2.87/0.99      | k2_relat_1(X0) = k1_xboole_0
% 2.87/0.99      | k1_relat_1(X0) != k1_xboole_0 ),
% 2.87/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1014,plain,
% 2.87/0.99      ( ~ v1_relat_1(X0_56)
% 2.87/0.99      | k2_relat_1(X0_56) = k1_xboole_0
% 2.87/0.99      | k1_relat_1(X0_56) != k1_xboole_0 ),
% 2.87/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1076,plain,
% 2.87/0.99      ( ~ v1_relat_1(sK2)
% 2.87/0.99      | k2_relat_1(sK2) = k1_xboole_0
% 2.87/0.99      | k1_relat_1(sK2) != k1_xboole_0 ),
% 2.87/0.99      inference(instantiation,[status(thm)],[c_1014]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_9,plain,
% 2.87/0.99      ( ~ v1_funct_1(X0)
% 2.87/0.99      | v1_funct_1(k2_funct_1(X0))
% 2.87/0.99      | ~ v1_relat_1(X0) ),
% 2.87/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1013,plain,
% 2.87/0.99      ( ~ v1_funct_1(X0_56)
% 2.87/0.99      | v1_funct_1(k2_funct_1(X0_56))
% 2.87/0.99      | ~ v1_relat_1(X0_56) ),
% 2.87/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1079,plain,
% 2.87/0.99      ( v1_funct_1(k2_funct_1(sK2))
% 2.87/0.99      | ~ v1_funct_1(sK2)
% 2.87/0.99      | ~ v1_relat_1(sK2) ),
% 2.87/0.99      inference(instantiation,[status(thm)],[c_1013]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1859,plain,
% 2.87/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.87/0.99      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.87/0.99      | v1_relat_1(sK2) ),
% 2.87/0.99      inference(instantiation,[status(thm)],[c_1798]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1,plain,
% 2.87/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.87/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1020,plain,
% 2.87/0.99      ( ~ v1_xboole_0(X0_57) | k1_xboole_0 = X0_57 ),
% 2.87/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1902,plain,
% 2.87/0.99      ( ~ v1_xboole_0(u1_struct_0(sK0))
% 2.87/0.99      | k1_xboole_0 = u1_struct_0(sK0) ),
% 2.87/0.99      inference(instantiation,[status(thm)],[c_1020]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1938,plain,
% 2.87/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.87/0.99      inference(instantiation,[status(thm)],[c_1018]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1024,plain,( X0_57 = X0_57 ),theory(equality) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_2103,plain,
% 2.87/0.99      ( k2_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.87/0.99      inference(instantiation,[status(thm)],[c_1024]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1028,plain,
% 2.87/0.99      ( ~ v1_xboole_0(X0_57) | v1_xboole_0(X1_57) | X1_57 != X0_57 ),
% 2.87/0.99      theory(equality) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1974,plain,
% 2.87/0.99      ( ~ v1_xboole_0(X0_57)
% 2.87/0.99      | v1_xboole_0(u1_struct_0(sK0))
% 2.87/0.99      | u1_struct_0(sK0) != X0_57 ),
% 2.87/0.99      inference(instantiation,[status(thm)],[c_1028]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_2208,plain,
% 2.87/0.99      ( v1_xboole_0(u1_struct_0(sK0))
% 2.87/0.99      | ~ v1_xboole_0(k2_struct_0(sK0))
% 2.87/0.99      | u1_struct_0(sK0) != k2_struct_0(sK0) ),
% 2.87/0.99      inference(instantiation,[status(thm)],[c_1974]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1027,plain,
% 2.87/0.99      ( X0_57 != X1_57 | X2_57 != X1_57 | X2_57 = X0_57 ),
% 2.87/0.99      theory(equality) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1916,plain,
% 2.87/0.99      ( X0_57 != X1_57
% 2.87/0.99      | k2_struct_0(sK1) != X1_57
% 2.87/0.99      | k2_struct_0(sK1) = X0_57 ),
% 2.87/0.99      inference(instantiation,[status(thm)],[c_1027]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_2102,plain,
% 2.87/0.99      ( X0_57 != k2_struct_0(sK1)
% 2.87/0.99      | k2_struct_0(sK1) = X0_57
% 2.87/0.99      | k2_struct_0(sK1) != k2_struct_0(sK1) ),
% 2.87/0.99      inference(instantiation,[status(thm)],[c_1916]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_2383,plain,
% 2.87/0.99      ( u1_struct_0(sK1) != k2_struct_0(sK1)
% 2.87/0.99      | k2_struct_0(sK1) = u1_struct_0(sK1)
% 2.87/0.99      | k2_struct_0(sK1) != k2_struct_0(sK1) ),
% 2.87/0.99      inference(instantiation,[status(thm)],[c_2102]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_1788,plain,
% 2.87/0.99      ( ~ v1_xboole_0(X0_57)
% 2.87/0.99      | v1_xboole_0(k2_struct_0(sK1))
% 2.87/0.99      | k2_struct_0(sK1) != X0_57 ),
% 2.87/0.99      inference(instantiation,[status(thm)],[c_1028]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_2492,plain,
% 2.87/0.99      ( ~ v1_xboole_0(u1_struct_0(sK1))
% 2.87/0.99      | v1_xboole_0(k2_struct_0(sK1))
% 2.87/0.99      | k2_struct_0(sK1) != u1_struct_0(sK1) ),
% 2.87/0.99      inference(instantiation,[status(thm)],[c_1788]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_22,plain,
% 2.87/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.87/0.99      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/0.99      | ~ v1_funct_1(X0)
% 2.87/0.99      | ~ v2_funct_1(X0)
% 2.87/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.87/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_650,plain,
% 2.87/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.87/0.99      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/0.99      | ~ v1_funct_1(X0)
% 2.87/0.99      | k2_relset_1(X1,X2,X0) != X2
% 2.87/0.99      | sK2 != X0 ),
% 2.87/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_28]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_651,plain,
% 2.87/0.99      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 2.87/0.99      | ~ v1_funct_2(sK2,X1,X0)
% 2.87/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.87/1.00      | ~ v1_funct_1(sK2)
% 2.87/1.00      | k2_relset_1(X1,X0,sK2) != X0 ),
% 2.87/1.00      inference(unflattening,[status(thm)],[c_650]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_655,plain,
% 2.87/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.87/1.00      | ~ v1_funct_2(sK2,X1,X0)
% 2.87/1.00      | v1_funct_2(k2_funct_1(sK2),X0,X1)
% 2.87/1.00      | k2_relset_1(X1,X0,sK2) != X0 ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_651,c_32]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_656,plain,
% 2.87/1.00      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 2.87/1.00      | ~ v1_funct_2(sK2,X1,X0)
% 2.87/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.87/1.00      | k2_relset_1(X1,X0,sK2) != X0 ),
% 2.87/1.00      inference(renaming,[status(thm)],[c_655]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_996,plain,
% 2.87/1.00      ( v1_funct_2(k2_funct_1(sK2),X0_57,X1_57)
% 2.87/1.00      | ~ v1_funct_2(sK2,X1_57,X0_57)
% 2.87/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1_57,X0_57)))
% 2.87/1.00      | k2_relset_1(X1_57,X0_57,sK2) != X0_57 ),
% 2.87/1.00      inference(subtyping,[status(esa)],[c_656]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1546,plain,
% 2.87/1.00      ( k2_relset_1(X0_57,X1_57,sK2) != X1_57
% 2.87/1.00      | v1_funct_2(k2_funct_1(sK2),X1_57,X0_57) = iProver_top
% 2.87/1.00      | v1_funct_2(sK2,X0_57,X1_57) != iProver_top
% 2.87/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_996]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2100,plain,
% 2.87/1.00      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
% 2.87/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.87/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_1569,c_1546]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2116,plain,
% 2.87/1.00      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_2100,c_1562,c_1572]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2779,plain,
% 2.87/1.00      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top ),
% 2.87/1.00      inference(demodulation,[status(thm)],[c_2734,c_2116]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2809,plain,
% 2.87/1.00      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
% 2.87/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2779]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_382,plain,
% 2.87/1.00      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 2.87/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_34]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_383,plain,
% 2.87/1.00      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.87/1.00      inference(unflattening,[status(thm)],[c_382]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_385,plain,
% 2.87/1.00      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_383,c_34,c_33,c_47]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1002,plain,
% 2.87/1.00      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.87/1.00      inference(subtyping,[status(esa)],[c_385]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1542,plain,
% 2.87/1.00      ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_1002]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2784,plain,
% 2.87/1.00      ( v1_xboole_0(k2_relat_1(sK2)) != iProver_top ),
% 2.87/1.00      inference(demodulation,[status(thm)],[c_2734,c_1542]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2812,plain,
% 2.87/1.00      ( ~ v1_xboole_0(k2_relat_1(sK2)) ),
% 2.87/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2784]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2196,plain,
% 2.87/1.00      ( ~ v1_funct_2(X0_56,X0_57,u1_struct_0(sK1))
% 2.87/1.00      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,u1_struct_0(sK1))))
% 2.87/1.00      | ~ v1_funct_1(X0_56)
% 2.87/1.00      | ~ v1_relat_1(X0_56)
% 2.87/1.00      | v1_xboole_0(u1_struct_0(sK1))
% 2.87/1.00      | k1_relat_1(X0_56) = X0_57 ),
% 2.87/1.00      inference(instantiation,[status(thm)],[c_999]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2839,plain,
% 2.87/1.00      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.87/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.87/1.00      | ~ v1_funct_1(sK2)
% 2.87/1.00      | ~ v1_relat_1(sK2)
% 2.87/1.00      | v1_xboole_0(u1_struct_0(sK1))
% 2.87/1.00      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 2.87/1.00      inference(instantiation,[status(thm)],[c_2196]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2114,plain,
% 2.87/1.00      ( k1_relat_1(X0_56) != X0_57
% 2.87/1.00      | k1_relat_1(X0_56) = k1_xboole_0
% 2.87/1.00      | k1_xboole_0 != X0_57 ),
% 2.87/1.00      inference(instantiation,[status(thm)],[c_1027]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_3002,plain,
% 2.87/1.00      ( k1_relat_1(sK2) != u1_struct_0(sK0)
% 2.87/1.00      | k1_relat_1(sK2) = k1_xboole_0
% 2.87/1.00      | k1_xboole_0 != u1_struct_0(sK0) ),
% 2.87/1.00      inference(instantiation,[status(thm)],[c_2114]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_3549,plain,
% 2.87/1.00      ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
% 2.87/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.87/1.00      | v1_xboole_0(k2_struct_0(sK0))
% 2.87/1.00      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.87/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3536]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_3639,plain,
% 2.87/1.00      ( ~ v1_xboole_0(X0_57)
% 2.87/1.00      | v1_xboole_0(k2_relat_1(sK2))
% 2.87/1.00      | k2_relat_1(sK2) != X0_57 ),
% 2.87/1.00      inference(instantiation,[status(thm)],[c_1028]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_3641,plain,
% 2.87/1.00      ( v1_xboole_0(k2_relat_1(sK2))
% 2.87/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 2.87/1.00      | k2_relat_1(sK2) != k1_xboole_0 ),
% 2.87/1.00      inference(instantiation,[status(thm)],[c_3639]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_5620,plain,
% 2.87/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_3536,c_34,c_33,c_32,c_31,c_30,c_47,c_0,c_1076,c_1079,
% 2.87/1.00                 c_1001,c_1000,c_1859,c_1902,c_1938,c_2103,c_2208,c_2383,
% 2.87/1.00                 c_2492,c_2809,c_2812,c_2839,c_3002,c_3549,c_3641]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_11,plain,
% 2.87/1.00      ( ~ v1_funct_1(X0)
% 2.87/1.00      | ~ v2_funct_1(X0)
% 2.87/1.00      | ~ v1_relat_1(X0)
% 2.87/1.00      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
% 2.87/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_698,plain,
% 2.87/1.00      ( ~ v1_funct_1(X0)
% 2.87/1.00      | ~ v1_relat_1(X0)
% 2.87/1.00      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
% 2.87/1.00      | sK2 != X0 ),
% 2.87/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_28]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_699,plain,
% 2.87/1.00      ( ~ v1_funct_1(sK2)
% 2.87/1.00      | ~ v1_relat_1(sK2)
% 2.87/1.00      | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
% 2.87/1.00      inference(unflattening,[status(thm)],[c_698]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_703,plain,
% 2.87/1.00      ( ~ v1_relat_1(sK2)
% 2.87/1.00      | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_699,c_32]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_994,plain,
% 2.87/1.00      ( ~ v1_relat_1(sK2)
% 2.87/1.00      | k9_relat_1(k2_funct_1(sK2),X0_57) = k10_relat_1(sK2,X0_57) ),
% 2.87/1.00      inference(subtyping,[status(esa)],[c_703]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1548,plain,
% 2.87/1.00      ( k9_relat_1(k2_funct_1(sK2),X0_57) = k10_relat_1(sK2,X0_57)
% 2.87/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_994]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1985,plain,
% 2.87/1.00      ( k9_relat_1(k2_funct_1(sK2),X0_57) = k10_relat_1(sK2,X0_57) ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_1548,c_30,c_994,c_1859,c_1938]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1527,plain,
% 2.87/1.00      ( m1_subset_1(X0_56,k1_zfmisc_1(X1_56)) != iProver_top
% 2.87/1.00      | v1_relat_1(X1_56) != iProver_top
% 2.87/1.00      | v1_relat_1(X0_56) = iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_1019]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2311,plain,
% 2.87/1.00      ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))) != iProver_top
% 2.87/1.00      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_2306,c_1527]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_39,plain,
% 2.87/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_41,plain,
% 2.87/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_10,plain,
% 2.87/1.00      ( ~ v1_funct_1(X0)
% 2.87/1.00      | ~ v1_relat_1(X0)
% 2.87/1.00      | v1_relat_1(k2_funct_1(X0)) ),
% 2.87/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1012,plain,
% 2.87/1.00      ( ~ v1_funct_1(X0_56)
% 2.87/1.00      | ~ v1_relat_1(X0_56)
% 2.87/1.00      | v1_relat_1(k2_funct_1(X0_56)) ),
% 2.87/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1081,plain,
% 2.87/1.00      ( v1_funct_1(X0_56) != iProver_top
% 2.87/1.00      | v1_relat_1(X0_56) != iProver_top
% 2.87/1.00      | v1_relat_1(k2_funct_1(X0_56)) = iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_1012]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1083,plain,
% 2.87/1.00      ( v1_funct_1(sK2) != iProver_top
% 2.87/1.00      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 2.87/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.87/1.00      inference(instantiation,[status(thm)],[c_1081]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1860,plain,
% 2.87/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.87/1.00      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.87/1.00      | v1_relat_1(sK2) = iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_1859]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1939,plain,
% 2.87/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_1938]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2405,plain,
% 2.87/1.00      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_2311,c_39,c_41,c_1083,c_1860,c_1939]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4,plain,
% 2.87/1.00      ( ~ v1_relat_1(X0)
% 2.87/1.00      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 2.87/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1017,plain,
% 2.87/1.00      ( ~ v1_relat_1(X0_56)
% 2.87/1.00      | k9_relat_1(X0_56,k1_relat_1(X0_56)) = k2_relat_1(X0_56) ),
% 2.87/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1529,plain,
% 2.87/1.00      ( k9_relat_1(X0_56,k1_relat_1(X0_56)) = k2_relat_1(X0_56)
% 2.87/1.00      | v1_relat_1(X0_56) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_1017]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2411,plain,
% 2.87/1.00      ( k9_relat_1(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2))) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_2405,c_1529]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_3050,plain,
% 2.87/1.00      ( k10_relat_1(sK2,k1_relat_1(k2_funct_1(sK2))) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_1985,c_2411]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_5624,plain,
% 2.87/1.00      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.87/1.00      inference(demodulation,[status(thm)],[c_5620,c_3050]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1846,plain,
% 2.87/1.00      ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != iProver_top
% 2.87/1.00      | v1_relat_1(sK2) = iProver_top ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_1572,c_1527]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2360,plain,
% 2.87/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_1846,c_41,c_1860,c_1939]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_5,plain,
% 2.87/1.00      ( ~ v1_relat_1(X0)
% 2.87/1.00      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 2.87/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1016,plain,
% 2.87/1.00      ( ~ v1_relat_1(X0_56)
% 2.87/1.00      | k10_relat_1(X0_56,k2_relat_1(X0_56)) = k1_relat_1(X0_56) ),
% 2.87/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1530,plain,
% 2.87/1.00      ( k10_relat_1(X0_56,k2_relat_1(X0_56)) = k1_relat_1(X0_56)
% 2.87/1.00      | v1_relat_1(X0_56) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_1016]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2366,plain,
% 2.87/1.00      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_2360,c_1530]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_5632,plain,
% 2.87/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.87/1.00      inference(light_normalisation,[status(thm)],[c_5624,c_2366]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2782,plain,
% 2.87/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.87/1.00      inference(demodulation,[status(thm)],[c_2734,c_1572]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_3517,plain,
% 2.87/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.87/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.87/1.00      | v1_funct_1(sK2) != iProver_top
% 2.87/1.00      | v1_xboole_0(k2_relat_1(sK2)) = iProver_top ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_2782,c_3039]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2783,plain,
% 2.87/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.87/1.00      inference(demodulation,[status(thm)],[c_2734,c_1562]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4187,plain,
% 2.87/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_3517,c_39,c_2783,c_2784]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_26,plain,
% 2.87/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.87/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.00      | ~ v1_funct_1(X0)
% 2.87/1.00      | ~ v2_funct_1(X0)
% 2.87/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.87/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.87/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_602,plain,
% 2.87/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.87/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.00      | ~ v1_funct_1(X0)
% 2.87/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.87/1.00      | k2_relset_1(X1,X2,X0) != X2
% 2.87/1.00      | sK2 != X0 ),
% 2.87/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_28]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_603,plain,
% 2.87/1.00      ( ~ v1_funct_2(sK2,X0,X1)
% 2.87/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.87/1.00      | ~ v1_funct_1(sK2)
% 2.87/1.00      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.87/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.87/1.00      inference(unflattening,[status(thm)],[c_602]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_607,plain,
% 2.87/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.87/1.00      | ~ v1_funct_2(sK2,X0,X1)
% 2.87/1.00      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.87/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_603,c_32]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_608,plain,
% 2.87/1.00      ( ~ v1_funct_2(sK2,X0,X1)
% 2.87/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.87/1.00      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.87/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.87/1.00      inference(renaming,[status(thm)],[c_607]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_998,plain,
% 2.87/1.00      ( ~ v1_funct_2(sK2,X0_57,X1_57)
% 2.87/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 2.87/1.00      | k2_relset_1(X0_57,X1_57,sK2) != X1_57
% 2.87/1.00      | k2_tops_2(X0_57,X1_57,sK2) = k2_funct_1(sK2) ),
% 2.87/1.00      inference(subtyping,[status(esa)],[c_608]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1544,plain,
% 2.87/1.00      ( k2_relset_1(X0_57,X1_57,sK2) != X1_57
% 2.87/1.00      | k2_tops_2(X0_57,X1_57,sK2) = k2_funct_1(sK2)
% 2.87/1.00      | v1_funct_2(sK2,X0_57,X1_57) != iProver_top
% 2.87/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_998]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2027,plain,
% 2.87/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.87/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.87/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_1569,c_1544]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2030,plain,
% 2.87/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_2027,c_1562,c_1572]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_27,negated_conjecture,
% 2.87/1.00      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.87/1.00      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.87/1.00      inference(cnf_transformation,[],[f95]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1007,negated_conjecture,
% 2.87/1.00      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.87/1.00      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.87/1.00      inference(subtyping,[status(esa)],[c_27]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1637,plain,
% 2.87/1.00      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.87/1.00      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.87/1.00      inference(light_normalisation,[status(thm)],[c_1007,c_1000,c_1001]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2033,plain,
% 2.87/1.00      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.87/1.00      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
% 2.87/1.00      inference(demodulation,[status(thm)],[c_2030,c_1637]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2780,plain,
% 2.87/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.87/1.00      | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 2.87/1.00      inference(demodulation,[status(thm)],[c_2734,c_2033]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_14,plain,
% 2.87/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.87/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1010,plain,
% 2.87/1.00      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 2.87/1.00      | k1_relset_1(X0_57,X1_57,X0_56) = k1_relat_1(X0_56) ),
% 2.87/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1536,plain,
% 2.87/1.00      ( k1_relset_1(X0_57,X1_57,X0_56) = k1_relat_1(X0_56)
% 2.87/1.00      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_1010]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2529,plain,
% 2.87/1.00      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_2306,c_1536]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_3088,plain,
% 2.87/1.00      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 2.87/1.00      inference(light_normalisation,[status(thm)],[c_2529,c_2734]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2624,plain,
% 2.87/1.00      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_2306,c_1537]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_3090,plain,
% 2.87/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.87/1.00      inference(light_normalisation,[status(thm)],[c_2624,c_2734]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_3632,plain,
% 2.87/1.00      ( k2_relat_1(k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.87/1.00      | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 2.87/1.00      inference(light_normalisation,[status(thm)],[c_2780,c_3088,c_3090]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4193,plain,
% 2.87/1.00      ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
% 2.87/1.00      | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 2.87/1.00      inference(demodulation,[status(thm)],[c_4187,c_3632]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(contradiction,plain,
% 2.87/1.00      ( $false ),
% 2.87/1.00      inference(minisat,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_5632,c_4193,c_3641,c_3549,c_3002,c_2839,c_2812,c_2809,
% 2.87/1.00                 c_2492,c_2383,c_2208,c_2103,c_1938,c_1902,c_1859,c_1000,
% 2.87/1.00                 c_1001,c_1079,c_1076,c_0,c_47,c_30,c_31,c_32,c_33,c_34]) ).
% 2.87/1.00  
% 2.87/1.00  
% 2.87/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.87/1.00  
% 2.87/1.00  ------                               Statistics
% 2.87/1.00  
% 2.87/1.00  ------ General
% 2.87/1.00  
% 2.87/1.00  abstr_ref_over_cycles:                  0
% 2.87/1.00  abstr_ref_under_cycles:                 0
% 2.87/1.00  gc_basic_clause_elim:                   0
% 2.87/1.00  forced_gc_time:                         0
% 2.87/1.00  parsing_time:                           0.015
% 2.87/1.00  unif_index_cands_time:                  0.
% 2.87/1.00  unif_index_add_time:                    0.
% 2.87/1.00  orderings_time:                         0.
% 2.87/1.00  out_proof_time:                         0.015
% 2.87/1.00  total_time:                             0.199
% 2.87/1.00  num_of_symbols:                         60
% 2.87/1.00  num_of_terms:                           4274
% 2.87/1.00  
% 2.87/1.00  ------ Preprocessing
% 2.87/1.00  
% 2.87/1.00  num_of_splits:                          0
% 2.87/1.00  num_of_split_atoms:                     0
% 2.87/1.00  num_of_reused_defs:                     0
% 2.87/1.00  num_eq_ax_congr_red:                    22
% 2.87/1.00  num_of_sem_filtered_clauses:            1
% 2.87/1.00  num_of_subtypes:                        4
% 2.87/1.00  monotx_restored_types:                  1
% 2.87/1.00  sat_num_of_epr_types:                   0
% 2.87/1.00  sat_num_of_non_cyclic_types:            0
% 2.87/1.00  sat_guarded_non_collapsed_types:        0
% 2.87/1.00  num_pure_diseq_elim:                    0
% 2.87/1.00  simp_replaced_by:                       0
% 2.87/1.00  res_preprocessed:                       161
% 2.87/1.00  prep_upred:                             0
% 2.87/1.00  prep_unflattend:                        22
% 2.87/1.00  smt_new_axioms:                         0
% 2.87/1.00  pred_elim_cands:                        5
% 2.87/1.00  pred_elim:                              5
% 2.87/1.00  pred_elim_cl:                           6
% 2.87/1.00  pred_elim_cycles:                       10
% 2.87/1.00  merged_defs:                            0
% 2.87/1.00  merged_defs_ncl:                        0
% 2.87/1.00  bin_hyper_res:                          0
% 2.87/1.00  prep_cycles:                            4
% 2.87/1.00  pred_elim_time:                         0.008
% 2.87/1.00  splitting_time:                         0.
% 2.87/1.00  sem_filter_time:                        0.
% 2.87/1.00  monotx_time:                            0.001
% 2.87/1.00  subtype_inf_time:                       0.002
% 2.87/1.00  
% 2.87/1.00  ------ Problem properties
% 2.87/1.00  
% 2.87/1.00  clauses:                                29
% 2.87/1.00  conjectures:                            5
% 2.87/1.00  epr:                                    3
% 2.87/1.00  horn:                                   28
% 2.87/1.00  ground:                                 10
% 2.87/1.00  unary:                                  9
% 2.87/1.00  binary:                                 10
% 2.87/1.00  lits:                                   66
% 2.87/1.00  lits_eq:                                23
% 2.87/1.00  fd_pure:                                0
% 2.87/1.00  fd_pseudo:                              0
% 2.87/1.00  fd_cond:                                1
% 2.87/1.00  fd_pseudo_cond:                         1
% 2.87/1.00  ac_symbols:                             0
% 2.87/1.00  
% 2.87/1.00  ------ Propositional Solver
% 2.87/1.00  
% 2.87/1.00  prop_solver_calls:                      30
% 2.87/1.00  prop_fast_solver_calls:                 1090
% 2.87/1.00  smt_solver_calls:                       0
% 2.87/1.00  smt_fast_solver_calls:                  0
% 2.87/1.00  prop_num_of_clauses:                    1865
% 2.87/1.00  prop_preprocess_simplified:             6102
% 2.87/1.00  prop_fo_subsumed:                       31
% 2.87/1.00  prop_solver_time:                       0.
% 2.87/1.00  smt_solver_time:                        0.
% 2.87/1.00  smt_fast_solver_time:                   0.
% 2.87/1.00  prop_fast_solver_time:                  0.
% 2.87/1.00  prop_unsat_core_time:                   0.
% 2.87/1.00  
% 2.87/1.00  ------ QBF
% 2.87/1.00  
% 2.87/1.00  qbf_q_res:                              0
% 2.87/1.00  qbf_num_tautologies:                    0
% 2.87/1.00  qbf_prep_cycles:                        0
% 2.87/1.00  
% 2.87/1.00  ------ BMC1
% 2.87/1.00  
% 2.87/1.00  bmc1_current_bound:                     -1
% 2.87/1.00  bmc1_last_solved_bound:                 -1
% 2.87/1.00  bmc1_unsat_core_size:                   -1
% 2.87/1.00  bmc1_unsat_core_parents_size:           -1
% 2.87/1.00  bmc1_merge_next_fun:                    0
% 2.87/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.87/1.00  
% 2.87/1.00  ------ Instantiation
% 2.87/1.00  
% 2.87/1.00  inst_num_of_clauses:                    673
% 2.87/1.00  inst_num_in_passive:                    29
% 2.87/1.00  inst_num_in_active:                     390
% 2.87/1.00  inst_num_in_unprocessed:                254
% 2.87/1.00  inst_num_of_loops:                      450
% 2.87/1.00  inst_num_of_learning_restarts:          0
% 2.87/1.00  inst_num_moves_active_passive:          55
% 2.87/1.00  inst_lit_activity:                      0
% 2.87/1.00  inst_lit_activity_moves:                0
% 2.87/1.00  inst_num_tautologies:                   0
% 2.87/1.00  inst_num_prop_implied:                  0
% 2.87/1.00  inst_num_existing_simplified:           0
% 2.87/1.00  inst_num_eq_res_simplified:             0
% 2.87/1.00  inst_num_child_elim:                    0
% 2.87/1.00  inst_num_of_dismatching_blockings:      145
% 2.87/1.00  inst_num_of_non_proper_insts:           620
% 2.87/1.00  inst_num_of_duplicates:                 0
% 2.87/1.00  inst_inst_num_from_inst_to_res:         0
% 2.87/1.00  inst_dismatching_checking_time:         0.
% 2.87/1.00  
% 2.87/1.00  ------ Resolution
% 2.87/1.00  
% 2.87/1.00  res_num_of_clauses:                     0
% 2.87/1.00  res_num_in_passive:                     0
% 2.87/1.00  res_num_in_active:                      0
% 2.87/1.00  res_num_of_loops:                       165
% 2.87/1.00  res_forward_subset_subsumed:            72
% 2.87/1.00  res_backward_subset_subsumed:           0
% 2.87/1.00  res_forward_subsumed:                   0
% 2.87/1.00  res_backward_subsumed:                  0
% 2.87/1.00  res_forward_subsumption_resolution:     0
% 2.87/1.00  res_backward_subsumption_resolution:    0
% 2.87/1.00  res_clause_to_clause_subsumption:       168
% 2.87/1.00  res_orphan_elimination:                 0
% 2.87/1.00  res_tautology_del:                      76
% 2.87/1.00  res_num_eq_res_simplified:              0
% 2.87/1.00  res_num_sel_changes:                    0
% 2.87/1.00  res_moves_from_active_to_pass:          0
% 2.87/1.00  
% 2.87/1.00  ------ Superposition
% 2.87/1.00  
% 2.87/1.00  sup_time_total:                         0.
% 2.87/1.00  sup_time_generating:                    0.
% 2.87/1.00  sup_time_sim_full:                      0.
% 2.87/1.00  sup_time_sim_immed:                     0.
% 2.87/1.00  
% 2.87/1.00  sup_num_of_clauses:                     93
% 2.87/1.00  sup_num_in_active:                      57
% 2.87/1.00  sup_num_in_passive:                     36
% 2.87/1.00  sup_num_of_loops:                       89
% 2.87/1.00  sup_fw_superposition:                   36
% 2.87/1.00  sup_bw_superposition:                   66
% 2.87/1.00  sup_immediate_simplified:               33
% 2.87/1.00  sup_given_eliminated:                   0
% 2.87/1.00  comparisons_done:                       0
% 2.87/1.00  comparisons_avoided:                    0
% 2.87/1.00  
% 2.87/1.00  ------ Simplifications
% 2.87/1.00  
% 2.87/1.00  
% 2.87/1.00  sim_fw_subset_subsumed:                 17
% 2.87/1.00  sim_bw_subset_subsumed:                 2
% 2.87/1.00  sim_fw_subsumed:                        0
% 2.87/1.00  sim_bw_subsumed:                        0
% 2.87/1.00  sim_fw_subsumption_res:                 2
% 2.87/1.00  sim_bw_subsumption_res:                 0
% 2.87/1.00  sim_tautology_del:                      0
% 2.87/1.00  sim_eq_tautology_del:                   5
% 2.87/1.00  sim_eq_res_simp:                        0
% 2.87/1.00  sim_fw_demodulated:                     0
% 2.87/1.00  sim_bw_demodulated:                     37
% 2.87/1.00  sim_light_normalised:                   22
% 2.87/1.00  sim_joinable_taut:                      0
% 2.87/1.00  sim_joinable_simp:                      0
% 2.87/1.00  sim_ac_normalised:                      0
% 2.87/1.00  sim_smt_subsumption:                    0
% 2.87/1.00  
%------------------------------------------------------------------------------
