%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:00 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :  226 (6768 expanded)
%              Number of clauses        :  143 (1843 expanded)
%              Number of leaves         :   23 (1899 expanded)
%              Depth                    :   28
%              Number of atoms          :  677 (45859 expanded)
%              Number of equality atoms :  278 (14630 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25,conjecture,(
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

fof(f26,negated_conjecture,(
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
    inference(negated_conjecture,[],[f25])).

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f61,plain,(
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

fof(f60,plain,(
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

fof(f59,plain,
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

fof(f62,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f56,f61,f60,f59])).

fof(f99,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f62])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f88,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f96,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f94,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f42])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f95,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f97,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f98,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f62])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f100,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f20,axiom,(
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
    inference(ennf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f101,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f51])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f102,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f74,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f75,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f66,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f72,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1700,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_25,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_37,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_500,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_37])).

cnf(c_501,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_39,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_505,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_39])).

cnf(c_506,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_1738,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1700,c_501,c_506])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_15,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_21,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_512,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_15,c_21])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_516,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_512,c_21,c_15,c_14])).

cnf(c_517,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_516])).

cnf(c_556,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_18,c_517])).

cnf(c_560,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_556,c_21,c_18,c_15,c_14])).

cnf(c_561,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_560])).

cnf(c_1695,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_561])).

cnf(c_2614,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1738,c_1695])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_41,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_42,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_43,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_26,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_59,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(k2_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_61,plain,
    ( v2_struct_0(sK1) = iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_59])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1699,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1732,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1699,c_501,c_506])).

cnf(c_2974,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2614,c_41,c_42,c_43,c_61,c_1732])).

cnf(c_2981,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2974,c_1738])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1704,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4659,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2981,c_1704])).

cnf(c_33,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1735,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_33,c_501,c_506])).

cnf(c_2983,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_2974,c_1735])).

cnf(c_4823,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4659,c_2983])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_32,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_660,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_32])).

cnf(c_661,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_660])).

cnf(c_665,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_661,c_36])).

cnf(c_666,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_665])).

cnf(c_1691,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_666])).

cnf(c_2606,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1735,c_1691])).

cnf(c_2966,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2606,c_1738,c_1732])).

cnf(c_2971,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_struct_0(sK1)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2966,c_1695])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_612,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_32])).

cnf(c_613,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_612])).

cnf(c_617,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_613,c_36])).

cnf(c_618,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK2))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_617])).

cnf(c_1693,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_618])).

cnf(c_2167,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1735,c_1693])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_636,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_637,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(unflattening,[status(thm)],[c_636])).

cnf(c_641,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X1,X0)
    | v1_funct_2(k2_funct_1(sK2),X0,X1)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_637,c_36])).

cnf(c_642,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(renaming,[status(thm)],[c_641])).

cnf(c_1692,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(k2_funct_1(sK2),X1,X0) = iProver_top
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_2287,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1735,c_1692])).

cnf(c_3689,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_struct_0(sK1)
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2971,c_1738,c_1732,c_2167,c_2287])).

cnf(c_3693,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_struct_0(sK1)
    | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3689,c_2974])).

cnf(c_4833,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4823,c_3693])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1717,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1714,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4513,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1717,c_1714])).

cnf(c_7410,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4833,c_4513])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_588,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_32])).

cnf(c_589,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_588])).

cnf(c_593,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_589,c_36])).

cnf(c_594,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_593])).

cnf(c_1694,plain,
    ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_594])).

cnf(c_2407,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1735,c_1694])).

cnf(c_2470,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2407,c_1738,c_1732])).

cnf(c_31,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1809,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_31,c_501,c_506])).

cnf(c_2473,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_2470,c_1809])).

cnf(c_2978,plain,
    ( k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2)
    | k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_2974,c_2473])).

cnf(c_4834,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2)
    | k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4823,c_2978])).

cnf(c_2977,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2974,c_2966])).

cnf(c_4658,plain,
    ( k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2977,c_1704])).

cnf(c_6823,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(light_normalisation,[status(thm)],[c_4658,c_4823])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1705,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4675,plain,
    ( k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2977,c_1705])).

cnf(c_7139,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(light_normalisation,[status(thm)],[c_4675,c_4823])).

cnf(c_7239,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4834,c_6823,c_7139])).

cnf(c_7436,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_7410,c_7239])).

cnf(c_1706,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3463,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2977,c_1706])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1708,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3928,plain,
    ( k9_relat_1(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2))) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3463,c_1708])).

cnf(c_7438,plain,
    ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7410,c_3928])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_684,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_32])).

cnf(c_685,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_684])).

cnf(c_689,plain,
    ( ~ v1_relat_1(sK2)
    | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_685,c_36])).

cnf(c_1690,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_689])).

cnf(c_1967,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2040,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1690,c_36,c_34,c_685,c_1967])).

cnf(c_3392,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2981,c_1706])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1707,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3921,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3392,c_1707])).

cnf(c_7441,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_7438,c_2040,c_3921])).

cnf(c_7449,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7436,c_7441])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1711,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3261,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2981,c_1711])).

cnf(c_4832,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4823,c_3261])).

cnf(c_7553,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7449,c_4832])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1713,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5668,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1713,c_4513])).

cnf(c_7830,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1717,c_5668])).

cnf(c_9164,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7553,c_7830])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1715,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9168,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9164,c_1715])).

cnf(c_487,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_38])).

cnf(c_488,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_60,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_490,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_488,c_38,c_37,c_60])).

cnf(c_1696,plain,
    ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_490])).

cnf(c_4840,plain,
    ( v1_xboole_0(k2_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4823,c_1696])).

cnf(c_9268,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9168,c_4840])).

cnf(c_9,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1710,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5669,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1710,c_4513])).

cnf(c_6942,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1717,c_5669])).

cnf(c_9327,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9268,c_6942])).

cnf(c_131,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9327,c_131])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:53:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.17/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.00  
% 3.17/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.17/1.00  
% 3.17/1.00  ------  iProver source info
% 3.17/1.00  
% 3.17/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.17/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.17/1.00  git: non_committed_changes: false
% 3.17/1.00  git: last_make_outside_of_git: false
% 3.17/1.00  
% 3.17/1.00  ------ 
% 3.17/1.00  
% 3.17/1.00  ------ Input Options
% 3.17/1.00  
% 3.17/1.00  --out_options                           all
% 3.17/1.00  --tptp_safe_out                         true
% 3.17/1.00  --problem_path                          ""
% 3.17/1.00  --include_path                          ""
% 3.17/1.00  --clausifier                            res/vclausify_rel
% 3.17/1.00  --clausifier_options                    --mode clausify
% 3.17/1.00  --stdin                                 false
% 3.17/1.00  --stats_out                             all
% 3.17/1.00  
% 3.17/1.00  ------ General Options
% 3.17/1.00  
% 3.17/1.00  --fof                                   false
% 3.17/1.00  --time_out_real                         305.
% 3.17/1.00  --time_out_virtual                      -1.
% 3.17/1.00  --symbol_type_check                     false
% 3.17/1.00  --clausify_out                          false
% 3.17/1.00  --sig_cnt_out                           false
% 3.17/1.00  --trig_cnt_out                          false
% 3.17/1.00  --trig_cnt_out_tolerance                1.
% 3.17/1.00  --trig_cnt_out_sk_spl                   false
% 3.17/1.00  --abstr_cl_out                          false
% 3.17/1.00  
% 3.17/1.00  ------ Global Options
% 3.17/1.00  
% 3.17/1.00  --schedule                              default
% 3.17/1.00  --add_important_lit                     false
% 3.17/1.00  --prop_solver_per_cl                    1000
% 3.17/1.00  --min_unsat_core                        false
% 3.17/1.00  --soft_assumptions                      false
% 3.17/1.00  --soft_lemma_size                       3
% 3.17/1.00  --prop_impl_unit_size                   0
% 3.17/1.00  --prop_impl_unit                        []
% 3.17/1.00  --share_sel_clauses                     true
% 3.17/1.00  --reset_solvers                         false
% 3.17/1.00  --bc_imp_inh                            [conj_cone]
% 3.17/1.00  --conj_cone_tolerance                   3.
% 3.17/1.00  --extra_neg_conj                        none
% 3.17/1.00  --large_theory_mode                     true
% 3.17/1.00  --prolific_symb_bound                   200
% 3.17/1.00  --lt_threshold                          2000
% 3.17/1.00  --clause_weak_htbl                      true
% 3.17/1.00  --gc_record_bc_elim                     false
% 3.17/1.00  
% 3.17/1.00  ------ Preprocessing Options
% 3.17/1.00  
% 3.17/1.00  --preprocessing_flag                    true
% 3.17/1.00  --time_out_prep_mult                    0.1
% 3.17/1.00  --splitting_mode                        input
% 3.17/1.00  --splitting_grd                         true
% 3.17/1.00  --splitting_cvd                         false
% 3.17/1.00  --splitting_cvd_svl                     false
% 3.17/1.00  --splitting_nvd                         32
% 3.17/1.00  --sub_typing                            true
% 3.17/1.00  --prep_gs_sim                           true
% 3.17/1.00  --prep_unflatten                        true
% 3.17/1.00  --prep_res_sim                          true
% 3.17/1.00  --prep_upred                            true
% 3.17/1.00  --prep_sem_filter                       exhaustive
% 3.17/1.00  --prep_sem_filter_out                   false
% 3.17/1.00  --pred_elim                             true
% 3.17/1.00  --res_sim_input                         true
% 3.17/1.00  --eq_ax_congr_red                       true
% 3.17/1.00  --pure_diseq_elim                       true
% 3.17/1.00  --brand_transform                       false
% 3.17/1.00  --non_eq_to_eq                          false
% 3.17/1.00  --prep_def_merge                        true
% 3.17/1.00  --prep_def_merge_prop_impl              false
% 3.17/1.00  --prep_def_merge_mbd                    true
% 3.17/1.00  --prep_def_merge_tr_red                 false
% 3.17/1.00  --prep_def_merge_tr_cl                  false
% 3.17/1.00  --smt_preprocessing                     true
% 3.17/1.00  --smt_ac_axioms                         fast
% 3.17/1.00  --preprocessed_out                      false
% 3.17/1.00  --preprocessed_stats                    false
% 3.17/1.00  
% 3.17/1.00  ------ Abstraction refinement Options
% 3.17/1.00  
% 3.17/1.00  --abstr_ref                             []
% 3.17/1.00  --abstr_ref_prep                        false
% 3.17/1.00  --abstr_ref_until_sat                   false
% 3.17/1.00  --abstr_ref_sig_restrict                funpre
% 3.17/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.17/1.00  --abstr_ref_under                       []
% 3.17/1.00  
% 3.17/1.00  ------ SAT Options
% 3.17/1.00  
% 3.17/1.00  --sat_mode                              false
% 3.17/1.00  --sat_fm_restart_options                ""
% 3.17/1.00  --sat_gr_def                            false
% 3.17/1.00  --sat_epr_types                         true
% 3.17/1.00  --sat_non_cyclic_types                  false
% 3.17/1.00  --sat_finite_models                     false
% 3.17/1.00  --sat_fm_lemmas                         false
% 3.17/1.00  --sat_fm_prep                           false
% 3.17/1.00  --sat_fm_uc_incr                        true
% 3.17/1.00  --sat_out_model                         small
% 3.17/1.00  --sat_out_clauses                       false
% 3.17/1.00  
% 3.17/1.00  ------ QBF Options
% 3.17/1.00  
% 3.17/1.00  --qbf_mode                              false
% 3.17/1.00  --qbf_elim_univ                         false
% 3.17/1.00  --qbf_dom_inst                          none
% 3.17/1.00  --qbf_dom_pre_inst                      false
% 3.17/1.00  --qbf_sk_in                             false
% 3.17/1.00  --qbf_pred_elim                         true
% 3.17/1.00  --qbf_split                             512
% 3.17/1.00  
% 3.17/1.00  ------ BMC1 Options
% 3.17/1.00  
% 3.17/1.00  --bmc1_incremental                      false
% 3.17/1.00  --bmc1_axioms                           reachable_all
% 3.17/1.00  --bmc1_min_bound                        0
% 3.17/1.00  --bmc1_max_bound                        -1
% 3.17/1.00  --bmc1_max_bound_default                -1
% 3.17/1.00  --bmc1_symbol_reachability              true
% 3.17/1.00  --bmc1_property_lemmas                  false
% 3.17/1.00  --bmc1_k_induction                      false
% 3.17/1.00  --bmc1_non_equiv_states                 false
% 3.17/1.00  --bmc1_deadlock                         false
% 3.17/1.00  --bmc1_ucm                              false
% 3.17/1.00  --bmc1_add_unsat_core                   none
% 3.17/1.00  --bmc1_unsat_core_children              false
% 3.17/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.17/1.00  --bmc1_out_stat                         full
% 3.17/1.00  --bmc1_ground_init                      false
% 3.17/1.00  --bmc1_pre_inst_next_state              false
% 3.17/1.00  --bmc1_pre_inst_state                   false
% 3.17/1.00  --bmc1_pre_inst_reach_state             false
% 3.17/1.00  --bmc1_out_unsat_core                   false
% 3.17/1.00  --bmc1_aig_witness_out                  false
% 3.17/1.00  --bmc1_verbose                          false
% 3.17/1.00  --bmc1_dump_clauses_tptp                false
% 3.17/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.17/1.00  --bmc1_dump_file                        -
% 3.17/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.17/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.17/1.00  --bmc1_ucm_extend_mode                  1
% 3.17/1.00  --bmc1_ucm_init_mode                    2
% 3.17/1.00  --bmc1_ucm_cone_mode                    none
% 3.17/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.17/1.00  --bmc1_ucm_relax_model                  4
% 3.17/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.17/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.17/1.00  --bmc1_ucm_layered_model                none
% 3.17/1.00  --bmc1_ucm_max_lemma_size               10
% 3.17/1.00  
% 3.17/1.00  ------ AIG Options
% 3.17/1.00  
% 3.17/1.00  --aig_mode                              false
% 3.17/1.00  
% 3.17/1.00  ------ Instantiation Options
% 3.17/1.00  
% 3.17/1.00  --instantiation_flag                    true
% 3.17/1.00  --inst_sos_flag                         false
% 3.17/1.00  --inst_sos_phase                        true
% 3.17/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.17/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.17/1.00  --inst_lit_sel_side                     num_symb
% 3.17/1.00  --inst_solver_per_active                1400
% 3.17/1.00  --inst_solver_calls_frac                1.
% 3.17/1.00  --inst_passive_queue_type               priority_queues
% 3.17/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.17/1.00  --inst_passive_queues_freq              [25;2]
% 3.17/1.00  --inst_dismatching                      true
% 3.17/1.00  --inst_eager_unprocessed_to_passive     true
% 3.17/1.00  --inst_prop_sim_given                   true
% 3.17/1.00  --inst_prop_sim_new                     false
% 3.17/1.00  --inst_subs_new                         false
% 3.17/1.00  --inst_eq_res_simp                      false
% 3.17/1.00  --inst_subs_given                       false
% 3.17/1.00  --inst_orphan_elimination               true
% 3.17/1.00  --inst_learning_loop_flag               true
% 3.17/1.00  --inst_learning_start                   3000
% 3.17/1.00  --inst_learning_factor                  2
% 3.17/1.00  --inst_start_prop_sim_after_learn       3
% 3.17/1.00  --inst_sel_renew                        solver
% 3.17/1.00  --inst_lit_activity_flag                true
% 3.17/1.00  --inst_restr_to_given                   false
% 3.17/1.00  --inst_activity_threshold               500
% 3.17/1.00  --inst_out_proof                        true
% 3.17/1.00  
% 3.17/1.00  ------ Resolution Options
% 3.17/1.00  
% 3.17/1.00  --resolution_flag                       true
% 3.17/1.00  --res_lit_sel                           adaptive
% 3.17/1.00  --res_lit_sel_side                      none
% 3.17/1.00  --res_ordering                          kbo
% 3.17/1.00  --res_to_prop_solver                    active
% 3.17/1.00  --res_prop_simpl_new                    false
% 3.17/1.00  --res_prop_simpl_given                  true
% 3.17/1.00  --res_passive_queue_type                priority_queues
% 3.17/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.17/1.00  --res_passive_queues_freq               [15;5]
% 3.17/1.00  --res_forward_subs                      full
% 3.17/1.00  --res_backward_subs                     full
% 3.17/1.00  --res_forward_subs_resolution           true
% 3.17/1.00  --res_backward_subs_resolution          true
% 3.17/1.00  --res_orphan_elimination                true
% 3.17/1.00  --res_time_limit                        2.
% 3.17/1.00  --res_out_proof                         true
% 3.17/1.00  
% 3.17/1.00  ------ Superposition Options
% 3.17/1.00  
% 3.17/1.00  --superposition_flag                    true
% 3.17/1.00  --sup_passive_queue_type                priority_queues
% 3.17/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.17/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.17/1.00  --demod_completeness_check              fast
% 3.17/1.00  --demod_use_ground                      true
% 3.17/1.00  --sup_to_prop_solver                    passive
% 3.17/1.00  --sup_prop_simpl_new                    true
% 3.17/1.00  --sup_prop_simpl_given                  true
% 3.17/1.00  --sup_fun_splitting                     false
% 3.17/1.00  --sup_smt_interval                      50000
% 3.17/1.00  
% 3.17/1.00  ------ Superposition Simplification Setup
% 3.17/1.00  
% 3.17/1.00  --sup_indices_passive                   []
% 3.17/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.17/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/1.00  --sup_full_bw                           [BwDemod]
% 3.17/1.00  --sup_immed_triv                        [TrivRules]
% 3.17/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.17/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/1.00  --sup_immed_bw_main                     []
% 3.17/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.17/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/1.00  
% 3.17/1.00  ------ Combination Options
% 3.17/1.00  
% 3.17/1.00  --comb_res_mult                         3
% 3.17/1.00  --comb_sup_mult                         2
% 3.17/1.00  --comb_inst_mult                        10
% 3.17/1.00  
% 3.17/1.00  ------ Debug Options
% 3.17/1.00  
% 3.17/1.00  --dbg_backtrace                         false
% 3.17/1.00  --dbg_dump_prop_clauses                 false
% 3.17/1.00  --dbg_dump_prop_clauses_file            -
% 3.17/1.00  --dbg_out_stat                          false
% 3.17/1.00  ------ Parsing...
% 3.17/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.17/1.00  
% 3.17/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.17/1.00  
% 3.17/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.17/1.00  
% 3.17/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.17/1.00  ------ Proving...
% 3.17/1.00  ------ Problem Properties 
% 3.17/1.00  
% 3.17/1.00  
% 3.17/1.00  clauses                                 33
% 3.17/1.00  conjectures                             5
% 3.17/1.00  EPR                                     5
% 3.17/1.00  Horn                                    32
% 3.17/1.00  unary                                   10
% 3.17/1.00  binary                                  13
% 3.17/1.00  lits                                    75
% 3.17/1.00  lits eq                                 19
% 3.17/1.00  fd_pure                                 0
% 3.17/1.00  fd_pseudo                               0
% 3.17/1.00  fd_cond                                 1
% 3.17/1.00  fd_pseudo_cond                          2
% 3.17/1.00  AC symbols                              0
% 3.17/1.00  
% 3.17/1.00  ------ Schedule dynamic 5 is on 
% 3.17/1.00  
% 3.17/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.17/1.00  
% 3.17/1.00  
% 3.17/1.00  ------ 
% 3.17/1.00  Current options:
% 3.17/1.00  ------ 
% 3.17/1.00  
% 3.17/1.00  ------ Input Options
% 3.17/1.00  
% 3.17/1.00  --out_options                           all
% 3.17/1.00  --tptp_safe_out                         true
% 3.17/1.00  --problem_path                          ""
% 3.17/1.00  --include_path                          ""
% 3.17/1.00  --clausifier                            res/vclausify_rel
% 3.17/1.00  --clausifier_options                    --mode clausify
% 3.17/1.00  --stdin                                 false
% 3.17/1.00  --stats_out                             all
% 3.17/1.00  
% 3.17/1.00  ------ General Options
% 3.17/1.00  
% 3.17/1.00  --fof                                   false
% 3.17/1.00  --time_out_real                         305.
% 3.17/1.00  --time_out_virtual                      -1.
% 3.17/1.00  --symbol_type_check                     false
% 3.17/1.00  --clausify_out                          false
% 3.17/1.00  --sig_cnt_out                           false
% 3.17/1.00  --trig_cnt_out                          false
% 3.17/1.00  --trig_cnt_out_tolerance                1.
% 3.17/1.00  --trig_cnt_out_sk_spl                   false
% 3.17/1.00  --abstr_cl_out                          false
% 3.17/1.00  
% 3.17/1.00  ------ Global Options
% 3.17/1.00  
% 3.17/1.00  --schedule                              default
% 3.17/1.00  --add_important_lit                     false
% 3.17/1.00  --prop_solver_per_cl                    1000
% 3.17/1.00  --min_unsat_core                        false
% 3.17/1.00  --soft_assumptions                      false
% 3.17/1.00  --soft_lemma_size                       3
% 3.17/1.00  --prop_impl_unit_size                   0
% 3.17/1.00  --prop_impl_unit                        []
% 3.17/1.00  --share_sel_clauses                     true
% 3.17/1.00  --reset_solvers                         false
% 3.17/1.00  --bc_imp_inh                            [conj_cone]
% 3.17/1.00  --conj_cone_tolerance                   3.
% 3.17/1.00  --extra_neg_conj                        none
% 3.17/1.00  --large_theory_mode                     true
% 3.17/1.00  --prolific_symb_bound                   200
% 3.17/1.00  --lt_threshold                          2000
% 3.17/1.00  --clause_weak_htbl                      true
% 3.17/1.00  --gc_record_bc_elim                     false
% 3.17/1.00  
% 3.17/1.00  ------ Preprocessing Options
% 3.17/1.00  
% 3.17/1.00  --preprocessing_flag                    true
% 3.17/1.00  --time_out_prep_mult                    0.1
% 3.17/1.00  --splitting_mode                        input
% 3.17/1.00  --splitting_grd                         true
% 3.17/1.00  --splitting_cvd                         false
% 3.17/1.00  --splitting_cvd_svl                     false
% 3.17/1.00  --splitting_nvd                         32
% 3.17/1.00  --sub_typing                            true
% 3.17/1.00  --prep_gs_sim                           true
% 3.17/1.00  --prep_unflatten                        true
% 3.17/1.00  --prep_res_sim                          true
% 3.17/1.00  --prep_upred                            true
% 3.17/1.00  --prep_sem_filter                       exhaustive
% 3.17/1.00  --prep_sem_filter_out                   false
% 3.17/1.00  --pred_elim                             true
% 3.17/1.00  --res_sim_input                         true
% 3.17/1.00  --eq_ax_congr_red                       true
% 3.17/1.00  --pure_diseq_elim                       true
% 3.17/1.00  --brand_transform                       false
% 3.17/1.00  --non_eq_to_eq                          false
% 3.17/1.00  --prep_def_merge                        true
% 3.17/1.00  --prep_def_merge_prop_impl              false
% 3.17/1.00  --prep_def_merge_mbd                    true
% 3.17/1.00  --prep_def_merge_tr_red                 false
% 3.17/1.00  --prep_def_merge_tr_cl                  false
% 3.17/1.00  --smt_preprocessing                     true
% 3.17/1.00  --smt_ac_axioms                         fast
% 3.17/1.00  --preprocessed_out                      false
% 3.17/1.00  --preprocessed_stats                    false
% 3.17/1.00  
% 3.17/1.00  ------ Abstraction refinement Options
% 3.17/1.00  
% 3.17/1.00  --abstr_ref                             []
% 3.17/1.00  --abstr_ref_prep                        false
% 3.17/1.00  --abstr_ref_until_sat                   false
% 3.17/1.00  --abstr_ref_sig_restrict                funpre
% 3.17/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.17/1.00  --abstr_ref_under                       []
% 3.17/1.00  
% 3.17/1.00  ------ SAT Options
% 3.17/1.00  
% 3.17/1.00  --sat_mode                              false
% 3.17/1.00  --sat_fm_restart_options                ""
% 3.17/1.00  --sat_gr_def                            false
% 3.17/1.00  --sat_epr_types                         true
% 3.17/1.00  --sat_non_cyclic_types                  false
% 3.17/1.00  --sat_finite_models                     false
% 3.17/1.00  --sat_fm_lemmas                         false
% 3.17/1.00  --sat_fm_prep                           false
% 3.17/1.00  --sat_fm_uc_incr                        true
% 3.17/1.00  --sat_out_model                         small
% 3.17/1.00  --sat_out_clauses                       false
% 3.17/1.00  
% 3.17/1.00  ------ QBF Options
% 3.17/1.00  
% 3.17/1.00  --qbf_mode                              false
% 3.17/1.00  --qbf_elim_univ                         false
% 3.17/1.00  --qbf_dom_inst                          none
% 3.17/1.00  --qbf_dom_pre_inst                      false
% 3.17/1.00  --qbf_sk_in                             false
% 3.17/1.00  --qbf_pred_elim                         true
% 3.17/1.00  --qbf_split                             512
% 3.17/1.00  
% 3.17/1.00  ------ BMC1 Options
% 3.17/1.00  
% 3.17/1.00  --bmc1_incremental                      false
% 3.17/1.00  --bmc1_axioms                           reachable_all
% 3.17/1.00  --bmc1_min_bound                        0
% 3.17/1.00  --bmc1_max_bound                        -1
% 3.17/1.00  --bmc1_max_bound_default                -1
% 3.17/1.00  --bmc1_symbol_reachability              true
% 3.17/1.00  --bmc1_property_lemmas                  false
% 3.17/1.00  --bmc1_k_induction                      false
% 3.17/1.00  --bmc1_non_equiv_states                 false
% 3.17/1.00  --bmc1_deadlock                         false
% 3.17/1.00  --bmc1_ucm                              false
% 3.17/1.00  --bmc1_add_unsat_core                   none
% 3.17/1.00  --bmc1_unsat_core_children              false
% 3.17/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.17/1.00  --bmc1_out_stat                         full
% 3.17/1.00  --bmc1_ground_init                      false
% 3.17/1.00  --bmc1_pre_inst_next_state              false
% 3.17/1.00  --bmc1_pre_inst_state                   false
% 3.17/1.00  --bmc1_pre_inst_reach_state             false
% 3.17/1.00  --bmc1_out_unsat_core                   false
% 3.17/1.00  --bmc1_aig_witness_out                  false
% 3.17/1.00  --bmc1_verbose                          false
% 3.17/1.00  --bmc1_dump_clauses_tptp                false
% 3.17/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.17/1.00  --bmc1_dump_file                        -
% 3.17/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.17/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.17/1.00  --bmc1_ucm_extend_mode                  1
% 3.17/1.00  --bmc1_ucm_init_mode                    2
% 3.17/1.00  --bmc1_ucm_cone_mode                    none
% 3.17/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.17/1.00  --bmc1_ucm_relax_model                  4
% 3.17/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.17/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.17/1.00  --bmc1_ucm_layered_model                none
% 3.17/1.00  --bmc1_ucm_max_lemma_size               10
% 3.17/1.00  
% 3.17/1.00  ------ AIG Options
% 3.17/1.00  
% 3.17/1.00  --aig_mode                              false
% 3.17/1.00  
% 3.17/1.00  ------ Instantiation Options
% 3.17/1.00  
% 3.17/1.00  --instantiation_flag                    true
% 3.17/1.00  --inst_sos_flag                         false
% 3.17/1.00  --inst_sos_phase                        true
% 3.17/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.17/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.17/1.00  --inst_lit_sel_side                     none
% 3.17/1.00  --inst_solver_per_active                1400
% 3.17/1.00  --inst_solver_calls_frac                1.
% 3.17/1.00  --inst_passive_queue_type               priority_queues
% 3.17/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.17/1.00  --inst_passive_queues_freq              [25;2]
% 3.17/1.00  --inst_dismatching                      true
% 3.17/1.00  --inst_eager_unprocessed_to_passive     true
% 3.17/1.00  --inst_prop_sim_given                   true
% 3.17/1.00  --inst_prop_sim_new                     false
% 3.17/1.00  --inst_subs_new                         false
% 3.17/1.00  --inst_eq_res_simp                      false
% 3.17/1.00  --inst_subs_given                       false
% 3.17/1.00  --inst_orphan_elimination               true
% 3.17/1.00  --inst_learning_loop_flag               true
% 3.17/1.00  --inst_learning_start                   3000
% 3.17/1.00  --inst_learning_factor                  2
% 3.17/1.00  --inst_start_prop_sim_after_learn       3
% 3.17/1.00  --inst_sel_renew                        solver
% 3.17/1.00  --inst_lit_activity_flag                true
% 3.17/1.00  --inst_restr_to_given                   false
% 3.17/1.00  --inst_activity_threshold               500
% 3.17/1.00  --inst_out_proof                        true
% 3.17/1.00  
% 3.17/1.00  ------ Resolution Options
% 3.17/1.00  
% 3.17/1.00  --resolution_flag                       false
% 3.17/1.00  --res_lit_sel                           adaptive
% 3.17/1.00  --res_lit_sel_side                      none
% 3.17/1.00  --res_ordering                          kbo
% 3.17/1.00  --res_to_prop_solver                    active
% 3.17/1.00  --res_prop_simpl_new                    false
% 3.17/1.00  --res_prop_simpl_given                  true
% 3.17/1.00  --res_passive_queue_type                priority_queues
% 3.17/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.17/1.00  --res_passive_queues_freq               [15;5]
% 3.17/1.00  --res_forward_subs                      full
% 3.17/1.00  --res_backward_subs                     full
% 3.17/1.00  --res_forward_subs_resolution           true
% 3.17/1.00  --res_backward_subs_resolution          true
% 3.17/1.00  --res_orphan_elimination                true
% 3.17/1.00  --res_time_limit                        2.
% 3.17/1.00  --res_out_proof                         true
% 3.17/1.00  
% 3.17/1.00  ------ Superposition Options
% 3.17/1.00  
% 3.17/1.00  --superposition_flag                    true
% 3.17/1.00  --sup_passive_queue_type                priority_queues
% 3.17/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.17/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.17/1.00  --demod_completeness_check              fast
% 3.17/1.00  --demod_use_ground                      true
% 3.17/1.00  --sup_to_prop_solver                    passive
% 3.17/1.00  --sup_prop_simpl_new                    true
% 3.17/1.00  --sup_prop_simpl_given                  true
% 3.17/1.00  --sup_fun_splitting                     false
% 3.17/1.00  --sup_smt_interval                      50000
% 3.17/1.00  
% 3.17/1.00  ------ Superposition Simplification Setup
% 3.17/1.00  
% 3.17/1.00  --sup_indices_passive                   []
% 3.17/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.17/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/1.00  --sup_full_bw                           [BwDemod]
% 3.17/1.00  --sup_immed_triv                        [TrivRules]
% 3.17/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.17/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/1.00  --sup_immed_bw_main                     []
% 3.17/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.17/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/1.00  
% 3.17/1.00  ------ Combination Options
% 3.17/1.00  
% 3.17/1.00  --comb_res_mult                         3
% 3.17/1.00  --comb_sup_mult                         2
% 3.17/1.00  --comb_inst_mult                        10
% 3.17/1.00  
% 3.17/1.00  ------ Debug Options
% 3.17/1.00  
% 3.17/1.00  --dbg_backtrace                         false
% 3.17/1.00  --dbg_dump_prop_clauses                 false
% 3.17/1.00  --dbg_dump_prop_clauses_file            -
% 3.17/1.00  --dbg_out_stat                          false
% 3.17/1.00  
% 3.17/1.00  
% 3.17/1.00  
% 3.17/1.00  
% 3.17/1.00  ------ Proving...
% 3.17/1.00  
% 3.17/1.00  
% 3.17/1.00  % SZS status Theorem for theBenchmark.p
% 3.17/1.00  
% 3.17/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.17/1.00  
% 3.17/1.00  fof(f25,conjecture,(
% 3.17/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 3.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f26,negated_conjecture,(
% 3.17/1.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 3.17/1.00    inference(negated_conjecture,[],[f25])).
% 3.17/1.00  
% 3.17/1.00  fof(f55,plain,(
% 3.17/1.00    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 3.17/1.00    inference(ennf_transformation,[],[f26])).
% 3.17/1.00  
% 3.17/1.00  fof(f56,plain,(
% 3.17/1.00    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 3.17/1.00    inference(flattening,[],[f55])).
% 3.17/1.00  
% 3.17/1.00  fof(f61,plain,(
% 3.17/1.00    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 3.17/1.00    introduced(choice_axiom,[])).
% 3.17/1.00  
% 3.17/1.00  fof(f60,plain,(
% 3.17/1.00    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 3.17/1.00    introduced(choice_axiom,[])).
% 3.17/1.00  
% 3.17/1.00  fof(f59,plain,(
% 3.17/1.00    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 3.17/1.00    introduced(choice_axiom,[])).
% 3.17/1.00  
% 3.17/1.00  fof(f62,plain,(
% 3.17/1.00    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 3.17/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f56,f61,f60,f59])).
% 3.17/1.00  
% 3.17/1.00  fof(f99,plain,(
% 3.17/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.17/1.00    inference(cnf_transformation,[],[f62])).
% 3.17/1.00  
% 3.17/1.00  fof(f21,axiom,(
% 3.17/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f48,plain,(
% 3.17/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.17/1.00    inference(ennf_transformation,[],[f21])).
% 3.17/1.00  
% 3.17/1.00  fof(f88,plain,(
% 3.17/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f48])).
% 3.17/1.00  
% 3.17/1.00  fof(f96,plain,(
% 3.17/1.00    l1_struct_0(sK1)),
% 3.17/1.00    inference(cnf_transformation,[],[f62])).
% 3.17/1.00  
% 3.17/1.00  fof(f94,plain,(
% 3.17/1.00    l1_struct_0(sK0)),
% 3.17/1.00    inference(cnf_transformation,[],[f62])).
% 3.17/1.00  
% 3.17/1.00  fof(f18,axiom,(
% 3.17/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f42,plain,(
% 3.17/1.00    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.17/1.00    inference(ennf_transformation,[],[f18])).
% 3.17/1.00  
% 3.17/1.00  fof(f43,plain,(
% 3.17/1.00    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.17/1.00    inference(flattening,[],[f42])).
% 3.17/1.00  
% 3.17/1.00  fof(f82,plain,(
% 3.17/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f43])).
% 3.17/1.00  
% 3.17/1.00  fof(f15,axiom,(
% 3.17/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f27,plain,(
% 3.17/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.17/1.00    inference(pure_predicate_removal,[],[f15])).
% 3.17/1.00  
% 3.17/1.00  fof(f39,plain,(
% 3.17/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.17/1.00    inference(ennf_transformation,[],[f27])).
% 3.17/1.00  
% 3.17/1.00  fof(f78,plain,(
% 3.17/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.17/1.00    inference(cnf_transformation,[],[f39])).
% 3.17/1.00  
% 3.17/1.00  fof(f19,axiom,(
% 3.17/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f44,plain,(
% 3.17/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.17/1.00    inference(ennf_transformation,[],[f19])).
% 3.17/1.00  
% 3.17/1.00  fof(f45,plain,(
% 3.17/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.17/1.00    inference(flattening,[],[f44])).
% 3.17/1.00  
% 3.17/1.00  fof(f58,plain,(
% 3.17/1.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.17/1.00    inference(nnf_transformation,[],[f45])).
% 3.17/1.00  
% 3.17/1.00  fof(f83,plain,(
% 3.17/1.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f58])).
% 3.17/1.00  
% 3.17/1.00  fof(f14,axiom,(
% 3.17/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f38,plain,(
% 3.17/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.17/1.00    inference(ennf_transformation,[],[f14])).
% 3.17/1.00  
% 3.17/1.00  fof(f77,plain,(
% 3.17/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.17/1.00    inference(cnf_transformation,[],[f38])).
% 3.17/1.00  
% 3.17/1.00  fof(f95,plain,(
% 3.17/1.00    ~v2_struct_0(sK1)),
% 3.17/1.00    inference(cnf_transformation,[],[f62])).
% 3.17/1.00  
% 3.17/1.00  fof(f97,plain,(
% 3.17/1.00    v1_funct_1(sK2)),
% 3.17/1.00    inference(cnf_transformation,[],[f62])).
% 3.17/1.00  
% 3.17/1.00  fof(f22,axiom,(
% 3.17/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 3.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f49,plain,(
% 3.17/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.17/1.00    inference(ennf_transformation,[],[f22])).
% 3.17/1.00  
% 3.17/1.00  fof(f50,plain,(
% 3.17/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.17/1.00    inference(flattening,[],[f49])).
% 3.17/1.00  
% 3.17/1.00  fof(f89,plain,(
% 3.17/1.00    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f50])).
% 3.17/1.00  
% 3.17/1.00  fof(f98,plain,(
% 3.17/1.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.17/1.00    inference(cnf_transformation,[],[f62])).
% 3.17/1.00  
% 3.17/1.00  fof(f17,axiom,(
% 3.17/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f41,plain,(
% 3.17/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.17/1.00    inference(ennf_transformation,[],[f17])).
% 3.17/1.00  
% 3.17/1.00  fof(f80,plain,(
% 3.17/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.17/1.00    inference(cnf_transformation,[],[f41])).
% 3.17/1.00  
% 3.17/1.00  fof(f100,plain,(
% 3.17/1.00    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 3.17/1.00    inference(cnf_transformation,[],[f62])).
% 3.17/1.00  
% 3.17/1.00  fof(f20,axiom,(
% 3.17/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f46,plain,(
% 3.17/1.00    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.17/1.00    inference(ennf_transformation,[],[f20])).
% 3.17/1.00  
% 3.17/1.00  fof(f47,plain,(
% 3.17/1.00    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.17/1.00    inference(flattening,[],[f46])).
% 3.17/1.00  
% 3.17/1.00  fof(f87,plain,(
% 3.17/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f47])).
% 3.17/1.00  
% 3.17/1.00  fof(f101,plain,(
% 3.17/1.00    v2_funct_1(sK2)),
% 3.17/1.00    inference(cnf_transformation,[],[f62])).
% 3.17/1.00  
% 3.17/1.00  fof(f85,plain,(
% 3.17/1.00    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f47])).
% 3.17/1.00  
% 3.17/1.00  fof(f86,plain,(
% 3.17/1.00    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f47])).
% 3.17/1.00  
% 3.17/1.00  fof(f1,axiom,(
% 3.17/1.00    v1_xboole_0(k1_xboole_0)),
% 3.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f63,plain,(
% 3.17/1.00    v1_xboole_0(k1_xboole_0)),
% 3.17/1.00    inference(cnf_transformation,[],[f1])).
% 3.17/1.00  
% 3.17/1.00  fof(f5,axiom,(
% 3.17/1.00    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f30,plain,(
% 3.17/1.00    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.17/1.00    inference(ennf_transformation,[],[f5])).
% 3.17/1.00  
% 3.17/1.00  fof(f67,plain,(
% 3.17/1.00    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f30])).
% 3.17/1.00  
% 3.17/1.00  fof(f23,axiom,(
% 3.17/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 3.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f51,plain,(
% 3.17/1.00    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.17/1.00    inference(ennf_transformation,[],[f23])).
% 3.17/1.00  
% 3.17/1.00  fof(f52,plain,(
% 3.17/1.00    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.17/1.00    inference(flattening,[],[f51])).
% 3.17/1.00  
% 3.17/1.00  fof(f90,plain,(
% 3.17/1.00    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f52])).
% 3.17/1.00  
% 3.17/1.00  fof(f102,plain,(
% 3.17/1.00    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 3.17/1.00    inference(cnf_transformation,[],[f62])).
% 3.17/1.00  
% 3.17/1.00  fof(f16,axiom,(
% 3.17/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f40,plain,(
% 3.17/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.17/1.00    inference(ennf_transformation,[],[f16])).
% 3.17/1.00  
% 3.17/1.00  fof(f79,plain,(
% 3.17/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.17/1.00    inference(cnf_transformation,[],[f40])).
% 3.17/1.00  
% 3.17/1.00  fof(f11,axiom,(
% 3.17/1.00    ! [X0] : (v1_relat_1(X0) => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)))),
% 3.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f34,plain,(
% 3.17/1.00    ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.17/1.00    inference(ennf_transformation,[],[f11])).
% 3.17/1.00  
% 3.17/1.00  fof(f74,plain,(
% 3.17/1.00    ( ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f34])).
% 3.17/1.00  
% 3.17/1.00  fof(f13,axiom,(
% 3.17/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)))),
% 3.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f36,plain,(
% 3.17/1.00    ! [X0,X1] : ((k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.17/1.00    inference(ennf_transformation,[],[f13])).
% 3.17/1.00  
% 3.17/1.00  fof(f37,plain,(
% 3.17/1.00    ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.17/1.00    inference(flattening,[],[f36])).
% 3.17/1.00  
% 3.17/1.00  fof(f76,plain,(
% 3.17/1.00    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f37])).
% 3.17/1.00  
% 3.17/1.00  fof(f12,axiom,(
% 3.17/1.00    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 3.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f35,plain,(
% 3.17/1.00    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.17/1.00    inference(ennf_transformation,[],[f12])).
% 3.17/1.00  
% 3.17/1.00  fof(f75,plain,(
% 3.17/1.00    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f35])).
% 3.17/1.00  
% 3.17/1.00  fof(f7,axiom,(
% 3.17/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f57,plain,(
% 3.17/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.17/1.00    inference(nnf_transformation,[],[f7])).
% 3.17/1.00  
% 3.17/1.00  fof(f69,plain,(
% 3.17/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.17/1.00    inference(cnf_transformation,[],[f57])).
% 3.17/1.00  
% 3.17/1.00  fof(f6,axiom,(
% 3.17/1.00    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f31,plain,(
% 3.17/1.00    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 3.17/1.00    inference(ennf_transformation,[],[f6])).
% 3.17/1.00  
% 3.17/1.00  fof(f68,plain,(
% 3.17/1.00    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f31])).
% 3.17/1.00  
% 3.17/1.00  fof(f4,axiom,(
% 3.17/1.00    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f29,plain,(
% 3.17/1.00    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.17/1.00    inference(ennf_transformation,[],[f4])).
% 3.17/1.00  
% 3.17/1.00  fof(f66,plain,(
% 3.17/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f29])).
% 3.17/1.00  
% 3.17/1.00  fof(f9,axiom,(
% 3.17/1.00    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 3.17/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.17/1.00  
% 3.17/1.00  fof(f33,plain,(
% 3.17/1.00    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 3.17/1.00    inference(ennf_transformation,[],[f9])).
% 3.17/1.00  
% 3.17/1.00  fof(f72,plain,(
% 3.17/1.00    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.17/1.00    inference(cnf_transformation,[],[f33])).
% 3.17/1.00  
% 3.17/1.00  cnf(c_34,negated_conjecture,
% 3.17/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.17/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1700,plain,
% 3.17/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_25,plain,
% 3.17/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.17/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_37,negated_conjecture,
% 3.17/1.00      ( l1_struct_0(sK1) ),
% 3.17/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_500,plain,
% 3.17/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 3.17/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_37]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_501,plain,
% 3.17/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.17/1.00      inference(unflattening,[status(thm)],[c_500]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_39,negated_conjecture,
% 3.17/1.00      ( l1_struct_0(sK0) ),
% 3.17/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_505,plain,
% 3.17/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 3.17/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_39]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_506,plain,
% 3.17/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.17/1.00      inference(unflattening,[status(thm)],[c_505]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1738,plain,
% 3.17/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 3.17/1.00      inference(light_normalisation,[status(thm)],[c_1700,c_501,c_506]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_18,plain,
% 3.17/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.17/1.00      | v1_partfun1(X0,X1)
% 3.17/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | ~ v1_funct_1(X0)
% 3.17/1.00      | v1_xboole_0(X2) ),
% 3.17/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_15,plain,
% 3.17/1.00      ( v4_relat_1(X0,X1)
% 3.17/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.17/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_21,plain,
% 3.17/1.00      ( ~ v1_partfun1(X0,X1)
% 3.17/1.00      | ~ v4_relat_1(X0,X1)
% 3.17/1.00      | ~ v1_relat_1(X0)
% 3.17/1.00      | k1_relat_1(X0) = X1 ),
% 3.17/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_512,plain,
% 3.17/1.00      ( ~ v1_partfun1(X0,X1)
% 3.17/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | ~ v1_relat_1(X0)
% 3.17/1.00      | k1_relat_1(X0) = X1 ),
% 3.17/1.00      inference(resolution,[status(thm)],[c_15,c_21]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_14,plain,
% 3.17/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | v1_relat_1(X0) ),
% 3.17/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_516,plain,
% 3.17/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | ~ v1_partfun1(X0,X1)
% 3.17/1.00      | k1_relat_1(X0) = X1 ),
% 3.17/1.00      inference(global_propositional_subsumption,
% 3.17/1.00                [status(thm)],
% 3.17/1.00                [c_512,c_21,c_15,c_14]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_517,plain,
% 3.17/1.00      ( ~ v1_partfun1(X0,X1)
% 3.17/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | k1_relat_1(X0) = X1 ),
% 3.17/1.00      inference(renaming,[status(thm)],[c_516]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_556,plain,
% 3.17/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.17/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.17/1.00      | ~ v1_funct_1(X0)
% 3.17/1.00      | v1_xboole_0(X2)
% 3.17/1.00      | k1_relat_1(X0) = X1 ),
% 3.17/1.00      inference(resolution,[status(thm)],[c_18,c_517]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_560,plain,
% 3.17/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | ~ v1_funct_2(X0,X1,X2)
% 3.17/1.00      | ~ v1_funct_1(X0)
% 3.17/1.00      | v1_xboole_0(X2)
% 3.17/1.00      | k1_relat_1(X0) = X1 ),
% 3.17/1.00      inference(global_propositional_subsumption,
% 3.17/1.00                [status(thm)],
% 3.17/1.00                [c_556,c_21,c_18,c_15,c_14]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_561,plain,
% 3.17/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.17/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | ~ v1_funct_1(X0)
% 3.17/1.00      | v1_xboole_0(X2)
% 3.17/1.00      | k1_relat_1(X0) = X1 ),
% 3.17/1.00      inference(renaming,[status(thm)],[c_560]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1695,plain,
% 3.17/1.00      ( k1_relat_1(X0) = X1
% 3.17/1.00      | v1_funct_2(X0,X1,X2) != iProver_top
% 3.17/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.17/1.00      | v1_funct_1(X0) != iProver_top
% 3.17/1.00      | v1_xboole_0(X2) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_561]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_2614,plain,
% 3.17/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 3.17/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.17/1.00      | v1_funct_1(sK2) != iProver_top
% 3.17/1.00      | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_1738,c_1695]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_38,negated_conjecture,
% 3.17/1.00      ( ~ v2_struct_0(sK1) ),
% 3.17/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_41,plain,
% 3.17/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_42,plain,
% 3.17/1.00      ( l1_struct_0(sK1) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_36,negated_conjecture,
% 3.17/1.00      ( v1_funct_1(sK2) ),
% 3.17/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_43,plain,
% 3.17/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_26,plain,
% 3.17/1.00      ( v2_struct_0(X0)
% 3.17/1.00      | ~ l1_struct_0(X0)
% 3.17/1.00      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 3.17/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_59,plain,
% 3.17/1.00      ( v2_struct_0(X0) = iProver_top
% 3.17/1.00      | l1_struct_0(X0) != iProver_top
% 3.17/1.00      | v1_xboole_0(k2_struct_0(X0)) != iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_61,plain,
% 3.17/1.00      ( v2_struct_0(sK1) = iProver_top
% 3.17/1.00      | l1_struct_0(sK1) != iProver_top
% 3.17/1.00      | v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
% 3.17/1.00      inference(instantiation,[status(thm)],[c_59]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_35,negated_conjecture,
% 3.17/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.17/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1699,plain,
% 3.17/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1732,plain,
% 3.17/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 3.17/1.00      inference(light_normalisation,[status(thm)],[c_1699,c_501,c_506]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_2974,plain,
% 3.17/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 3.17/1.00      inference(global_propositional_subsumption,
% 3.17/1.00                [status(thm)],
% 3.17/1.00                [c_2614,c_41,c_42,c_43,c_61,c_1732]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_2981,plain,
% 3.17/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) = iProver_top ),
% 3.17/1.00      inference(demodulation,[status(thm)],[c_2974,c_1738]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_17,plain,
% 3.17/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.17/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1704,plain,
% 3.17/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.17/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_4659,plain,
% 3.17/1.00      ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_2981,c_1704]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_33,negated_conjecture,
% 3.17/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.17/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1735,plain,
% 3.17/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.17/1.00      inference(light_normalisation,[status(thm)],[c_33,c_501,c_506]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_2983,plain,
% 3.17/1.00      ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.17/1.00      inference(demodulation,[status(thm)],[c_2974,c_1735]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_4823,plain,
% 3.17/1.00      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 3.17/1.00      inference(demodulation,[status(thm)],[c_4659,c_2983]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_22,plain,
% 3.17/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.17/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.17/1.00      | ~ v1_funct_1(X0)
% 3.17/1.00      | ~ v2_funct_1(X0)
% 3.17/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.17/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_32,negated_conjecture,
% 3.17/1.00      ( v2_funct_1(sK2) ),
% 3.17/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_660,plain,
% 3.17/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.17/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.17/1.00      | ~ v1_funct_1(X0)
% 3.17/1.00      | k2_relset_1(X1,X2,X0) != X2
% 3.17/1.00      | sK2 != X0 ),
% 3.17/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_32]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_661,plain,
% 3.17/1.00      ( ~ v1_funct_2(sK2,X0,X1)
% 3.17/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.17/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.17/1.00      | ~ v1_funct_1(sK2)
% 3.17/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.17/1.00      inference(unflattening,[status(thm)],[c_660]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_665,plain,
% 3.17/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.17/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.17/1.00      | ~ v1_funct_2(sK2,X0,X1)
% 3.17/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.17/1.00      inference(global_propositional_subsumption,
% 3.17/1.00                [status(thm)],
% 3.17/1.00                [c_661,c_36]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_666,plain,
% 3.17/1.00      ( ~ v1_funct_2(sK2,X0,X1)
% 3.17/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.17/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.17/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.17/1.00      inference(renaming,[status(thm)],[c_665]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1691,plain,
% 3.17/1.00      ( k2_relset_1(X0,X1,sK2) != X1
% 3.17/1.00      | v1_funct_2(sK2,X0,X1) != iProver_top
% 3.17/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 3.17/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_666]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_2606,plain,
% 3.17/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.17/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 3.17/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_1735,c_1691]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_2966,plain,
% 3.17/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
% 3.17/1.00      inference(global_propositional_subsumption,
% 3.17/1.00                [status(thm)],
% 3.17/1.00                [c_2606,c_1738,c_1732]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_2971,plain,
% 3.17/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_struct_0(sK1)
% 3.17/1.00      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 3.17/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.17/1.00      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_2966,c_1695]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_24,plain,
% 3.17/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.17/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | ~ v1_funct_1(X0)
% 3.17/1.00      | v1_funct_1(k2_funct_1(X0))
% 3.17/1.00      | ~ v2_funct_1(X0)
% 3.17/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.17/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_612,plain,
% 3.17/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.17/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | ~ v1_funct_1(X0)
% 3.17/1.00      | v1_funct_1(k2_funct_1(X0))
% 3.17/1.00      | k2_relset_1(X1,X2,X0) != X2
% 3.17/1.00      | sK2 != X0 ),
% 3.17/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_32]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_613,plain,
% 3.17/1.00      ( ~ v1_funct_2(sK2,X0,X1)
% 3.17/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.17/1.00      | v1_funct_1(k2_funct_1(sK2))
% 3.17/1.00      | ~ v1_funct_1(sK2)
% 3.17/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.17/1.00      inference(unflattening,[status(thm)],[c_612]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_617,plain,
% 3.17/1.00      ( v1_funct_1(k2_funct_1(sK2))
% 3.17/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.17/1.00      | ~ v1_funct_2(sK2,X0,X1)
% 3.17/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.17/1.00      inference(global_propositional_subsumption,
% 3.17/1.00                [status(thm)],
% 3.17/1.00                [c_613,c_36]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_618,plain,
% 3.17/1.00      ( ~ v1_funct_2(sK2,X0,X1)
% 3.17/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.17/1.00      | v1_funct_1(k2_funct_1(sK2))
% 3.17/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.17/1.00      inference(renaming,[status(thm)],[c_617]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1693,plain,
% 3.17/1.00      ( k2_relset_1(X0,X1,sK2) != X1
% 3.17/1.00      | v1_funct_2(sK2,X0,X1) != iProver_top
% 3.17/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.17/1.00      | v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_618]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_2167,plain,
% 3.17/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.17/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.17/1.00      | v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_1735,c_1693]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_23,plain,
% 3.17/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.17/1.00      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 3.17/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | ~ v1_funct_1(X0)
% 3.17/1.00      | ~ v2_funct_1(X0)
% 3.17/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.17/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_636,plain,
% 3.17/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.17/1.00      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 3.17/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | ~ v1_funct_1(X0)
% 3.17/1.00      | k2_relset_1(X1,X2,X0) != X2
% 3.17/1.00      | sK2 != X0 ),
% 3.17/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_32]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_637,plain,
% 3.17/1.00      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 3.17/1.00      | ~ v1_funct_2(sK2,X1,X0)
% 3.17/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.17/1.00      | ~ v1_funct_1(sK2)
% 3.17/1.00      | k2_relset_1(X1,X0,sK2) != X0 ),
% 3.17/1.00      inference(unflattening,[status(thm)],[c_636]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_641,plain,
% 3.17/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.17/1.00      | ~ v1_funct_2(sK2,X1,X0)
% 3.17/1.00      | v1_funct_2(k2_funct_1(sK2),X0,X1)
% 3.17/1.00      | k2_relset_1(X1,X0,sK2) != X0 ),
% 3.17/1.00      inference(global_propositional_subsumption,
% 3.17/1.00                [status(thm)],
% 3.17/1.00                [c_637,c_36]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_642,plain,
% 3.17/1.00      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 3.17/1.00      | ~ v1_funct_2(sK2,X1,X0)
% 3.17/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.17/1.00      | k2_relset_1(X1,X0,sK2) != X0 ),
% 3.17/1.00      inference(renaming,[status(thm)],[c_641]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1692,plain,
% 3.17/1.00      ( k2_relset_1(X0,X1,sK2) != X1
% 3.17/1.00      | v1_funct_2(k2_funct_1(sK2),X1,X0) = iProver_top
% 3.17/1.00      | v1_funct_2(sK2,X0,X1) != iProver_top
% 3.17/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_2287,plain,
% 3.17/1.00      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
% 3.17/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.17/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_1735,c_1692]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_3689,plain,
% 3.17/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_struct_0(sK1)
% 3.17/1.00      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
% 3.17/1.00      inference(global_propositional_subsumption,
% 3.17/1.00                [status(thm)],
% 3.17/1.00                [c_2971,c_1738,c_1732,c_2167,c_2287]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_3693,plain,
% 3.17/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_struct_0(sK1)
% 3.17/1.00      | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
% 3.17/1.00      inference(light_normalisation,[status(thm)],[c_3689,c_2974]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_4833,plain,
% 3.17/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.17/1.00      | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
% 3.17/1.00      inference(demodulation,[status(thm)],[c_4823,c_3693]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_0,plain,
% 3.17/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.17/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1717,plain,
% 3.17/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_4,plain,
% 3.17/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 3.17/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1714,plain,
% 3.17/1.00      ( X0 = X1
% 3.17/1.00      | v1_xboole_0(X0) != iProver_top
% 3.17/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_4513,plain,
% 3.17/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_1717,c_1714]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_7410,plain,
% 3.17/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.17/1.00      | k1_relat_1(sK2) = k1_xboole_0 ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_4833,c_4513]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_27,plain,
% 3.17/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.17/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | ~ v1_funct_1(X0)
% 3.17/1.00      | ~ v2_funct_1(X0)
% 3.17/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.17/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.17/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_588,plain,
% 3.17/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.17/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | ~ v1_funct_1(X0)
% 3.17/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.17/1.00      | k2_relset_1(X1,X2,X0) != X2
% 3.17/1.00      | sK2 != X0 ),
% 3.17/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_32]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_589,plain,
% 3.17/1.00      ( ~ v1_funct_2(sK2,X0,X1)
% 3.17/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.17/1.00      | ~ v1_funct_1(sK2)
% 3.17/1.00      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 3.17/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.17/1.00      inference(unflattening,[status(thm)],[c_588]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_593,plain,
% 3.17/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.17/1.00      | ~ v1_funct_2(sK2,X0,X1)
% 3.17/1.00      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 3.17/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.17/1.00      inference(global_propositional_subsumption,
% 3.17/1.00                [status(thm)],
% 3.17/1.00                [c_589,c_36]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_594,plain,
% 3.17/1.00      ( ~ v1_funct_2(sK2,X0,X1)
% 3.17/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.17/1.00      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 3.17/1.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.17/1.00      inference(renaming,[status(thm)],[c_593]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1694,plain,
% 3.17/1.00      ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 3.17/1.00      | k2_relset_1(X0,X1,sK2) != X1
% 3.17/1.00      | v1_funct_2(sK2,X0,X1) != iProver_top
% 3.17/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_594]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_2407,plain,
% 3.17/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 3.17/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.17/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_1735,c_1694]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_2470,plain,
% 3.17/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 3.17/1.00      inference(global_propositional_subsumption,
% 3.17/1.00                [status(thm)],
% 3.17/1.00                [c_2407,c_1738,c_1732]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_31,negated_conjecture,
% 3.17/1.00      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 3.17/1.00      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 3.17/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1809,plain,
% 3.17/1.00      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 3.17/1.00      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 3.17/1.00      inference(light_normalisation,[status(thm)],[c_31,c_501,c_506]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_2473,plain,
% 3.17/1.00      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 3.17/1.00      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
% 3.17/1.00      inference(demodulation,[status(thm)],[c_2470,c_1809]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_2978,plain,
% 3.17/1.00      ( k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2)
% 3.17/1.00      | k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
% 3.17/1.00      inference(demodulation,[status(thm)],[c_2974,c_2473]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_4834,plain,
% 3.17/1.00      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2)
% 3.17/1.00      | k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 3.17/1.00      inference(demodulation,[status(thm)],[c_4823,c_2978]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_2977,plain,
% 3.17/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) = iProver_top ),
% 3.17/1.00      inference(demodulation,[status(thm)],[c_2974,c_2966]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_4658,plain,
% 3.17/1.00      ( k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_2977,c_1704]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_6823,plain,
% 3.17/1.00      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 3.17/1.00      inference(light_normalisation,[status(thm)],[c_4658,c_4823]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_16,plain,
% 3.17/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.17/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1705,plain,
% 3.17/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.17/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_4675,plain,
% 3.17/1.00      ( k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_2977,c_1705]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_7139,plain,
% 3.17/1.00      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 3.17/1.00      inference(light_normalisation,[status(thm)],[c_4675,c_4823]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_7239,plain,
% 3.17/1.00      ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
% 3.17/1.00      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 3.17/1.00      inference(light_normalisation,[status(thm)],[c_4834,c_6823,c_7139]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_7436,plain,
% 3.17/1.00      ( k1_relat_1(sK2) = k1_xboole_0
% 3.17/1.00      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_7410,c_7239]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1706,plain,
% 3.17/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.17/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_3463,plain,
% 3.17/1.00      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_2977,c_1706]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_11,plain,
% 3.17/1.00      ( ~ v1_relat_1(X0)
% 3.17/1.00      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 3.17/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1708,plain,
% 3.17/1.00      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 3.17/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_3928,plain,
% 3.17/1.00      ( k9_relat_1(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2))) = k2_relat_1(k2_funct_1(sK2)) ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_3463,c_1708]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_7438,plain,
% 3.17/1.00      ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
% 3.17/1.00      | k1_relat_1(sK2) = k1_xboole_0 ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_7410,c_3928]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_13,plain,
% 3.17/1.00      ( ~ v1_funct_1(X0)
% 3.17/1.00      | ~ v2_funct_1(X0)
% 3.17/1.00      | ~ v1_relat_1(X0)
% 3.17/1.00      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
% 3.17/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_684,plain,
% 3.17/1.00      ( ~ v1_funct_1(X0)
% 3.17/1.00      | ~ v1_relat_1(X0)
% 3.17/1.00      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
% 3.17/1.00      | sK2 != X0 ),
% 3.17/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_32]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_685,plain,
% 3.17/1.00      ( ~ v1_funct_1(sK2)
% 3.17/1.00      | ~ v1_relat_1(sK2)
% 3.17/1.00      | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
% 3.17/1.00      inference(unflattening,[status(thm)],[c_684]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_689,plain,
% 3.17/1.00      ( ~ v1_relat_1(sK2)
% 3.17/1.00      | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
% 3.17/1.00      inference(global_propositional_subsumption,
% 3.17/1.00                [status(thm)],
% 3.17/1.00                [c_685,c_36]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1690,plain,
% 3.17/1.00      ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0)
% 3.17/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_689]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1967,plain,
% 3.17/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.17/1.00      | v1_relat_1(sK2) ),
% 3.17/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_2040,plain,
% 3.17/1.00      ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
% 3.17/1.00      inference(global_propositional_subsumption,
% 3.17/1.00                [status(thm)],
% 3.17/1.00                [c_1690,c_36,c_34,c_685,c_1967]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_3392,plain,
% 3.17/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_2981,c_1706]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_12,plain,
% 3.17/1.00      ( ~ v1_relat_1(X0)
% 3.17/1.00      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 3.17/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1707,plain,
% 3.17/1.00      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 3.17/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_3921,plain,
% 3.17/1.00      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_3392,c_1707]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_7441,plain,
% 3.17/1.00      ( k1_relat_1(sK2) = k1_xboole_0
% 3.17/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.17/1.00      inference(demodulation,[status(thm)],[c_7438,c_2040,c_3921]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_7449,plain,
% 3.17/1.00      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 3.17/1.00      inference(forward_subsumption_resolution,
% 3.17/1.00                [status(thm)],
% 3.17/1.00                [c_7436,c_7441]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_7,plain,
% 3.17/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.17/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1711,plain,
% 3.17/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.17/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_3261,plain,
% 3.17/1.00      ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))) = iProver_top ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_2981,c_1711]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_4832,plain,
% 3.17/1.00      ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) = iProver_top ),
% 3.17/1.00      inference(demodulation,[status(thm)],[c_4823,c_3261]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_7553,plain,
% 3.17/1.00      ( r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2))) = iProver_top ),
% 3.17/1.00      inference(demodulation,[status(thm)],[c_7449,c_4832]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_5,plain,
% 3.17/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 3.17/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1713,plain,
% 3.17/1.00      ( v1_xboole_0(X0) != iProver_top
% 3.17/1.00      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_5668,plain,
% 3.17/1.00      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 3.17/1.00      | v1_xboole_0(X0) != iProver_top ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_1713,c_4513]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_7830,plain,
% 3.17/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_1717,c_5668]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_9164,plain,
% 3.17/1.00      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.17/1.00      inference(demodulation,[status(thm)],[c_7553,c_7830]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_3,plain,
% 3.17/1.00      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.17/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1715,plain,
% 3.17/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_9168,plain,
% 3.17/1.00      ( sK2 = k1_xboole_0 ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_9164,c_1715]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_487,plain,
% 3.17/1.00      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 3.17/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_38]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_488,plain,
% 3.17/1.00      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 3.17/1.00      inference(unflattening,[status(thm)],[c_487]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_60,plain,
% 3.17/1.00      ( v2_struct_0(sK1)
% 3.17/1.00      | ~ l1_struct_0(sK1)
% 3.17/1.00      | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 3.17/1.00      inference(instantiation,[status(thm)],[c_26]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_490,plain,
% 3.17/1.00      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 3.17/1.00      inference(global_propositional_subsumption,
% 3.17/1.00                [status(thm)],
% 3.17/1.00                [c_488,c_38,c_37,c_60]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1696,plain,
% 3.17/1.00      ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_490]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_4840,plain,
% 3.17/1.00      ( v1_xboole_0(k2_relat_1(sK2)) != iProver_top ),
% 3.17/1.00      inference(demodulation,[status(thm)],[c_4823,c_1696]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_9268,plain,
% 3.17/1.00      ( v1_xboole_0(k2_relat_1(k1_xboole_0)) != iProver_top ),
% 3.17/1.00      inference(demodulation,[status(thm)],[c_9168,c_4840]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_9,plain,
% 3.17/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_relat_1(X0)) ),
% 3.17/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_1710,plain,
% 3.17/1.00      ( v1_xboole_0(X0) != iProver_top
% 3.17/1.00      | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_5669,plain,
% 3.17/1.00      ( k2_relat_1(X0) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_1710,c_4513]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_6942,plain,
% 3.17/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.17/1.00      inference(superposition,[status(thm)],[c_1717,c_5669]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_9327,plain,
% 3.17/1.00      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.17/1.00      inference(light_normalisation,[status(thm)],[c_9268,c_6942]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(c_131,plain,
% 3.17/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.17/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.17/1.00  
% 3.17/1.00  cnf(contradiction,plain,
% 3.17/1.00      ( $false ),
% 3.17/1.00      inference(minisat,[status(thm)],[c_9327,c_131]) ).
% 3.17/1.00  
% 3.17/1.00  
% 3.17/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.17/1.00  
% 3.17/1.00  ------                               Statistics
% 3.17/1.00  
% 3.17/1.00  ------ General
% 3.17/1.00  
% 3.17/1.00  abstr_ref_over_cycles:                  0
% 3.17/1.00  abstr_ref_under_cycles:                 0
% 3.17/1.00  gc_basic_clause_elim:                   0
% 3.17/1.00  forced_gc_time:                         0
% 3.17/1.00  parsing_time:                           0.016
% 3.17/1.00  unif_index_cands_time:                  0.
% 3.17/1.00  unif_index_add_time:                    0.
% 3.17/1.00  orderings_time:                         0.
% 3.17/1.00  out_proof_time:                         0.015
% 3.17/1.00  total_time:                             0.261
% 3.17/1.00  num_of_symbols:                         59
% 3.17/1.00  num_of_terms:                           7696
% 3.17/1.00  
% 3.17/1.00  ------ Preprocessing
% 3.17/1.00  
% 3.17/1.00  num_of_splits:                          0
% 3.17/1.00  num_of_split_atoms:                     0
% 3.17/1.00  num_of_reused_defs:                     0
% 3.17/1.00  num_eq_ax_congr_red:                    16
% 3.17/1.00  num_of_sem_filtered_clauses:            1
% 3.17/1.00  num_of_subtypes:                        0
% 3.17/1.00  monotx_restored_types:                  0
% 3.17/1.00  sat_num_of_epr_types:                   0
% 3.17/1.00  sat_num_of_non_cyclic_types:            0
% 3.17/1.00  sat_guarded_non_collapsed_types:        0
% 3.17/1.00  num_pure_diseq_elim:                    0
% 3.17/1.00  simp_replaced_by:                       0
% 3.17/1.00  res_preprocessed:                       177
% 3.17/1.00  prep_upred:                             0
% 3.17/1.00  prep_unflattend:                        12
% 3.17/1.00  smt_new_axioms:                         0
% 3.17/1.00  pred_elim_cands:                        6
% 3.17/1.00  pred_elim:                              5
% 3.17/1.00  pred_elim_cl:                           6
% 3.17/1.00  pred_elim_cycles:                       7
% 3.17/1.00  merged_defs:                            8
% 3.17/1.00  merged_defs_ncl:                        0
% 3.17/1.00  bin_hyper_res:                          9
% 3.17/1.00  prep_cycles:                            4
% 3.17/1.00  pred_elim_time:                         0.006
% 3.17/1.00  splitting_time:                         0.
% 3.17/1.00  sem_filter_time:                        0.
% 3.17/1.00  monotx_time:                            0.
% 3.17/1.00  subtype_inf_time:                       0.
% 3.17/1.00  
% 3.17/1.00  ------ Problem properties
% 3.17/1.00  
% 3.17/1.00  clauses:                                33
% 3.17/1.00  conjectures:                            5
% 3.17/1.00  epr:                                    5
% 3.17/1.00  horn:                                   32
% 3.17/1.00  ground:                                 9
% 3.17/1.00  unary:                                  10
% 3.17/1.00  binary:                                 13
% 3.17/1.00  lits:                                   75
% 3.17/1.00  lits_eq:                                19
% 3.17/1.00  fd_pure:                                0
% 3.17/1.00  fd_pseudo:                              0
% 3.17/1.00  fd_cond:                                1
% 3.17/1.00  fd_pseudo_cond:                         2
% 3.17/1.00  ac_symbols:                             0
% 3.17/1.00  
% 3.17/1.00  ------ Propositional Solver
% 3.17/1.00  
% 3.17/1.00  prop_solver_calls:                      28
% 3.17/1.00  prop_fast_solver_calls:                 1134
% 3.17/1.00  smt_solver_calls:                       0
% 3.17/1.00  smt_fast_solver_calls:                  0
% 3.17/1.00  prop_num_of_clauses:                    4388
% 3.17/1.00  prop_preprocess_simplified:             10877
% 3.17/1.00  prop_fo_subsumed:                       26
% 3.17/1.00  prop_solver_time:                       0.
% 3.17/1.00  smt_solver_time:                        0.
% 3.17/1.00  smt_fast_solver_time:                   0.
% 3.17/1.00  prop_fast_solver_time:                  0.
% 3.17/1.00  prop_unsat_core_time:                   0.
% 3.17/1.00  
% 3.17/1.00  ------ QBF
% 3.17/1.00  
% 3.17/1.00  qbf_q_res:                              0
% 3.17/1.00  qbf_num_tautologies:                    0
% 3.17/1.00  qbf_prep_cycles:                        0
% 3.17/1.00  
% 3.17/1.00  ------ BMC1
% 3.17/1.00  
% 3.17/1.00  bmc1_current_bound:                     -1
% 3.17/1.00  bmc1_last_solved_bound:                 -1
% 3.17/1.00  bmc1_unsat_core_size:                   -1
% 3.17/1.00  bmc1_unsat_core_parents_size:           -1
% 3.17/1.00  bmc1_merge_next_fun:                    0
% 3.17/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.17/1.00  
% 3.17/1.00  ------ Instantiation
% 3.17/1.00  
% 3.17/1.00  inst_num_of_clauses:                    1382
% 3.17/1.00  inst_num_in_passive:                    418
% 3.17/1.00  inst_num_in_active:                     479
% 3.17/1.00  inst_num_in_unprocessed:                485
% 3.17/1.00  inst_num_of_loops:                      500
% 3.17/1.00  inst_num_of_learning_restarts:          0
% 3.17/1.00  inst_num_moves_active_passive:          19
% 3.17/1.00  inst_lit_activity:                      0
% 3.17/1.00  inst_lit_activity_moves:                0
% 3.17/1.00  inst_num_tautologies:                   0
% 3.17/1.00  inst_num_prop_implied:                  0
% 3.17/1.00  inst_num_existing_simplified:           0
% 3.17/1.00  inst_num_eq_res_simplified:             0
% 3.17/1.00  inst_num_child_elim:                    0
% 3.17/1.00  inst_num_of_dismatching_blockings:      100
% 3.17/1.00  inst_num_of_non_proper_insts:           1125
% 3.17/1.00  inst_num_of_duplicates:                 0
% 3.17/1.00  inst_inst_num_from_inst_to_res:         0
% 3.17/1.00  inst_dismatching_checking_time:         0.
% 3.17/1.00  
% 3.17/1.00  ------ Resolution
% 3.17/1.00  
% 3.17/1.00  res_num_of_clauses:                     0
% 3.17/1.00  res_num_in_passive:                     0
% 3.17/1.00  res_num_in_active:                      0
% 3.17/1.00  res_num_of_loops:                       181
% 3.17/1.00  res_forward_subset_subsumed:            69
% 3.17/1.00  res_backward_subset_subsumed:           2
% 3.17/1.00  res_forward_subsumed:                   0
% 3.17/1.00  res_backward_subsumed:                  0
% 3.17/1.00  res_forward_subsumption_resolution:     1
% 3.17/1.00  res_backward_subsumption_resolution:    0
% 3.17/1.00  res_clause_to_clause_subsumption:       236
% 3.17/1.00  res_orphan_elimination:                 0
% 3.17/1.00  res_tautology_del:                      112
% 3.17/1.00  res_num_eq_res_simplified:              0
% 3.17/1.00  res_num_sel_changes:                    0
% 3.17/1.00  res_moves_from_active_to_pass:          0
% 3.17/1.00  
% 3.17/1.00  ------ Superposition
% 3.17/1.00  
% 3.17/1.00  sup_time_total:                         0.
% 3.17/1.00  sup_time_generating:                    0.
% 3.17/1.00  sup_time_sim_full:                      0.
% 3.17/1.00  sup_time_sim_immed:                     0.
% 3.17/1.00  
% 3.17/1.00  sup_num_of_clauses:                     80
% 3.17/1.00  sup_num_in_active:                      32
% 3.17/1.00  sup_num_in_passive:                     48
% 3.17/1.00  sup_num_of_loops:                       98
% 3.17/1.00  sup_fw_superposition:                   38
% 3.17/1.00  sup_bw_superposition:                   71
% 3.17/1.00  sup_immediate_simplified:               36
% 3.17/1.00  sup_given_eliminated:                   2
% 3.17/1.00  comparisons_done:                       0
% 3.17/1.00  comparisons_avoided:                    3
% 3.17/1.00  
% 3.17/1.00  ------ Simplifications
% 3.17/1.00  
% 3.17/1.00  
% 3.17/1.00  sim_fw_subset_subsumed:                 23
% 3.17/1.00  sim_bw_subset_subsumed:                 1
% 3.17/1.00  sim_fw_subsumed:                        2
% 3.17/1.00  sim_bw_subsumed:                        2
% 3.17/1.00  sim_fw_subsumption_res:                 1
% 3.17/1.00  sim_bw_subsumption_res:                 0
% 3.17/1.00  sim_tautology_del:                      1
% 3.17/1.00  sim_eq_tautology_del:                   4
% 3.17/1.00  sim_eq_res_simp:                        0
% 3.17/1.00  sim_fw_demodulated:                     2
% 3.17/1.00  sim_bw_demodulated:                     65
% 3.17/1.00  sim_light_normalised:                   26
% 3.17/1.00  sim_joinable_taut:                      0
% 3.17/1.00  sim_joinable_simp:                      0
% 3.17/1.00  sim_ac_normalised:                      0
% 3.17/1.00  sim_smt_subsumption:                    0
% 3.17/1.00  
%------------------------------------------------------------------------------
