%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:12 EST 2020

% Result     : Theorem 7.15s
% Output     : CNFRefutation 7.15s
% Verified   : 
% Statistics : Number of formulae       :  275 (56527 expanded)
%              Number of clauses        :  185 (15862 expanded)
%              Number of leaves         :   24 (16809 expanded)
%              Depth                    :   30
%              Number of atoms          :  803 (411751 expanded)
%              Number of equality atoms :  380 (137769 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
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

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

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
    inference(ennf_transformation,[],[f24])).

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f62,plain,(
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

fof(f61,plain,(
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

fof(f60,plain,
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

fof(f63,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f54,f62,f61,f60])).

fof(f99,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f63])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f91,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f96,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f94,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f100,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

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

fof(f90,plain,(
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
    inference(cnf_transformation,[],[f63])).

fof(f97,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f98,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f63])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

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

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f18,axiom,(
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
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f95,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f21,axiom,(
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
    inference(ennf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f55])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f104,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f64,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f22,axiom,(
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
    inference(ennf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f51])).

fof(f93,plain,(
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
    inference(cnf_transformation,[],[f63])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f57])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f106,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f105,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f70])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1455,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_27,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_36,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_396,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_36])).

cnf(c_397,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_38,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_401,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_38])).

cnf(c_402,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_1494,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1455,c_397,c_402])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1457,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2921,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1494,c_1457])).

cnf(c_32,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1487,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_32,c_397,c_402])).

cnf(c_3046,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2921,c_1487])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_31,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_590,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

cnf(c_591,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_590])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_595,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_591,c_35])).

cnf(c_596,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_595])).

cnf(c_1446,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_596])).

cnf(c_2227,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1487,c_1446])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1454,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1484,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1454,c_397,c_402])).

cnf(c_2472,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2227,c_1494,c_1484])).

cnf(c_3055,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3046,c_2472])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_502,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_13,c_10])).

cnf(c_1451,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_502])).

cnf(c_3899,plain,
    ( k7_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3055,c_1451])).

cnf(c_43,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_44,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_53,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1676,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_596])).

cnf(c_1677,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1676])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1916,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1917,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1916])).

cnf(c_975,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1766,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_975])).

cnf(c_1999,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1766])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1685,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2258,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1685])).

cnf(c_2274,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2258])).

cnf(c_5432,plain,
    ( k7_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3899,c_36,c_43,c_44,c_32,c_53,c_1677,c_1917,c_1999,c_2274])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_23,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_464,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_20,c_23])).

cnf(c_468,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_464,c_13])).

cnf(c_1450,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_468])).

cnf(c_2695,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1494,c_1450])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_40,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_41,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_42,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_28,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_49,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(k2_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_51,plain,
    ( v2_struct_0(sK1) = iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_1776,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1685])).

cnf(c_1777,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1776])).

cnf(c_1908,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1909,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1908])).

cnf(c_3969,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2695,c_40,c_41,c_42,c_44,c_51,c_1484,c_1777,c_1909])).

cnf(c_3973,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3969,c_3055])).

cnf(c_1464,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5212,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3973,c_1464])).

cnf(c_6631,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5212,c_36,c_43,c_44,c_32,c_53,c_1677,c_1917,c_1999,c_2274])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1462,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6636,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0)) = k9_relat_1(k2_funct_1(sK2),X0) ),
    inference(superposition,[status(thm)],[c_6631,c_1462])).

cnf(c_7804,plain,
    ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_5432,c_6636])).

cnf(c_3059,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3046,c_1494])).

cnf(c_3784,plain,
    ( k7_relat_1(sK2,k2_struct_0(sK0)) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3059,c_1451])).

cnf(c_5345,plain,
    ( k7_relat_1(sK2,k2_struct_0(sK0)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3784,c_44,c_1777,c_1909])).

cnf(c_5347,plain,
    ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_5345,c_3969])).

cnf(c_3976,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3969,c_3059])).

cnf(c_4648,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3976,c_1464])).

cnf(c_5982,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4648,c_44,c_1777,c_1909])).

cnf(c_5987,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_5982,c_1462])).

cnf(c_7602,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_5347,c_5987])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1465,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_628,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_31])).

cnf(c_629,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_628])).

cnf(c_633,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_629,c_35])).

cnf(c_1444,plain,
    ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_1866,plain,
    ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2))) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1465,c_1444])).

cnf(c_1867,plain,
    ( ~ v1_relat_1(sK2)
    | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2))) = k1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1866])).

cnf(c_2551,plain,
    ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2))) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1866,c_33,c_1776,c_1867,c_1908])).

cnf(c_7709,plain,
    ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_7602,c_2551])).

cnf(c_7805,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_7804,c_7709])).

cnf(c_2696,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_struct_0(sK1)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2472,c_1450])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_542,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_31])).

cnf(c_543,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_547,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_543,c_35])).

cnf(c_548,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK2))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_547])).

cnf(c_1448,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_548])).

cnf(c_1952,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1487,c_1448])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_566,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_31])).

cnf(c_567,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(unflattening,[status(thm)],[c_566])).

cnf(c_571,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X1,X0)
    | v1_funct_2(k2_funct_1(sK2),X0,X1)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_567,c_35])).

cnf(c_572,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(renaming,[status(thm)],[c_571])).

cnf(c_1447,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(k2_funct_1(sK2),X1,X0) = iProver_top
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_572])).

cnf(c_2042,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1487,c_1447])).

cnf(c_4485,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_struct_0(sK1)
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2696,c_36,c_43,c_44,c_32,c_53,c_1494,c_1484,c_1677,c_1917,c_1952,c_1999,c_2042,c_2274])).

cnf(c_4489,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4485,c_3046,c_3969])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1467,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4493,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4489,c_1467])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_518,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_31])).

cnf(c_519,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_518])).

cnf(c_523,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_519,c_35])).

cnf(c_524,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_523])).

cnf(c_1449,plain,
    ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_524])).

cnf(c_2158,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1487,c_1449])).

cnf(c_2161,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2158,c_1494,c_1484])).

cnf(c_30,negated_conjecture,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1569,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_30,c_397,c_402])).

cnf(c_2164,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2161,c_1569])).

cnf(c_3056,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_3046,c_2164])).

cnf(c_2922,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2472,c_1457])).

cnf(c_3804,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(light_normalisation,[status(thm)],[c_2922,c_3046])).

cnf(c_3965,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_3056,c_3804])).

cnf(c_3972,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3969,c_3965])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1458,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3896,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3055,c_1458])).

cnf(c_5099,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(light_normalisation,[status(thm)],[c_3896,c_3969])).

cnf(c_5435,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3972,c_5099])).

cnf(c_5521,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_4493,c_5435])).

cnf(c_7808,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7805,c_5521])).

cnf(c_7816,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7808])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1461,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5216,plain,
    ( v1_xboole_0(k1_relat_1(sK2)) != iProver_top
    | v1_xboole_0(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3973,c_1461])).

cnf(c_5915,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_xboole_0(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4489,c_5216])).

cnf(c_5920,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | k2_funct_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5915,c_1467])).

cnf(c_6953,plain,
    ( k2_funct_1(sK2) = k1_xboole_0
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_5920,c_5435])).

cnf(c_8203,plain,
    ( k2_funct_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6953,c_7805])).

cnf(c_8208,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_8203,c_7805])).

cnf(c_12682,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7816,c_8208])).

cnf(c_9719,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k1_xboole_0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8208,c_3976])).

cnf(c_12697,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12682,c_9719])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_12723,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12697,c_5])).

cnf(c_2924,plain,
    ( k2_relset_1(k1_xboole_0,X0,X1) = k2_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1457])).

cnf(c_13160,plain,
    ( k2_relset_1(k1_xboole_0,X0,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_12723,c_2924])).

cnf(c_8218,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(sK2)
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8203,c_5915])).

cnf(c_3975,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(demodulation,[status(thm)],[c_3969,c_3804])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1460,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5342,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(k1_relat_1(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3975,c_1460])).

cnf(c_6767,plain,
    ( m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(k1_relat_1(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5342,c_3973])).

cnf(c_7807,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7805,c_6767])).

cnf(c_7822,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7807,c_7816])).

cnf(c_7810,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_7805,c_3975])).

cnf(c_7818,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_xboole_0,k2_funct_1(sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7816,c_7810])).

cnf(c_4946,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1461])).

cnf(c_4976,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(k2_relset_1(X1,k1_xboole_0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1460,c_4946])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_4994,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(k2_relset_1(X2,k1_xboole_0,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4976,c_4])).

cnf(c_6280,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(k2_relset_1(X1,k1_xboole_0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4489,c_4994])).

cnf(c_7865,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7818,c_6280])).

cnf(c_7874,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7865,c_5435,c_7805])).

cnf(c_8206,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8203,c_7874])).

cnf(c_9245,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8218,c_7822,c_8206])).

cnf(c_9251,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(k2_relset_1(X1,k1_xboole_0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9245,c_4994])).

cnf(c_18133,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(k2_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_13160,c_9251])).

cnf(c_383,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_37])).

cnf(c_384,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_50,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_386,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_384,c_37,c_36,c_50])).

cnf(c_1452,plain,
    ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_386])).

cnf(c_3061,plain,
    ( v1_xboole_0(k2_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3046,c_1452])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18133,c_12723,c_3061])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.15/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.15/1.50  
% 7.15/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.15/1.50  
% 7.15/1.50  ------  iProver source info
% 7.15/1.50  
% 7.15/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.15/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.15/1.50  git: non_committed_changes: false
% 7.15/1.50  git: last_make_outside_of_git: false
% 7.15/1.50  
% 7.15/1.50  ------ 
% 7.15/1.50  
% 7.15/1.50  ------ Input Options
% 7.15/1.50  
% 7.15/1.50  --out_options                           all
% 7.15/1.50  --tptp_safe_out                         true
% 7.15/1.50  --problem_path                          ""
% 7.15/1.50  --include_path                          ""
% 7.15/1.50  --clausifier                            res/vclausify_rel
% 7.15/1.50  --clausifier_options                    --mode clausify
% 7.15/1.50  --stdin                                 false
% 7.15/1.50  --stats_out                             all
% 7.15/1.50  
% 7.15/1.50  ------ General Options
% 7.15/1.50  
% 7.15/1.50  --fof                                   false
% 7.15/1.50  --time_out_real                         305.
% 7.15/1.50  --time_out_virtual                      -1.
% 7.15/1.50  --symbol_type_check                     false
% 7.15/1.50  --clausify_out                          false
% 7.15/1.50  --sig_cnt_out                           false
% 7.15/1.50  --trig_cnt_out                          false
% 7.15/1.50  --trig_cnt_out_tolerance                1.
% 7.15/1.50  --trig_cnt_out_sk_spl                   false
% 7.15/1.50  --abstr_cl_out                          false
% 7.15/1.50  
% 7.15/1.50  ------ Global Options
% 7.15/1.50  
% 7.15/1.50  --schedule                              default
% 7.15/1.50  --add_important_lit                     false
% 7.15/1.50  --prop_solver_per_cl                    1000
% 7.15/1.50  --min_unsat_core                        false
% 7.15/1.50  --soft_assumptions                      false
% 7.15/1.50  --soft_lemma_size                       3
% 7.15/1.50  --prop_impl_unit_size                   0
% 7.15/1.50  --prop_impl_unit                        []
% 7.15/1.50  --share_sel_clauses                     true
% 7.15/1.50  --reset_solvers                         false
% 7.15/1.50  --bc_imp_inh                            [conj_cone]
% 7.15/1.50  --conj_cone_tolerance                   3.
% 7.15/1.50  --extra_neg_conj                        none
% 7.15/1.50  --large_theory_mode                     true
% 7.15/1.50  --prolific_symb_bound                   200
% 7.15/1.50  --lt_threshold                          2000
% 7.15/1.50  --clause_weak_htbl                      true
% 7.15/1.50  --gc_record_bc_elim                     false
% 7.15/1.50  
% 7.15/1.50  ------ Preprocessing Options
% 7.15/1.50  
% 7.15/1.50  --preprocessing_flag                    true
% 7.15/1.50  --time_out_prep_mult                    0.1
% 7.15/1.50  --splitting_mode                        input
% 7.15/1.50  --splitting_grd                         true
% 7.15/1.50  --splitting_cvd                         false
% 7.15/1.50  --splitting_cvd_svl                     false
% 7.15/1.50  --splitting_nvd                         32
% 7.15/1.50  --sub_typing                            true
% 7.15/1.50  --prep_gs_sim                           true
% 7.15/1.50  --prep_unflatten                        true
% 7.15/1.50  --prep_res_sim                          true
% 7.15/1.50  --prep_upred                            true
% 7.15/1.50  --prep_sem_filter                       exhaustive
% 7.15/1.50  --prep_sem_filter_out                   false
% 7.15/1.50  --pred_elim                             true
% 7.15/1.50  --res_sim_input                         true
% 7.15/1.50  --eq_ax_congr_red                       true
% 7.15/1.50  --pure_diseq_elim                       true
% 7.15/1.50  --brand_transform                       false
% 7.15/1.50  --non_eq_to_eq                          false
% 7.15/1.50  --prep_def_merge                        true
% 7.15/1.50  --prep_def_merge_prop_impl              false
% 7.15/1.50  --prep_def_merge_mbd                    true
% 7.15/1.50  --prep_def_merge_tr_red                 false
% 7.15/1.50  --prep_def_merge_tr_cl                  false
% 7.15/1.50  --smt_preprocessing                     true
% 7.15/1.50  --smt_ac_axioms                         fast
% 7.15/1.50  --preprocessed_out                      false
% 7.15/1.50  --preprocessed_stats                    false
% 7.15/1.50  
% 7.15/1.50  ------ Abstraction refinement Options
% 7.15/1.50  
% 7.15/1.50  --abstr_ref                             []
% 7.15/1.50  --abstr_ref_prep                        false
% 7.15/1.50  --abstr_ref_until_sat                   false
% 7.15/1.50  --abstr_ref_sig_restrict                funpre
% 7.15/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.15/1.50  --abstr_ref_under                       []
% 7.15/1.50  
% 7.15/1.50  ------ SAT Options
% 7.15/1.50  
% 7.15/1.50  --sat_mode                              false
% 7.15/1.50  --sat_fm_restart_options                ""
% 7.15/1.50  --sat_gr_def                            false
% 7.15/1.50  --sat_epr_types                         true
% 7.15/1.50  --sat_non_cyclic_types                  false
% 7.15/1.50  --sat_finite_models                     false
% 7.15/1.50  --sat_fm_lemmas                         false
% 7.15/1.50  --sat_fm_prep                           false
% 7.15/1.50  --sat_fm_uc_incr                        true
% 7.15/1.50  --sat_out_model                         small
% 7.15/1.50  --sat_out_clauses                       false
% 7.15/1.50  
% 7.15/1.50  ------ QBF Options
% 7.15/1.50  
% 7.15/1.50  --qbf_mode                              false
% 7.15/1.50  --qbf_elim_univ                         false
% 7.15/1.50  --qbf_dom_inst                          none
% 7.15/1.50  --qbf_dom_pre_inst                      false
% 7.15/1.50  --qbf_sk_in                             false
% 7.15/1.50  --qbf_pred_elim                         true
% 7.15/1.50  --qbf_split                             512
% 7.15/1.50  
% 7.15/1.50  ------ BMC1 Options
% 7.15/1.50  
% 7.15/1.50  --bmc1_incremental                      false
% 7.15/1.50  --bmc1_axioms                           reachable_all
% 7.15/1.50  --bmc1_min_bound                        0
% 7.15/1.50  --bmc1_max_bound                        -1
% 7.15/1.50  --bmc1_max_bound_default                -1
% 7.15/1.50  --bmc1_symbol_reachability              true
% 7.15/1.50  --bmc1_property_lemmas                  false
% 7.15/1.50  --bmc1_k_induction                      false
% 7.15/1.50  --bmc1_non_equiv_states                 false
% 7.15/1.50  --bmc1_deadlock                         false
% 7.15/1.50  --bmc1_ucm                              false
% 7.15/1.50  --bmc1_add_unsat_core                   none
% 7.15/1.50  --bmc1_unsat_core_children              false
% 7.15/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.15/1.50  --bmc1_out_stat                         full
% 7.15/1.50  --bmc1_ground_init                      false
% 7.15/1.50  --bmc1_pre_inst_next_state              false
% 7.15/1.50  --bmc1_pre_inst_state                   false
% 7.15/1.50  --bmc1_pre_inst_reach_state             false
% 7.15/1.50  --bmc1_out_unsat_core                   false
% 7.15/1.50  --bmc1_aig_witness_out                  false
% 7.15/1.50  --bmc1_verbose                          false
% 7.15/1.50  --bmc1_dump_clauses_tptp                false
% 7.15/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.15/1.50  --bmc1_dump_file                        -
% 7.15/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.15/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.15/1.50  --bmc1_ucm_extend_mode                  1
% 7.15/1.50  --bmc1_ucm_init_mode                    2
% 7.15/1.50  --bmc1_ucm_cone_mode                    none
% 7.15/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.15/1.50  --bmc1_ucm_relax_model                  4
% 7.15/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.15/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.15/1.50  --bmc1_ucm_layered_model                none
% 7.15/1.50  --bmc1_ucm_max_lemma_size               10
% 7.15/1.50  
% 7.15/1.50  ------ AIG Options
% 7.15/1.50  
% 7.15/1.50  --aig_mode                              false
% 7.15/1.50  
% 7.15/1.50  ------ Instantiation Options
% 7.15/1.50  
% 7.15/1.50  --instantiation_flag                    true
% 7.15/1.50  --inst_sos_flag                         false
% 7.15/1.50  --inst_sos_phase                        true
% 7.15/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.15/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.15/1.50  --inst_lit_sel_side                     num_symb
% 7.15/1.50  --inst_solver_per_active                1400
% 7.15/1.50  --inst_solver_calls_frac                1.
% 7.15/1.50  --inst_passive_queue_type               priority_queues
% 7.15/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.15/1.50  --inst_passive_queues_freq              [25;2]
% 7.15/1.50  --inst_dismatching                      true
% 7.15/1.50  --inst_eager_unprocessed_to_passive     true
% 7.15/1.50  --inst_prop_sim_given                   true
% 7.15/1.50  --inst_prop_sim_new                     false
% 7.15/1.50  --inst_subs_new                         false
% 7.15/1.50  --inst_eq_res_simp                      false
% 7.15/1.50  --inst_subs_given                       false
% 7.15/1.50  --inst_orphan_elimination               true
% 7.15/1.50  --inst_learning_loop_flag               true
% 7.15/1.50  --inst_learning_start                   3000
% 7.15/1.50  --inst_learning_factor                  2
% 7.15/1.50  --inst_start_prop_sim_after_learn       3
% 7.15/1.50  --inst_sel_renew                        solver
% 7.15/1.50  --inst_lit_activity_flag                true
% 7.15/1.50  --inst_restr_to_given                   false
% 7.15/1.50  --inst_activity_threshold               500
% 7.15/1.50  --inst_out_proof                        true
% 7.15/1.50  
% 7.15/1.50  ------ Resolution Options
% 7.15/1.50  
% 7.15/1.50  --resolution_flag                       true
% 7.15/1.50  --res_lit_sel                           adaptive
% 7.15/1.50  --res_lit_sel_side                      none
% 7.15/1.50  --res_ordering                          kbo
% 7.15/1.50  --res_to_prop_solver                    active
% 7.15/1.50  --res_prop_simpl_new                    false
% 7.15/1.50  --res_prop_simpl_given                  true
% 7.15/1.50  --res_passive_queue_type                priority_queues
% 7.15/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.15/1.50  --res_passive_queues_freq               [15;5]
% 7.15/1.50  --res_forward_subs                      full
% 7.15/1.50  --res_backward_subs                     full
% 7.15/1.50  --res_forward_subs_resolution           true
% 7.15/1.50  --res_backward_subs_resolution          true
% 7.15/1.50  --res_orphan_elimination                true
% 7.15/1.50  --res_time_limit                        2.
% 7.15/1.50  --res_out_proof                         true
% 7.15/1.50  
% 7.15/1.50  ------ Superposition Options
% 7.15/1.50  
% 7.15/1.50  --superposition_flag                    true
% 7.15/1.50  --sup_passive_queue_type                priority_queues
% 7.15/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.15/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.15/1.50  --demod_completeness_check              fast
% 7.15/1.50  --demod_use_ground                      true
% 7.15/1.50  --sup_to_prop_solver                    passive
% 7.15/1.50  --sup_prop_simpl_new                    true
% 7.15/1.50  --sup_prop_simpl_given                  true
% 7.15/1.50  --sup_fun_splitting                     false
% 7.15/1.50  --sup_smt_interval                      50000
% 7.15/1.50  
% 7.15/1.50  ------ Superposition Simplification Setup
% 7.15/1.50  
% 7.15/1.50  --sup_indices_passive                   []
% 7.15/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.15/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.15/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.15/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.15/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.15/1.50  --sup_full_bw                           [BwDemod]
% 7.15/1.50  --sup_immed_triv                        [TrivRules]
% 7.15/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.15/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.15/1.50  --sup_immed_bw_main                     []
% 7.15/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.15/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.15/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.15/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.15/1.50  
% 7.15/1.50  ------ Combination Options
% 7.15/1.50  
% 7.15/1.50  --comb_res_mult                         3
% 7.15/1.50  --comb_sup_mult                         2
% 7.15/1.50  --comb_inst_mult                        10
% 7.15/1.50  
% 7.15/1.50  ------ Debug Options
% 7.15/1.50  
% 7.15/1.50  --dbg_backtrace                         false
% 7.15/1.50  --dbg_dump_prop_clauses                 false
% 7.15/1.50  --dbg_dump_prop_clauses_file            -
% 7.15/1.50  --dbg_out_stat                          false
% 7.15/1.50  ------ Parsing...
% 7.15/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.15/1.50  
% 7.15/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 7.15/1.50  
% 7.15/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.15/1.50  
% 7.15/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.15/1.50  ------ Proving...
% 7.15/1.50  ------ Problem Properties 
% 7.15/1.50  
% 7.15/1.50  
% 7.15/1.50  clauses                                 31
% 7.15/1.50  conjectures                             5
% 7.15/1.50  EPR                                     4
% 7.15/1.50  Horn                                    29
% 7.15/1.50  unary                                   11
% 7.15/1.50  binary                                  9
% 7.15/1.50  lits                                    69
% 7.15/1.50  lits eq                                 25
% 7.15/1.50  fd_pure                                 0
% 7.15/1.50  fd_pseudo                               0
% 7.15/1.50  fd_cond                                 2
% 7.15/1.50  fd_pseudo_cond                          2
% 7.15/1.50  AC symbols                              0
% 7.15/1.50  
% 7.15/1.50  ------ Schedule dynamic 5 is on 
% 7.15/1.50  
% 7.15/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.15/1.50  
% 7.15/1.50  
% 7.15/1.50  ------ 
% 7.15/1.50  Current options:
% 7.15/1.50  ------ 
% 7.15/1.50  
% 7.15/1.50  ------ Input Options
% 7.15/1.50  
% 7.15/1.50  --out_options                           all
% 7.15/1.50  --tptp_safe_out                         true
% 7.15/1.50  --problem_path                          ""
% 7.15/1.50  --include_path                          ""
% 7.15/1.50  --clausifier                            res/vclausify_rel
% 7.15/1.50  --clausifier_options                    --mode clausify
% 7.15/1.50  --stdin                                 false
% 7.15/1.50  --stats_out                             all
% 7.15/1.50  
% 7.15/1.50  ------ General Options
% 7.15/1.50  
% 7.15/1.50  --fof                                   false
% 7.15/1.50  --time_out_real                         305.
% 7.15/1.50  --time_out_virtual                      -1.
% 7.15/1.50  --symbol_type_check                     false
% 7.15/1.50  --clausify_out                          false
% 7.15/1.50  --sig_cnt_out                           false
% 7.15/1.50  --trig_cnt_out                          false
% 7.15/1.50  --trig_cnt_out_tolerance                1.
% 7.15/1.50  --trig_cnt_out_sk_spl                   false
% 7.15/1.50  --abstr_cl_out                          false
% 7.15/1.50  
% 7.15/1.50  ------ Global Options
% 7.15/1.50  
% 7.15/1.50  --schedule                              default
% 7.15/1.50  --add_important_lit                     false
% 7.15/1.50  --prop_solver_per_cl                    1000
% 7.15/1.50  --min_unsat_core                        false
% 7.15/1.50  --soft_assumptions                      false
% 7.15/1.50  --soft_lemma_size                       3
% 7.15/1.50  --prop_impl_unit_size                   0
% 7.15/1.50  --prop_impl_unit                        []
% 7.15/1.50  --share_sel_clauses                     true
% 7.15/1.50  --reset_solvers                         false
% 7.15/1.50  --bc_imp_inh                            [conj_cone]
% 7.15/1.50  --conj_cone_tolerance                   3.
% 7.15/1.50  --extra_neg_conj                        none
% 7.15/1.50  --large_theory_mode                     true
% 7.15/1.50  --prolific_symb_bound                   200
% 7.15/1.50  --lt_threshold                          2000
% 7.15/1.50  --clause_weak_htbl                      true
% 7.15/1.50  --gc_record_bc_elim                     false
% 7.15/1.50  
% 7.15/1.50  ------ Preprocessing Options
% 7.15/1.50  
% 7.15/1.50  --preprocessing_flag                    true
% 7.15/1.50  --time_out_prep_mult                    0.1
% 7.15/1.50  --splitting_mode                        input
% 7.15/1.50  --splitting_grd                         true
% 7.15/1.50  --splitting_cvd                         false
% 7.15/1.50  --splitting_cvd_svl                     false
% 7.15/1.50  --splitting_nvd                         32
% 7.15/1.50  --sub_typing                            true
% 7.15/1.50  --prep_gs_sim                           true
% 7.15/1.50  --prep_unflatten                        true
% 7.15/1.50  --prep_res_sim                          true
% 7.15/1.50  --prep_upred                            true
% 7.15/1.50  --prep_sem_filter                       exhaustive
% 7.15/1.50  --prep_sem_filter_out                   false
% 7.15/1.50  --pred_elim                             true
% 7.15/1.50  --res_sim_input                         true
% 7.15/1.50  --eq_ax_congr_red                       true
% 7.15/1.50  --pure_diseq_elim                       true
% 7.15/1.50  --brand_transform                       false
% 7.15/1.50  --non_eq_to_eq                          false
% 7.15/1.50  --prep_def_merge                        true
% 7.15/1.50  --prep_def_merge_prop_impl              false
% 7.15/1.50  --prep_def_merge_mbd                    true
% 7.15/1.50  --prep_def_merge_tr_red                 false
% 7.15/1.50  --prep_def_merge_tr_cl                  false
% 7.15/1.50  --smt_preprocessing                     true
% 7.15/1.50  --smt_ac_axioms                         fast
% 7.15/1.50  --preprocessed_out                      false
% 7.15/1.50  --preprocessed_stats                    false
% 7.15/1.50  
% 7.15/1.50  ------ Abstraction refinement Options
% 7.15/1.50  
% 7.15/1.50  --abstr_ref                             []
% 7.15/1.50  --abstr_ref_prep                        false
% 7.15/1.50  --abstr_ref_until_sat                   false
% 7.15/1.50  --abstr_ref_sig_restrict                funpre
% 7.15/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.15/1.50  --abstr_ref_under                       []
% 7.15/1.50  
% 7.15/1.50  ------ SAT Options
% 7.15/1.50  
% 7.15/1.50  --sat_mode                              false
% 7.15/1.50  --sat_fm_restart_options                ""
% 7.15/1.50  --sat_gr_def                            false
% 7.15/1.50  --sat_epr_types                         true
% 7.15/1.50  --sat_non_cyclic_types                  false
% 7.15/1.50  --sat_finite_models                     false
% 7.15/1.50  --sat_fm_lemmas                         false
% 7.15/1.50  --sat_fm_prep                           false
% 7.15/1.50  --sat_fm_uc_incr                        true
% 7.15/1.50  --sat_out_model                         small
% 7.15/1.50  --sat_out_clauses                       false
% 7.15/1.50  
% 7.15/1.50  ------ QBF Options
% 7.15/1.50  
% 7.15/1.50  --qbf_mode                              false
% 7.15/1.50  --qbf_elim_univ                         false
% 7.15/1.50  --qbf_dom_inst                          none
% 7.15/1.50  --qbf_dom_pre_inst                      false
% 7.15/1.50  --qbf_sk_in                             false
% 7.15/1.50  --qbf_pred_elim                         true
% 7.15/1.50  --qbf_split                             512
% 7.15/1.50  
% 7.15/1.50  ------ BMC1 Options
% 7.15/1.50  
% 7.15/1.50  --bmc1_incremental                      false
% 7.15/1.50  --bmc1_axioms                           reachable_all
% 7.15/1.50  --bmc1_min_bound                        0
% 7.15/1.50  --bmc1_max_bound                        -1
% 7.15/1.50  --bmc1_max_bound_default                -1
% 7.15/1.50  --bmc1_symbol_reachability              true
% 7.15/1.50  --bmc1_property_lemmas                  false
% 7.15/1.50  --bmc1_k_induction                      false
% 7.15/1.50  --bmc1_non_equiv_states                 false
% 7.15/1.50  --bmc1_deadlock                         false
% 7.15/1.50  --bmc1_ucm                              false
% 7.15/1.50  --bmc1_add_unsat_core                   none
% 7.15/1.50  --bmc1_unsat_core_children              false
% 7.15/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.15/1.50  --bmc1_out_stat                         full
% 7.15/1.50  --bmc1_ground_init                      false
% 7.15/1.50  --bmc1_pre_inst_next_state              false
% 7.15/1.50  --bmc1_pre_inst_state                   false
% 7.15/1.50  --bmc1_pre_inst_reach_state             false
% 7.15/1.50  --bmc1_out_unsat_core                   false
% 7.15/1.50  --bmc1_aig_witness_out                  false
% 7.15/1.50  --bmc1_verbose                          false
% 7.15/1.50  --bmc1_dump_clauses_tptp                false
% 7.15/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.15/1.50  --bmc1_dump_file                        -
% 7.15/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.15/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.15/1.50  --bmc1_ucm_extend_mode                  1
% 7.15/1.50  --bmc1_ucm_init_mode                    2
% 7.15/1.50  --bmc1_ucm_cone_mode                    none
% 7.15/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.15/1.50  --bmc1_ucm_relax_model                  4
% 7.15/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.15/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.15/1.50  --bmc1_ucm_layered_model                none
% 7.15/1.50  --bmc1_ucm_max_lemma_size               10
% 7.15/1.50  
% 7.15/1.50  ------ AIG Options
% 7.15/1.50  
% 7.15/1.50  --aig_mode                              false
% 7.15/1.50  
% 7.15/1.50  ------ Instantiation Options
% 7.15/1.50  
% 7.15/1.50  --instantiation_flag                    true
% 7.15/1.50  --inst_sos_flag                         false
% 7.15/1.50  --inst_sos_phase                        true
% 7.15/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.15/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.15/1.50  --inst_lit_sel_side                     none
% 7.15/1.50  --inst_solver_per_active                1400
% 7.15/1.50  --inst_solver_calls_frac                1.
% 7.15/1.50  --inst_passive_queue_type               priority_queues
% 7.15/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.15/1.50  --inst_passive_queues_freq              [25;2]
% 7.15/1.50  --inst_dismatching                      true
% 7.15/1.50  --inst_eager_unprocessed_to_passive     true
% 7.15/1.50  --inst_prop_sim_given                   true
% 7.15/1.50  --inst_prop_sim_new                     false
% 7.15/1.50  --inst_subs_new                         false
% 7.15/1.50  --inst_eq_res_simp                      false
% 7.15/1.50  --inst_subs_given                       false
% 7.15/1.50  --inst_orphan_elimination               true
% 7.15/1.50  --inst_learning_loop_flag               true
% 7.15/1.50  --inst_learning_start                   3000
% 7.15/1.50  --inst_learning_factor                  2
% 7.15/1.50  --inst_start_prop_sim_after_learn       3
% 7.15/1.50  --inst_sel_renew                        solver
% 7.15/1.50  --inst_lit_activity_flag                true
% 7.15/1.50  --inst_restr_to_given                   false
% 7.15/1.50  --inst_activity_threshold               500
% 7.15/1.50  --inst_out_proof                        true
% 7.15/1.50  
% 7.15/1.50  ------ Resolution Options
% 7.15/1.50  
% 7.15/1.50  --resolution_flag                       false
% 7.15/1.50  --res_lit_sel                           adaptive
% 7.15/1.50  --res_lit_sel_side                      none
% 7.15/1.50  --res_ordering                          kbo
% 7.15/1.50  --res_to_prop_solver                    active
% 7.15/1.50  --res_prop_simpl_new                    false
% 7.15/1.50  --res_prop_simpl_given                  true
% 7.15/1.50  --res_passive_queue_type                priority_queues
% 7.15/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.15/1.50  --res_passive_queues_freq               [15;5]
% 7.15/1.50  --res_forward_subs                      full
% 7.15/1.50  --res_backward_subs                     full
% 7.15/1.50  --res_forward_subs_resolution           true
% 7.15/1.50  --res_backward_subs_resolution          true
% 7.15/1.50  --res_orphan_elimination                true
% 7.15/1.50  --res_time_limit                        2.
% 7.15/1.50  --res_out_proof                         true
% 7.15/1.50  
% 7.15/1.50  ------ Superposition Options
% 7.15/1.50  
% 7.15/1.50  --superposition_flag                    true
% 7.15/1.50  --sup_passive_queue_type                priority_queues
% 7.15/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.15/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.15/1.50  --demod_completeness_check              fast
% 7.15/1.50  --demod_use_ground                      true
% 7.15/1.50  --sup_to_prop_solver                    passive
% 7.15/1.50  --sup_prop_simpl_new                    true
% 7.15/1.50  --sup_prop_simpl_given                  true
% 7.15/1.50  --sup_fun_splitting                     false
% 7.15/1.50  --sup_smt_interval                      50000
% 7.15/1.50  
% 7.15/1.50  ------ Superposition Simplification Setup
% 7.15/1.50  
% 7.15/1.50  --sup_indices_passive                   []
% 7.15/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.15/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.15/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.15/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.15/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.15/1.50  --sup_full_bw                           [BwDemod]
% 7.15/1.50  --sup_immed_triv                        [TrivRules]
% 7.15/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.15/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.15/1.50  --sup_immed_bw_main                     []
% 7.15/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.15/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.15/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.15/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.15/1.50  
% 7.15/1.50  ------ Combination Options
% 7.15/1.50  
% 7.15/1.50  --comb_res_mult                         3
% 7.15/1.50  --comb_sup_mult                         2
% 7.15/1.50  --comb_inst_mult                        10
% 7.15/1.50  
% 7.15/1.50  ------ Debug Options
% 7.15/1.50  
% 7.15/1.50  --dbg_backtrace                         false
% 7.15/1.50  --dbg_dump_prop_clauses                 false
% 7.15/1.50  --dbg_dump_prop_clauses_file            -
% 7.15/1.50  --dbg_out_stat                          false
% 7.15/1.50  
% 7.15/1.50  
% 7.15/1.50  
% 7.15/1.50  
% 7.15/1.50  ------ Proving...
% 7.15/1.50  
% 7.15/1.50  
% 7.15/1.50  % SZS status Theorem for theBenchmark.p
% 7.15/1.50  
% 7.15/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.15/1.50  
% 7.15/1.50  fof(f23,conjecture,(
% 7.15/1.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 7.15/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f24,negated_conjecture,(
% 7.15/1.50    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 7.15/1.50    inference(negated_conjecture,[],[f23])).
% 7.15/1.50  
% 7.15/1.50  fof(f53,plain,(
% 7.15/1.50    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 7.15/1.50    inference(ennf_transformation,[],[f24])).
% 7.15/1.50  
% 7.15/1.50  fof(f54,plain,(
% 7.15/1.50    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 7.15/1.50    inference(flattening,[],[f53])).
% 7.15/1.50  
% 7.15/1.50  fof(f62,plain,(
% 7.15/1.50    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 7.15/1.50    introduced(choice_axiom,[])).
% 7.15/1.50  
% 7.15/1.50  fof(f61,plain,(
% 7.15/1.50    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 7.15/1.50    introduced(choice_axiom,[])).
% 7.15/1.50  
% 7.15/1.50  fof(f60,plain,(
% 7.15/1.50    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 7.15/1.50    introduced(choice_axiom,[])).
% 7.15/1.50  
% 7.15/1.50  fof(f63,plain,(
% 7.15/1.50    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 7.15/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f54,f62,f61,f60])).
% 7.15/1.50  
% 7.15/1.50  fof(f99,plain,(
% 7.15/1.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 7.15/1.50    inference(cnf_transformation,[],[f63])).
% 7.15/1.50  
% 7.15/1.50  fof(f20,axiom,(
% 7.15/1.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 7.15/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f48,plain,(
% 7.15/1.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 7.15/1.50    inference(ennf_transformation,[],[f20])).
% 7.15/1.50  
% 7.15/1.50  fof(f91,plain,(
% 7.15/1.50    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f48])).
% 7.15/1.50  
% 7.15/1.50  fof(f96,plain,(
% 7.15/1.50    l1_struct_0(sK1)),
% 7.15/1.50    inference(cnf_transformation,[],[f63])).
% 7.15/1.50  
% 7.15/1.50  fof(f94,plain,(
% 7.15/1.50    l1_struct_0(sK0)),
% 7.15/1.50    inference(cnf_transformation,[],[f63])).
% 7.15/1.50  
% 7.15/1.50  fof(f15,axiom,(
% 7.15/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.15/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f40,plain,(
% 7.15/1.50    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.15/1.50    inference(ennf_transformation,[],[f15])).
% 7.15/1.50  
% 7.15/1.50  fof(f82,plain,(
% 7.15/1.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.15/1.50    inference(cnf_transformation,[],[f40])).
% 7.15/1.50  
% 7.15/1.50  fof(f100,plain,(
% 7.15/1.50    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 7.15/1.50    inference(cnf_transformation,[],[f63])).
% 7.15/1.50  
% 7.15/1.50  fof(f19,axiom,(
% 7.15/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 7.15/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f46,plain,(
% 7.15/1.50    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.15/1.50    inference(ennf_transformation,[],[f19])).
% 7.15/1.50  
% 7.15/1.50  fof(f47,plain,(
% 7.15/1.50    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.15/1.50    inference(flattening,[],[f46])).
% 7.15/1.50  
% 7.15/1.50  fof(f90,plain,(
% 7.15/1.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f47])).
% 7.15/1.50  
% 7.15/1.50  fof(f101,plain,(
% 7.15/1.50    v2_funct_1(sK2)),
% 7.15/1.50    inference(cnf_transformation,[],[f63])).
% 7.15/1.50  
% 7.15/1.50  fof(f97,plain,(
% 7.15/1.50    v1_funct_1(sK2)),
% 7.15/1.50    inference(cnf_transformation,[],[f63])).
% 7.15/1.50  
% 7.15/1.50  fof(f98,plain,(
% 7.15/1.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 7.15/1.50    inference(cnf_transformation,[],[f63])).
% 7.15/1.50  
% 7.15/1.50  fof(f10,axiom,(
% 7.15/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.15/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f25,plain,(
% 7.15/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.15/1.50    inference(pure_predicate_removal,[],[f10])).
% 7.15/1.50  
% 7.15/1.50  fof(f35,plain,(
% 7.15/1.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.15/1.50    inference(ennf_transformation,[],[f25])).
% 7.15/1.50  
% 7.15/1.50  fof(f77,plain,(
% 7.15/1.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.15/1.50    inference(cnf_transformation,[],[f35])).
% 7.15/1.50  
% 7.15/1.50  fof(f7,axiom,(
% 7.15/1.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.15/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f29,plain,(
% 7.15/1.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.15/1.50    inference(ennf_transformation,[],[f7])).
% 7.15/1.50  
% 7.15/1.50  fof(f30,plain,(
% 7.15/1.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.15/1.50    inference(flattening,[],[f29])).
% 7.15/1.50  
% 7.15/1.50  fof(f74,plain,(
% 7.15/1.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f30])).
% 7.15/1.50  
% 7.15/1.50  fof(f5,axiom,(
% 7.15/1.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.15/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f72,plain,(
% 7.15/1.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.15/1.50    inference(cnf_transformation,[],[f5])).
% 7.15/1.50  
% 7.15/1.50  fof(f4,axiom,(
% 7.15/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.15/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f27,plain,(
% 7.15/1.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.15/1.50    inference(ennf_transformation,[],[f4])).
% 7.15/1.50  
% 7.15/1.50  fof(f71,plain,(
% 7.15/1.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f27])).
% 7.15/1.50  
% 7.15/1.50  fof(f17,axiom,(
% 7.15/1.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 7.15/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f42,plain,(
% 7.15/1.50    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.15/1.50    inference(ennf_transformation,[],[f17])).
% 7.15/1.50  
% 7.15/1.50  fof(f43,plain,(
% 7.15/1.50    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.15/1.50    inference(flattening,[],[f42])).
% 7.15/1.50  
% 7.15/1.50  fof(f85,plain,(
% 7.15/1.50    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f43])).
% 7.15/1.50  
% 7.15/1.50  fof(f18,axiom,(
% 7.15/1.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 7.15/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f44,plain,(
% 7.15/1.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.15/1.50    inference(ennf_transformation,[],[f18])).
% 7.15/1.50  
% 7.15/1.50  fof(f45,plain,(
% 7.15/1.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.15/1.50    inference(flattening,[],[f44])).
% 7.15/1.50  
% 7.15/1.50  fof(f59,plain,(
% 7.15/1.50    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.15/1.50    inference(nnf_transformation,[],[f45])).
% 7.15/1.50  
% 7.15/1.50  fof(f86,plain,(
% 7.15/1.50    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f59])).
% 7.15/1.50  
% 7.15/1.50  fof(f95,plain,(
% 7.15/1.50    ~v2_struct_0(sK1)),
% 7.15/1.50    inference(cnf_transformation,[],[f63])).
% 7.15/1.50  
% 7.15/1.50  fof(f21,axiom,(
% 7.15/1.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 7.15/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f49,plain,(
% 7.15/1.50    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 7.15/1.50    inference(ennf_transformation,[],[f21])).
% 7.15/1.50  
% 7.15/1.50  fof(f50,plain,(
% 7.15/1.50    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 7.15/1.50    inference(flattening,[],[f49])).
% 7.15/1.50  
% 7.15/1.50  fof(f92,plain,(
% 7.15/1.50    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f50])).
% 7.15/1.50  
% 7.15/1.50  fof(f6,axiom,(
% 7.15/1.50    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 7.15/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f28,plain,(
% 7.15/1.50    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.15/1.50    inference(ennf_transformation,[],[f6])).
% 7.15/1.50  
% 7.15/1.50  fof(f73,plain,(
% 7.15/1.50    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f28])).
% 7.15/1.50  
% 7.15/1.50  fof(f2,axiom,(
% 7.15/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.15/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f55,plain,(
% 7.15/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.15/1.50    inference(nnf_transformation,[],[f2])).
% 7.15/1.50  
% 7.15/1.50  fof(f56,plain,(
% 7.15/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.15/1.50    inference(flattening,[],[f55])).
% 7.15/1.50  
% 7.15/1.50  fof(f65,plain,(
% 7.15/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.15/1.50    inference(cnf_transformation,[],[f56])).
% 7.15/1.50  
% 7.15/1.50  fof(f104,plain,(
% 7.15/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.15/1.50    inference(equality_resolution,[],[f65])).
% 7.15/1.50  
% 7.15/1.50  fof(f9,axiom,(
% 7.15/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 7.15/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f33,plain,(
% 7.15/1.50    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | (~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.15/1.50    inference(ennf_transformation,[],[f9])).
% 7.15/1.50  
% 7.15/1.50  fof(f34,plain,(
% 7.15/1.50    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.15/1.50    inference(flattening,[],[f33])).
% 7.15/1.50  
% 7.15/1.50  fof(f76,plain,(
% 7.15/1.50    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f34])).
% 7.15/1.50  
% 7.15/1.50  fof(f88,plain,(
% 7.15/1.50    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f47])).
% 7.15/1.50  
% 7.15/1.50  fof(f89,plain,(
% 7.15/1.50    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f47])).
% 7.15/1.50  
% 7.15/1.50  fof(f1,axiom,(
% 7.15/1.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.15/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f26,plain,(
% 7.15/1.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.15/1.50    inference(ennf_transformation,[],[f1])).
% 7.15/1.50  
% 7.15/1.50  fof(f64,plain,(
% 7.15/1.50    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f26])).
% 7.15/1.50  
% 7.15/1.50  fof(f22,axiom,(
% 7.15/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 7.15/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f51,plain,(
% 7.15/1.50    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.15/1.50    inference(ennf_transformation,[],[f22])).
% 7.15/1.50  
% 7.15/1.50  fof(f52,plain,(
% 7.15/1.50    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.15/1.50    inference(flattening,[],[f51])).
% 7.15/1.50  
% 7.15/1.50  fof(f93,plain,(
% 7.15/1.50    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f52])).
% 7.15/1.50  
% 7.15/1.50  fof(f102,plain,(
% 7.15/1.50    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 7.15/1.50    inference(cnf_transformation,[],[f63])).
% 7.15/1.50  
% 7.15/1.50  fof(f14,axiom,(
% 7.15/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.15/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f39,plain,(
% 7.15/1.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.15/1.50    inference(ennf_transformation,[],[f14])).
% 7.15/1.50  
% 7.15/1.50  fof(f81,plain,(
% 7.15/1.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.15/1.50    inference(cnf_transformation,[],[f39])).
% 7.15/1.50  
% 7.15/1.50  fof(f11,axiom,(
% 7.15/1.50    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 7.15/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f36,plain,(
% 7.15/1.50    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 7.15/1.50    inference(ennf_transformation,[],[f11])).
% 7.15/1.50  
% 7.15/1.50  fof(f78,plain,(
% 7.15/1.50    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 7.15/1.50    inference(cnf_transformation,[],[f36])).
% 7.15/1.50  
% 7.15/1.50  fof(f3,axiom,(
% 7.15/1.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.15/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f57,plain,(
% 7.15/1.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.15/1.50    inference(nnf_transformation,[],[f3])).
% 7.15/1.50  
% 7.15/1.50  fof(f58,plain,(
% 7.15/1.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.15/1.50    inference(flattening,[],[f57])).
% 7.15/1.50  
% 7.15/1.50  fof(f69,plain,(
% 7.15/1.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.15/1.50    inference(cnf_transformation,[],[f58])).
% 7.15/1.50  
% 7.15/1.50  fof(f106,plain,(
% 7.15/1.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.15/1.50    inference(equality_resolution,[],[f69])).
% 7.15/1.50  
% 7.15/1.50  fof(f12,axiom,(
% 7.15/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 7.15/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.15/1.50  
% 7.15/1.50  fof(f37,plain,(
% 7.15/1.50    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.15/1.50    inference(ennf_transformation,[],[f12])).
% 7.15/1.50  
% 7.15/1.50  fof(f79,plain,(
% 7.15/1.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.15/1.50    inference(cnf_transformation,[],[f37])).
% 7.15/1.50  
% 7.15/1.50  fof(f70,plain,(
% 7.15/1.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.15/1.50    inference(cnf_transformation,[],[f58])).
% 7.15/1.50  
% 7.15/1.50  fof(f105,plain,(
% 7.15/1.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.15/1.50    inference(equality_resolution,[],[f70])).
% 7.15/1.50  
% 7.15/1.50  cnf(c_33,negated_conjecture,
% 7.15/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 7.15/1.50      inference(cnf_transformation,[],[f99]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1455,plain,
% 7.15/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_27,plain,
% 7.15/1.50      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.15/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_36,negated_conjecture,
% 7.15/1.50      ( l1_struct_0(sK1) ),
% 7.15/1.50      inference(cnf_transformation,[],[f96]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_396,plain,
% 7.15/1.50      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 7.15/1.50      inference(resolution_lifted,[status(thm)],[c_27,c_36]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_397,plain,
% 7.15/1.50      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 7.15/1.50      inference(unflattening,[status(thm)],[c_396]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_38,negated_conjecture,
% 7.15/1.50      ( l1_struct_0(sK0) ),
% 7.15/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_401,plain,
% 7.15/1.50      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 7.15/1.50      inference(resolution_lifted,[status(thm)],[c_27,c_38]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_402,plain,
% 7.15/1.50      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 7.15/1.50      inference(unflattening,[status(thm)],[c_401]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1494,plain,
% 7.15/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 7.15/1.50      inference(light_normalisation,[status(thm)],[c_1455,c_397,c_402]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_18,plain,
% 7.15/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.15/1.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.15/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1457,plain,
% 7.15/1.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.15/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2921,plain,
% 7.15/1.50      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1494,c_1457]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_32,negated_conjecture,
% 7.15/1.50      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 7.15/1.50      inference(cnf_transformation,[],[f100]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1487,plain,
% 7.15/1.50      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 7.15/1.50      inference(light_normalisation,[status(thm)],[c_32,c_397,c_402]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3046,plain,
% 7.15/1.50      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_2921,c_1487]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_24,plain,
% 7.15/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.15/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.15/1.50      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.15/1.50      | ~ v1_funct_1(X0)
% 7.15/1.50      | ~ v2_funct_1(X0)
% 7.15/1.50      | k2_relset_1(X1,X2,X0) != X2 ),
% 7.15/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_31,negated_conjecture,
% 7.15/1.50      ( v2_funct_1(sK2) ),
% 7.15/1.50      inference(cnf_transformation,[],[f101]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_590,plain,
% 7.15/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.15/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.15/1.50      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.15/1.50      | ~ v1_funct_1(X0)
% 7.15/1.50      | k2_relset_1(X1,X2,X0) != X2
% 7.15/1.50      | sK2 != X0 ),
% 7.15/1.50      inference(resolution_lifted,[status(thm)],[c_24,c_31]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_591,plain,
% 7.15/1.50      ( ~ v1_funct_2(sK2,X0,X1)
% 7.15/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.15/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.15/1.50      | ~ v1_funct_1(sK2)
% 7.15/1.50      | k2_relset_1(X0,X1,sK2) != X1 ),
% 7.15/1.50      inference(unflattening,[status(thm)],[c_590]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_35,negated_conjecture,
% 7.15/1.50      ( v1_funct_1(sK2) ),
% 7.15/1.50      inference(cnf_transformation,[],[f97]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_595,plain,
% 7.15/1.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.15/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.15/1.50      | ~ v1_funct_2(sK2,X0,X1)
% 7.15/1.50      | k2_relset_1(X0,X1,sK2) != X1 ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_591,c_35]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_596,plain,
% 7.15/1.50      ( ~ v1_funct_2(sK2,X0,X1)
% 7.15/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.15/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.15/1.50      | k2_relset_1(X0,X1,sK2) != X1 ),
% 7.15/1.50      inference(renaming,[status(thm)],[c_595]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1446,plain,
% 7.15/1.50      ( k2_relset_1(X0,X1,sK2) != X1
% 7.15/1.50      | v1_funct_2(sK2,X0,X1) != iProver_top
% 7.15/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 7.15/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_596]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2227,plain,
% 7.15/1.50      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 7.15/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 7.15/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1487,c_1446]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_34,negated_conjecture,
% 7.15/1.50      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 7.15/1.50      inference(cnf_transformation,[],[f98]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1454,plain,
% 7.15/1.50      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1484,plain,
% 7.15/1.50      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 7.15/1.50      inference(light_normalisation,[status(thm)],[c_1454,c_397,c_402]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2472,plain,
% 7.15/1.50      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_2227,c_1494,c_1484]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3055,plain,
% 7.15/1.50      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_3046,c_2472]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_13,plain,
% 7.15/1.50      ( v4_relat_1(X0,X1)
% 7.15/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.15/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_10,plain,
% 7.15/1.50      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.15/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_502,plain,
% 7.15/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.15/1.50      | ~ v1_relat_1(X0)
% 7.15/1.50      | k7_relat_1(X0,X1) = X0 ),
% 7.15/1.50      inference(resolution,[status(thm)],[c_13,c_10]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1451,plain,
% 7.15/1.50      ( k7_relat_1(X0,X1) = X0
% 7.15/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.15/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_502]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3899,plain,
% 7.15/1.50      ( k7_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_funct_1(sK2)
% 7.15/1.50      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_3055,c_1451]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_43,plain,
% 7.15/1.50      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_44,plain,
% 7.15/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_53,plain,
% 7.15/1.50      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_27]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1676,plain,
% 7.15/1.50      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 7.15/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.15/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.15/1.50      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_596]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1677,plain,
% 7.15/1.50      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 7.15/1.50      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 7.15/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
% 7.15/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_1676]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_8,plain,
% 7.15/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.15/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1916,plain,
% 7.15/1.50      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1917,plain,
% 7.15/1.50      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_1916]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_975,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1766,plain,
% 7.15/1.50      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
% 7.15/1.50      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 7.15/1.50      | u1_struct_0(sK1) != X0 ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_975]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1999,plain,
% 7.15/1.50      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 7.15/1.50      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 7.15/1.50      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_1766]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_7,plain,
% 7.15/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.15/1.50      | ~ v1_relat_1(X1)
% 7.15/1.50      | v1_relat_1(X0) ),
% 7.15/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1685,plain,
% 7.15/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.15/1.50      | v1_relat_1(X0)
% 7.15/1.50      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2258,plain,
% 7.15/1.50      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.15/1.50      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 7.15/1.50      | v1_relat_1(k2_funct_1(sK2)) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_1685]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2274,plain,
% 7.15/1.50      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 7.15/1.50      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
% 7.15/1.50      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_2258]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_5432,plain,
% 7.15/1.50      ( k7_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_funct_1(sK2) ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_3899,c_36,c_43,c_44,c_32,c_53,c_1677,c_1917,c_1999,
% 7.15/1.50                 c_2274]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_20,plain,
% 7.15/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.15/1.50      | v1_partfun1(X0,X1)
% 7.15/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.15/1.50      | ~ v1_funct_1(X0)
% 7.15/1.50      | v1_xboole_0(X2) ),
% 7.15/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_23,plain,
% 7.15/1.50      ( ~ v1_partfun1(X0,X1)
% 7.15/1.50      | ~ v4_relat_1(X0,X1)
% 7.15/1.50      | ~ v1_relat_1(X0)
% 7.15/1.50      | k1_relat_1(X0) = X1 ),
% 7.15/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_464,plain,
% 7.15/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.15/1.50      | ~ v4_relat_1(X0,X1)
% 7.15/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.15/1.50      | ~ v1_funct_1(X0)
% 7.15/1.50      | ~ v1_relat_1(X0)
% 7.15/1.50      | v1_xboole_0(X2)
% 7.15/1.50      | k1_relat_1(X0) = X1 ),
% 7.15/1.50      inference(resolution,[status(thm)],[c_20,c_23]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_468,plain,
% 7.15/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.15/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.15/1.50      | ~ v1_funct_1(X0)
% 7.15/1.50      | ~ v1_relat_1(X0)
% 7.15/1.50      | v1_xboole_0(X2)
% 7.15/1.50      | k1_relat_1(X0) = X1 ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_464,c_13]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1450,plain,
% 7.15/1.50      ( k1_relat_1(X0) = X1
% 7.15/1.50      | v1_funct_2(X0,X1,X2) != iProver_top
% 7.15/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.15/1.50      | v1_funct_1(X0) != iProver_top
% 7.15/1.50      | v1_relat_1(X0) != iProver_top
% 7.15/1.50      | v1_xboole_0(X2) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_468]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2695,plain,
% 7.15/1.50      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 7.15/1.50      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 7.15/1.50      | v1_funct_1(sK2) != iProver_top
% 7.15/1.50      | v1_relat_1(sK2) != iProver_top
% 7.15/1.50      | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1494,c_1450]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_37,negated_conjecture,
% 7.15/1.50      ( ~ v2_struct_0(sK1) ),
% 7.15/1.50      inference(cnf_transformation,[],[f95]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_40,plain,
% 7.15/1.50      ( v2_struct_0(sK1) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_41,plain,
% 7.15/1.50      ( l1_struct_0(sK1) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_42,plain,
% 7.15/1.50      ( v1_funct_1(sK2) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_28,plain,
% 7.15/1.50      ( v2_struct_0(X0)
% 7.15/1.50      | ~ l1_struct_0(X0)
% 7.15/1.50      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 7.15/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_49,plain,
% 7.15/1.50      ( v2_struct_0(X0) = iProver_top
% 7.15/1.50      | l1_struct_0(X0) != iProver_top
% 7.15/1.50      | v1_xboole_0(k2_struct_0(X0)) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_51,plain,
% 7.15/1.50      ( v2_struct_0(sK1) = iProver_top
% 7.15/1.50      | l1_struct_0(sK1) != iProver_top
% 7.15/1.50      | v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_49]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1776,plain,
% 7.15/1.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 7.15/1.50      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 7.15/1.50      | v1_relat_1(sK2) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_1685]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1777,plain,
% 7.15/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 7.15/1.50      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 7.15/1.50      | v1_relat_1(sK2) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_1776]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1908,plain,
% 7.15/1.50      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1909,plain,
% 7.15/1.50      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_1908]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3969,plain,
% 7.15/1.50      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_2695,c_40,c_41,c_42,c_44,c_51,c_1484,c_1777,c_1909]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3973,plain,
% 7.15/1.50      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_3969,c_3055]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1464,plain,
% 7.15/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.15/1.50      | v1_relat_1(X1) != iProver_top
% 7.15/1.50      | v1_relat_1(X0) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_5212,plain,
% 7.15/1.50      ( v1_relat_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))) != iProver_top
% 7.15/1.50      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_3973,c_1464]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_6631,plain,
% 7.15/1.50      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_5212,c_36,c_43,c_44,c_32,c_53,c_1677,c_1917,c_1999,
% 7.15/1.50                 c_2274]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_9,plain,
% 7.15/1.50      ( ~ v1_relat_1(X0)
% 7.15/1.50      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 7.15/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1462,plain,
% 7.15/1.50      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 7.15/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_6636,plain,
% 7.15/1.50      ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0)) = k9_relat_1(k2_funct_1(sK2),X0) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_6631,c_1462]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_7804,plain,
% 7.15/1.50      ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_5432,c_6636]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3059,plain,
% 7.15/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_3046,c_1494]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3784,plain,
% 7.15/1.50      ( k7_relat_1(sK2,k2_struct_0(sK0)) = sK2
% 7.15/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_3059,c_1451]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_5345,plain,
% 7.15/1.50      ( k7_relat_1(sK2,k2_struct_0(sK0)) = sK2 ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_3784,c_44,c_1777,c_1909]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_5347,plain,
% 7.15/1.50      ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
% 7.15/1.50      inference(light_normalisation,[status(thm)],[c_5345,c_3969]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3976,plain,
% 7.15/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_3969,c_3059]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4648,plain,
% 7.15/1.50      ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != iProver_top
% 7.15/1.50      | v1_relat_1(sK2) = iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_3976,c_1464]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_5982,plain,
% 7.15/1.50      ( v1_relat_1(sK2) = iProver_top ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_4648,c_44,c_1777,c_1909]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_5987,plain,
% 7.15/1.50      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_5982,c_1462]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_7602,plain,
% 7.15/1.50      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_5347,c_5987]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3,plain,
% 7.15/1.50      ( r1_tarski(X0,X0) ),
% 7.15/1.50      inference(cnf_transformation,[],[f104]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1465,plain,
% 7.15/1.50      ( r1_tarski(X0,X0) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_12,plain,
% 7.15/1.50      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.15/1.50      | ~ v1_funct_1(X1)
% 7.15/1.50      | ~ v2_funct_1(X1)
% 7.15/1.50      | ~ v1_relat_1(X1)
% 7.15/1.50      | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0 ),
% 7.15/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_628,plain,
% 7.15/1.50      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.15/1.50      | ~ v1_funct_1(X1)
% 7.15/1.50      | ~ v1_relat_1(X1)
% 7.15/1.50      | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0
% 7.15/1.50      | sK2 != X1 ),
% 7.15/1.50      inference(resolution_lifted,[status(thm)],[c_12,c_31]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_629,plain,
% 7.15/1.50      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 7.15/1.50      | ~ v1_funct_1(sK2)
% 7.15/1.50      | ~ v1_relat_1(sK2)
% 7.15/1.50      | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0 ),
% 7.15/1.50      inference(unflattening,[status(thm)],[c_628]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_633,plain,
% 7.15/1.50      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 7.15/1.50      | ~ v1_relat_1(sK2)
% 7.15/1.50      | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0 ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_629,c_35]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1444,plain,
% 7.15/1.50      ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0
% 7.15/1.50      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 7.15/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1866,plain,
% 7.15/1.50      ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2))) = k1_relat_1(sK2)
% 7.15/1.50      | v1_relat_1(sK2) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1465,c_1444]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1867,plain,
% 7.15/1.50      ( ~ v1_relat_1(sK2)
% 7.15/1.50      | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2))) = k1_relat_1(sK2) ),
% 7.15/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_1866]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2551,plain,
% 7.15/1.50      ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2))) = k1_relat_1(sK2) ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_1866,c_33,c_1776,c_1867,c_1908]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_7709,plain,
% 7.15/1.50      ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_7602,c_2551]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_7805,plain,
% 7.15/1.50      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.15/1.50      inference(light_normalisation,[status(thm)],[c_7804,c_7709]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2696,plain,
% 7.15/1.50      ( k1_relat_1(k2_funct_1(sK2)) = k2_struct_0(sK1)
% 7.15/1.50      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 7.15/1.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 7.15/1.50      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 7.15/1.50      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_2472,c_1450]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_26,plain,
% 7.15/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.15/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.15/1.50      | ~ v1_funct_1(X0)
% 7.15/1.50      | v1_funct_1(k2_funct_1(X0))
% 7.15/1.50      | ~ v2_funct_1(X0)
% 7.15/1.50      | k2_relset_1(X1,X2,X0) != X2 ),
% 7.15/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_542,plain,
% 7.15/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.15/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.15/1.50      | ~ v1_funct_1(X0)
% 7.15/1.50      | v1_funct_1(k2_funct_1(X0))
% 7.15/1.50      | k2_relset_1(X1,X2,X0) != X2
% 7.15/1.50      | sK2 != X0 ),
% 7.15/1.50      inference(resolution_lifted,[status(thm)],[c_26,c_31]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_543,plain,
% 7.15/1.50      ( ~ v1_funct_2(sK2,X0,X1)
% 7.15/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.15/1.50      | v1_funct_1(k2_funct_1(sK2))
% 7.15/1.50      | ~ v1_funct_1(sK2)
% 7.15/1.50      | k2_relset_1(X0,X1,sK2) != X1 ),
% 7.15/1.50      inference(unflattening,[status(thm)],[c_542]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_547,plain,
% 7.15/1.50      ( v1_funct_1(k2_funct_1(sK2))
% 7.15/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.15/1.50      | ~ v1_funct_2(sK2,X0,X1)
% 7.15/1.50      | k2_relset_1(X0,X1,sK2) != X1 ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_543,c_35]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_548,plain,
% 7.15/1.50      ( ~ v1_funct_2(sK2,X0,X1)
% 7.15/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.15/1.50      | v1_funct_1(k2_funct_1(sK2))
% 7.15/1.50      | k2_relset_1(X0,X1,sK2) != X1 ),
% 7.15/1.50      inference(renaming,[status(thm)],[c_547]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1448,plain,
% 7.15/1.50      ( k2_relset_1(X0,X1,sK2) != X1
% 7.15/1.50      | v1_funct_2(sK2,X0,X1) != iProver_top
% 7.15/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.15/1.50      | v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_548]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1952,plain,
% 7.15/1.50      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 7.15/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 7.15/1.50      | v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1487,c_1448]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_25,plain,
% 7.15/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.15/1.50      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 7.15/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.15/1.50      | ~ v1_funct_1(X0)
% 7.15/1.50      | ~ v2_funct_1(X0)
% 7.15/1.50      | k2_relset_1(X1,X2,X0) != X2 ),
% 7.15/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_566,plain,
% 7.15/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.15/1.50      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 7.15/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.15/1.50      | ~ v1_funct_1(X0)
% 7.15/1.50      | k2_relset_1(X1,X2,X0) != X2
% 7.15/1.50      | sK2 != X0 ),
% 7.15/1.50      inference(resolution_lifted,[status(thm)],[c_25,c_31]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_567,plain,
% 7.15/1.50      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 7.15/1.50      | ~ v1_funct_2(sK2,X1,X0)
% 7.15/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.15/1.50      | ~ v1_funct_1(sK2)
% 7.15/1.50      | k2_relset_1(X1,X0,sK2) != X0 ),
% 7.15/1.50      inference(unflattening,[status(thm)],[c_566]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_571,plain,
% 7.15/1.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.15/1.50      | ~ v1_funct_2(sK2,X1,X0)
% 7.15/1.50      | v1_funct_2(k2_funct_1(sK2),X0,X1)
% 7.15/1.50      | k2_relset_1(X1,X0,sK2) != X0 ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_567,c_35]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_572,plain,
% 7.15/1.50      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 7.15/1.50      | ~ v1_funct_2(sK2,X1,X0)
% 7.15/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.15/1.50      | k2_relset_1(X1,X0,sK2) != X0 ),
% 7.15/1.50      inference(renaming,[status(thm)],[c_571]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1447,plain,
% 7.15/1.50      ( k2_relset_1(X0,X1,sK2) != X1
% 7.15/1.50      | v1_funct_2(k2_funct_1(sK2),X1,X0) = iProver_top
% 7.15/1.50      | v1_funct_2(sK2,X0,X1) != iProver_top
% 7.15/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_572]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2042,plain,
% 7.15/1.50      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
% 7.15/1.50      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 7.15/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1487,c_1447]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4485,plain,
% 7.15/1.50      ( k1_relat_1(k2_funct_1(sK2)) = k2_struct_0(sK1)
% 7.15/1.50      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_2696,c_36,c_43,c_44,c_32,c_53,c_1494,c_1484,c_1677,
% 7.15/1.50                 c_1917,c_1952,c_1999,c_2042,c_2274]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4489,plain,
% 7.15/1.50      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 7.15/1.50      | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
% 7.15/1.50      inference(light_normalisation,[status(thm)],[c_4485,c_3046,c_3969]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_0,plain,
% 7.15/1.50      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.15/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1467,plain,
% 7.15/1.50      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4493,plain,
% 7.15/1.50      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 7.15/1.50      | k1_relat_1(sK2) = k1_xboole_0 ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_4489,c_1467]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_29,plain,
% 7.15/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.15/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.15/1.50      | ~ v1_funct_1(X0)
% 7.15/1.50      | ~ v2_funct_1(X0)
% 7.15/1.50      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 7.15/1.50      | k2_relset_1(X1,X2,X0) != X2 ),
% 7.15/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_518,plain,
% 7.15/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.15/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.15/1.50      | ~ v1_funct_1(X0)
% 7.15/1.50      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 7.15/1.50      | k2_relset_1(X1,X2,X0) != X2
% 7.15/1.50      | sK2 != X0 ),
% 7.15/1.50      inference(resolution_lifted,[status(thm)],[c_29,c_31]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_519,plain,
% 7.15/1.50      ( ~ v1_funct_2(sK2,X0,X1)
% 7.15/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.15/1.50      | ~ v1_funct_1(sK2)
% 7.15/1.50      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 7.15/1.50      | k2_relset_1(X0,X1,sK2) != X1 ),
% 7.15/1.50      inference(unflattening,[status(thm)],[c_518]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_523,plain,
% 7.15/1.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.15/1.50      | ~ v1_funct_2(sK2,X0,X1)
% 7.15/1.50      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 7.15/1.50      | k2_relset_1(X0,X1,sK2) != X1 ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_519,c_35]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_524,plain,
% 7.15/1.50      ( ~ v1_funct_2(sK2,X0,X1)
% 7.15/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.15/1.50      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 7.15/1.50      | k2_relset_1(X0,X1,sK2) != X1 ),
% 7.15/1.50      inference(renaming,[status(thm)],[c_523]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1449,plain,
% 7.15/1.50      ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 7.15/1.50      | k2_relset_1(X0,X1,sK2) != X1
% 7.15/1.50      | v1_funct_2(sK2,X0,X1) != iProver_top
% 7.15/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_524]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2158,plain,
% 7.15/1.50      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 7.15/1.50      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 7.15/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1487,c_1449]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2161,plain,
% 7.15/1.50      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_2158,c_1494,c_1484]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_30,negated_conjecture,
% 7.15/1.50      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 7.15/1.50      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 7.15/1.50      inference(cnf_transformation,[],[f102]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1569,plain,
% 7.15/1.50      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 7.15/1.50      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 7.15/1.50      inference(light_normalisation,[status(thm)],[c_30,c_397,c_402]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2164,plain,
% 7.15/1.50      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1)
% 7.15/1.50      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_2161,c_1569]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3056,plain,
% 7.15/1.50      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
% 7.15/1.50      | k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_3046,c_2164]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2922,plain,
% 7.15/1.50      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_2472,c_1457]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3804,plain,
% 7.15/1.50      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 7.15/1.50      inference(light_normalisation,[status(thm)],[c_2922,c_3046]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3965,plain,
% 7.15/1.50      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
% 7.15/1.50      | k2_relat_1(k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 7.15/1.50      inference(light_normalisation,[status(thm)],[c_3056,c_3804]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3972,plain,
% 7.15/1.50      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2)
% 7.15/1.50      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_3969,c_3965]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_17,plain,
% 7.15/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.15/1.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.15/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1458,plain,
% 7.15/1.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.15/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3896,plain,
% 7.15/1.50      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_3055,c_1458]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_5099,plain,
% 7.15/1.50      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 7.15/1.50      inference(light_normalisation,[status(thm)],[c_3896,c_3969]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_5435,plain,
% 7.15/1.50      ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
% 7.15/1.50      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 7.15/1.50      inference(light_normalisation,[status(thm)],[c_3972,c_5099]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_5521,plain,
% 7.15/1.50      ( k1_relat_1(sK2) = k1_xboole_0
% 7.15/1.50      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_4493,c_5435]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_7808,plain,
% 7.15/1.50      ( k1_relat_1(sK2) != k1_relat_1(sK2)
% 7.15/1.50      | k1_relat_1(sK2) = k1_xboole_0 ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_7805,c_5521]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_7816,plain,
% 7.15/1.50      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 7.15/1.50      inference(equality_resolution_simp,[status(thm)],[c_7808]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_14,plain,
% 7.15/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.15/1.50      | ~ v1_xboole_0(X2)
% 7.15/1.50      | v1_xboole_0(X0) ),
% 7.15/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1461,plain,
% 7.15/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.15/1.50      | v1_xboole_0(X2) != iProver_top
% 7.15/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_5216,plain,
% 7.15/1.50      ( v1_xboole_0(k1_relat_1(sK2)) != iProver_top
% 7.15/1.50      | v1_xboole_0(k2_funct_1(sK2)) = iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_3973,c_1461]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_5915,plain,
% 7.15/1.50      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 7.15/1.50      | v1_xboole_0(k2_funct_1(sK2)) = iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_4489,c_5216]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_5920,plain,
% 7.15/1.50      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 7.15/1.50      | k2_funct_1(sK2) = k1_xboole_0 ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_5915,c_1467]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_6953,plain,
% 7.15/1.50      ( k2_funct_1(sK2) = k1_xboole_0
% 7.15/1.50      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_5920,c_5435]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_8203,plain,
% 7.15/1.50      ( k2_funct_1(sK2) = k1_xboole_0 ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_6953,c_7805]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_8208,plain,
% 7.15/1.50      ( k1_relat_1(sK2) = k2_relat_1(k1_xboole_0) ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_8203,c_7805]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_12682,plain,
% 7.15/1.50      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_7816,c_8208]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_9719,plain,
% 7.15/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(k1_xboole_0),k2_relat_1(sK2)))) = iProver_top ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_8208,c_3976]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_12697,plain,
% 7.15/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)))) = iProver_top ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_12682,c_9719]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_5,plain,
% 7.15/1.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.15/1.50      inference(cnf_transformation,[],[f106]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_12723,plain,
% 7.15/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_12697,c_5]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_2924,plain,
% 7.15/1.50      ( k2_relset_1(k1_xboole_0,X0,X1) = k2_relat_1(X1)
% 7.15/1.50      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_5,c_1457]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_13160,plain,
% 7.15/1.50      ( k2_relset_1(k1_xboole_0,X0,sK2) = k2_relat_1(sK2) ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_12723,c_2924]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_8218,plain,
% 7.15/1.50      ( k1_relat_1(k1_xboole_0) = k2_relat_1(sK2)
% 7.15/1.50      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_8203,c_5915]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3975,plain,
% 7.15/1.50      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_3969,c_3804]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_15,plain,
% 7.15/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.15/1.50      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 7.15/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1460,plain,
% 7.15/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.15/1.50      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_5342,plain,
% 7.15/1.50      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 7.15/1.50      | m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(k1_relat_1(sK2))) = iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_3975,c_1460]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_6767,plain,
% 7.15/1.50      ( m1_subset_1(k2_relat_1(k2_funct_1(sK2)),k1_zfmisc_1(k1_relat_1(sK2))) = iProver_top ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_5342,c_3973]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_7807,plain,
% 7.15/1.50      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_relat_1(sK2))) = iProver_top ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_7805,c_6767]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_7822,plain,
% 7.15/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.15/1.50      inference(light_normalisation,[status(thm)],[c_7807,c_7816]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_7810,plain,
% 7.15/1.50      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_7805,c_3975]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_7818,plain,
% 7.15/1.50      ( k2_relset_1(k2_relat_1(sK2),k1_xboole_0,k2_funct_1(sK2)) = k1_xboole_0 ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_7816,c_7810]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4946,plain,
% 7.15/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.15/1.50      | v1_xboole_0(X1) != iProver_top
% 7.15/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_5,c_1461]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4976,plain,
% 7.15/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top
% 7.15/1.50      | v1_xboole_0(X2) != iProver_top
% 7.15/1.50      | v1_xboole_0(k2_relset_1(X1,k1_xboole_0,X0)) = iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_1460,c_4946]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4,plain,
% 7.15/1.50      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.15/1.50      inference(cnf_transformation,[],[f105]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_4994,plain,
% 7.15/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.15/1.50      | v1_xboole_0(X1) != iProver_top
% 7.15/1.50      | v1_xboole_0(k2_relset_1(X2,k1_xboole_0,X0)) = iProver_top ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_4976,c_4]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_6280,plain,
% 7.15/1.50      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 7.15/1.50      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.15/1.50      | v1_xboole_0(k2_relset_1(X1,k1_xboole_0,X0)) = iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_4489,c_4994]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_7865,plain,
% 7.15/1.50      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 7.15/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.15/1.50      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_7818,c_6280]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_7874,plain,
% 7.15/1.50      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.15/1.50      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_7865,c_5435,c_7805]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_8206,plain,
% 7.15/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.15/1.50      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_8203,c_7874]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_9245,plain,
% 7.15/1.50      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_8218,c_7822,c_8206]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_9251,plain,
% 7.15/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.15/1.50      | v1_xboole_0(k2_relset_1(X1,k1_xboole_0,X0)) = iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_9245,c_4994]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_18133,plain,
% 7.15/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.15/1.50      | v1_xboole_0(k2_relat_1(sK2)) = iProver_top ),
% 7.15/1.50      inference(superposition,[status(thm)],[c_13160,c_9251]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_383,plain,
% 7.15/1.50      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 7.15/1.50      inference(resolution_lifted,[status(thm)],[c_28,c_37]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_384,plain,
% 7.15/1.50      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 7.15/1.50      inference(unflattening,[status(thm)],[c_383]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_50,plain,
% 7.15/1.50      ( v2_struct_0(sK1)
% 7.15/1.50      | ~ l1_struct_0(sK1)
% 7.15/1.50      | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 7.15/1.50      inference(instantiation,[status(thm)],[c_28]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_386,plain,
% 7.15/1.50      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 7.15/1.50      inference(global_propositional_subsumption,
% 7.15/1.50                [status(thm)],
% 7.15/1.50                [c_384,c_37,c_36,c_50]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_1452,plain,
% 7.15/1.50      ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
% 7.15/1.50      inference(predicate_to_equality,[status(thm)],[c_386]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(c_3061,plain,
% 7.15/1.50      ( v1_xboole_0(k2_relat_1(sK2)) != iProver_top ),
% 7.15/1.50      inference(demodulation,[status(thm)],[c_3046,c_1452]) ).
% 7.15/1.50  
% 7.15/1.50  cnf(contradiction,plain,
% 7.15/1.50      ( $false ),
% 7.15/1.50      inference(minisat,[status(thm)],[c_18133,c_12723,c_3061]) ).
% 7.15/1.50  
% 7.15/1.50  
% 7.15/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.15/1.50  
% 7.15/1.50  ------                               Statistics
% 7.15/1.50  
% 7.15/1.50  ------ General
% 7.15/1.50  
% 7.15/1.50  abstr_ref_over_cycles:                  0
% 7.15/1.50  abstr_ref_under_cycles:                 0
% 7.15/1.50  gc_basic_clause_elim:                   0
% 7.15/1.50  forced_gc_time:                         0
% 7.15/1.50  parsing_time:                           0.019
% 7.15/1.50  unif_index_cands_time:                  0.
% 7.15/1.50  unif_index_add_time:                    0.
% 7.15/1.50  orderings_time:                         0.
% 7.15/1.50  out_proof_time:                         0.025
% 7.15/1.50  total_time:                             0.772
% 7.15/1.50  num_of_symbols:                         60
% 7.15/1.50  num_of_terms:                           15667
% 7.15/1.50  
% 7.15/1.50  ------ Preprocessing
% 7.15/1.50  
% 7.15/1.50  num_of_splits:                          0
% 7.15/1.50  num_of_split_atoms:                     0
% 7.15/1.50  num_of_reused_defs:                     0
% 7.15/1.50  num_eq_ax_congr_red:                    23
% 7.15/1.50  num_of_sem_filtered_clauses:            1
% 7.15/1.50  num_of_subtypes:                        0
% 7.15/1.50  monotx_restored_types:                  0
% 7.15/1.50  sat_num_of_epr_types:                   0
% 7.15/1.50  sat_num_of_non_cyclic_types:            0
% 7.15/1.50  sat_guarded_non_collapsed_types:        0
% 7.15/1.50  num_pure_diseq_elim:                    0
% 7.15/1.50  simp_replaced_by:                       0
% 7.15/1.50  res_preprocessed:                       171
% 7.15/1.50  prep_upred:                             0
% 7.15/1.50  prep_unflattend:                        17
% 7.15/1.50  smt_new_axioms:                         0
% 7.15/1.50  pred_elim_cands:                        6
% 7.15/1.50  pred_elim:                              5
% 7.15/1.50  pred_elim_cl:                           6
% 7.15/1.50  pred_elim_cycles:                       8
% 7.15/1.50  merged_defs:                            0
% 7.15/1.50  merged_defs_ncl:                        0
% 7.15/1.50  bin_hyper_res:                          0
% 7.15/1.50  prep_cycles:                            4
% 7.15/1.50  pred_elim_time:                         0.01
% 7.15/1.50  splitting_time:                         0.
% 7.15/1.50  sem_filter_time:                        0.
% 7.15/1.50  monotx_time:                            0.
% 7.15/1.50  subtype_inf_time:                       0.
% 7.15/1.50  
% 7.15/1.50  ------ Problem properties
% 7.15/1.50  
% 7.15/1.50  clauses:                                31
% 7.15/1.50  conjectures:                            5
% 7.15/1.50  epr:                                    4
% 7.15/1.50  horn:                                   29
% 7.15/1.50  ground:                                 9
% 7.15/1.50  unary:                                  11
% 7.15/1.50  binary:                                 9
% 7.15/1.50  lits:                                   69
% 7.15/1.50  lits_eq:                                25
% 7.15/1.50  fd_pure:                                0
% 7.15/1.50  fd_pseudo:                              0
% 7.15/1.50  fd_cond:                                2
% 7.15/1.50  fd_pseudo_cond:                         2
% 7.15/1.50  ac_symbols:                             0
% 7.15/1.50  
% 7.15/1.50  ------ Propositional Solver
% 7.15/1.50  
% 7.15/1.50  prop_solver_calls:                      32
% 7.15/1.50  prop_fast_solver_calls:                 1539
% 7.15/1.50  smt_solver_calls:                       0
% 7.15/1.50  smt_fast_solver_calls:                  0
% 7.15/1.50  prop_num_of_clauses:                    7177
% 7.15/1.50  prop_preprocess_simplified:             12693
% 7.15/1.50  prop_fo_subsumed:                       64
% 7.15/1.50  prop_solver_time:                       0.
% 7.15/1.50  smt_solver_time:                        0.
% 7.15/1.50  smt_fast_solver_time:                   0.
% 7.15/1.50  prop_fast_solver_time:                  0.
% 7.15/1.50  prop_unsat_core_time:                   0.001
% 7.15/1.50  
% 7.15/1.50  ------ QBF
% 7.15/1.50  
% 7.15/1.50  qbf_q_res:                              0
% 7.15/1.50  qbf_num_tautologies:                    0
% 7.15/1.50  qbf_prep_cycles:                        0
% 7.15/1.50  
% 7.15/1.50  ------ BMC1
% 7.15/1.50  
% 7.15/1.50  bmc1_current_bound:                     -1
% 7.15/1.50  bmc1_last_solved_bound:                 -1
% 7.15/1.50  bmc1_unsat_core_size:                   -1
% 7.15/1.50  bmc1_unsat_core_parents_size:           -1
% 7.15/1.50  bmc1_merge_next_fun:                    0
% 7.15/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.15/1.50  
% 7.15/1.50  ------ Instantiation
% 7.15/1.50  
% 7.15/1.50  inst_num_of_clauses:                    2399
% 7.15/1.50  inst_num_in_passive:                    534
% 7.15/1.50  inst_num_in_active:                     1195
% 7.15/1.50  inst_num_in_unprocessed:                671
% 7.15/1.50  inst_num_of_loops:                      1280
% 7.15/1.50  inst_num_of_learning_restarts:          0
% 7.15/1.50  inst_num_moves_active_passive:          76
% 7.15/1.50  inst_lit_activity:                      0
% 7.15/1.50  inst_lit_activity_moves:                0
% 7.15/1.50  inst_num_tautologies:                   0
% 7.15/1.50  inst_num_prop_implied:                  0
% 7.15/1.50  inst_num_existing_simplified:           0
% 7.15/1.50  inst_num_eq_res_simplified:             0
% 7.15/1.50  inst_num_child_elim:                    0
% 7.15/1.50  inst_num_of_dismatching_blockings:      600
% 7.15/1.50  inst_num_of_non_proper_insts:           2849
% 7.15/1.50  inst_num_of_duplicates:                 0
% 7.15/1.50  inst_inst_num_from_inst_to_res:         0
% 7.15/1.50  inst_dismatching_checking_time:         0.
% 7.15/1.50  
% 7.15/1.50  ------ Resolution
% 7.15/1.50  
% 7.15/1.50  res_num_of_clauses:                     0
% 7.15/1.50  res_num_in_passive:                     0
% 7.15/1.50  res_num_in_active:                      0
% 7.15/1.50  res_num_of_loops:                       175
% 7.15/1.50  res_forward_subset_subsumed:            442
% 7.15/1.50  res_backward_subset_subsumed:           12
% 7.15/1.50  res_forward_subsumed:                   0
% 7.15/1.50  res_backward_subsumed:                  0
% 7.15/1.50  res_forward_subsumption_resolution:     0
% 7.15/1.50  res_backward_subsumption_resolution:    0
% 7.15/1.50  res_clause_to_clause_subsumption:       3385
% 7.15/1.50  res_orphan_elimination:                 0
% 7.15/1.50  res_tautology_del:                      317
% 7.15/1.50  res_num_eq_res_simplified:              0
% 7.15/1.50  res_num_sel_changes:                    0
% 7.15/1.50  res_moves_from_active_to_pass:          0
% 7.15/1.50  
% 7.15/1.50  ------ Superposition
% 7.15/1.50  
% 7.15/1.50  sup_time_total:                         0.
% 7.15/1.50  sup_time_generating:                    0.
% 7.15/1.50  sup_time_sim_full:                      0.
% 7.15/1.50  sup_time_sim_immed:                     0.
% 7.15/1.50  
% 7.15/1.50  sup_num_of_clauses:                     500
% 7.15/1.50  sup_num_in_active:                      162
% 7.15/1.50  sup_num_in_passive:                     338
% 7.15/1.50  sup_num_of_loops:                       254
% 7.15/1.50  sup_fw_superposition:                   358
% 7.15/1.50  sup_bw_superposition:                   357
% 7.15/1.50  sup_immediate_simplified:               439
% 7.15/1.50  sup_given_eliminated:                   1
% 7.15/1.50  comparisons_done:                       0
% 7.15/1.50  comparisons_avoided:                    12
% 7.15/1.50  
% 7.15/1.50  ------ Simplifications
% 7.15/1.50  
% 7.15/1.50  
% 7.15/1.50  sim_fw_subset_subsumed:                 48
% 7.15/1.50  sim_bw_subset_subsumed:                 4
% 7.15/1.50  sim_fw_subsumed:                        14
% 7.15/1.50  sim_bw_subsumed:                        2
% 7.15/1.50  sim_fw_subsumption_res:                 3
% 7.15/1.50  sim_bw_subsumption_res:                 0
% 7.15/1.50  sim_tautology_del:                      3
% 7.15/1.50  sim_eq_tautology_del:                   24
% 7.15/1.50  sim_eq_res_simp:                        2
% 7.15/1.50  sim_fw_demodulated:                     104
% 7.15/1.50  sim_bw_demodulated:                     308
% 7.15/1.50  sim_light_normalised:                   94
% 7.15/1.50  sim_joinable_taut:                      0
% 7.15/1.50  sim_joinable_simp:                      0
% 7.15/1.50  sim_ac_normalised:                      0
% 7.15/1.50  sim_smt_subsumption:                    0
% 7.15/1.50  
%------------------------------------------------------------------------------
