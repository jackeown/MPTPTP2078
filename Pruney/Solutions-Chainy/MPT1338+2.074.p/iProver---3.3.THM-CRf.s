%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:15 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :  185 (2977 expanded)
%              Number of clauses        :  118 ( 928 expanded)
%              Number of leaves         :   18 ( 838 expanded)
%              Depth                    :   28
%              Number of atoms          :  539 (20626 expanded)
%              Number of equality atoms :  210 (6789 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f43,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f42,f41,f40])).

fof(f65,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f48,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(X0) = k4_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f46,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k4_relat_1(X2) = k3_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_relat_1(X2) = k3_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k4_relat_1(X2) = k3_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_13,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_15,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_271,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_272,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_271])).

cnf(c_23,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_37,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_274,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_272,c_24,c_23,c_37])).

cnf(c_296,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_274])).

cnf(c_297,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_296])).

cnf(c_369,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK0) != X1
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_297])).

cnf(c_370,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_14,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_40,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_372,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_370,c_23,c_22,c_40])).

cnf(c_441,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_relat_1(X0)
    | u1_struct_0(sK0) != X1
    | k1_relat_1(X0) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_372])).

cnf(c_442,plain,
    ( ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_5,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_452,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_442,c_5])).

cnf(c_550,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_452])).

cnf(c_812,plain,
    ( k1_relat_1(sK2) = u1_struct_0(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_550])).

cnf(c_25,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_289,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_290,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_289])).

cnf(c_555,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_290])).

cnf(c_863,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_812,c_555])).

cnf(c_864,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_863,c_555])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_557,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_808,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_557])).

cnf(c_284,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_285,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_284])).

cnf(c_556,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_285])).

cnf(c_822,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_808,c_555,c_556])).

cnf(c_868,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_864,c_822])).

cnf(c_876,plain,
    ( ~ v1_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_868])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_565,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ v1_relat_1(X1_53)
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_902,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | v1_relat_1(X0_53)
    | ~ v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) ),
    inference(instantiation,[status(thm)],[c_565])).

cnf(c_980,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_902])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_564,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_992,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_1723,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_868,c_20,c_876,c_980,c_992])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_561,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k2_relset_1(X0_55,X1_55,X0_53) = k2_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_806,plain,
    ( k2_relset_1(X0_55,X1_55,X0_53) = k2_relat_1(X0_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_561])).

cnf(c_1066,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_822,c_806])).

cnf(c_19,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_558,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_819,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_558,c_555,c_556])).

cnf(c_1158,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1066,c_819])).

cnf(c_1194,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1158,c_822])).

cnf(c_1726,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1723,c_1194])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_563,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | m1_subset_1(k3_relset_1(X0_55,X1_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_804,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(k3_relset_1(X0_55,X1_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_563])).

cnf(c_1289,plain,
    ( k2_relset_1(X0_55,X1_55,k3_relset_1(X1_55,X0_55,X0_53)) = k2_relat_1(k3_relset_1(X1_55,X0_55,X0_53))
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) != iProver_top ),
    inference(superposition,[status(thm)],[c_804,c_806])).

cnf(c_2233,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k3_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) = k2_relat_1(k3_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) ),
    inference(superposition,[status(thm)],[c_1726,c_1289])).

cnf(c_802,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
    | v1_relat_1(X1_53) != iProver_top
    | v1_relat_1(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_565])).

cnf(c_1020,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_822,c_802])).

cnf(c_31,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_981,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_980])).

cnf(c_993,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_992])).

cnf(c_1354,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1020,c_31,c_981,c_993])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_18,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_402,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_18])).

cnf(c_403,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_405,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_403,c_22])).

cnf(c_552,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_405])).

cnf(c_810,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_552])).

cnf(c_1359,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1354,c_810])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k4_relat_1(X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_416,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k4_relat_1(X0) = k2_funct_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_18])).

cnf(c_417,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k4_relat_1(sK2) = k2_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_419,plain,
    ( ~ v1_relat_1(sK2)
    | k4_relat_1(sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_417,c_22])).

cnf(c_551,plain,
    ( ~ v1_relat_1(sK2)
    | k4_relat_1(sK2) = k2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_419])).

cnf(c_811,plain,
    ( k4_relat_1(sK2) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_551])).

cnf(c_1361,plain,
    ( k4_relat_1(sK2) = k2_funct_1(sK2) ),
    inference(superposition,[status(thm)],[c_1354,c_811])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_560,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k3_relset_1(X0_55,X1_55,X0_53) = k4_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_807,plain,
    ( k3_relset_1(X0_55,X1_55,X0_53) = k4_relat_1(X0_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_560])).

cnf(c_1116,plain,
    ( k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_822,c_807])).

cnf(c_1244,plain,
    ( k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k4_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1116,c_1158])).

cnf(c_1506,plain,
    ( k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1361,c_1244])).

cnf(c_2060,plain,
    ( k3_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1506,c_1723])).

cnf(c_2239,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2233,c_1359,c_2060])).

cnf(c_1287,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_804])).

cnf(c_1369,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1287,c_1194])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_562,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k1_relset_1(X0_55,X1_55,X0_53) = k1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_805,plain,
    ( k1_relset_1(X0_55,X1_55,X0_53) = k1_relat_1(X0_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_562])).

cnf(c_1376,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_1369,c_805])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_388,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_18])).

cnf(c_389,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_391,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_389,c_22])).

cnf(c_553,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_391])).

cnf(c_809,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_553])).

cnf(c_1360,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1354,c_809])).

cnf(c_1846,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1376,c_1360,c_1361,c_1723])).

cnf(c_17,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_559,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_358,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | u1_struct_0(sK0) != X1
    | u1_struct_0(sK1) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_359,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_361,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_359,c_22,c_20,c_18])).

cnf(c_554,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_361])).

cnf(c_855,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_554,c_555,c_556,c_819])).

cnf(c_856,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_855])).

cnf(c_871,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_559,c_555,c_556,c_856])).

cnf(c_1195,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1158,c_871])).

cnf(c_1730,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2)
    | k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1723,c_1195])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2239,c_1846,c_1730])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:54:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.61/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.01  
% 2.61/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.61/1.01  
% 2.61/1.01  ------  iProver source info
% 2.61/1.01  
% 2.61/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.61/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.61/1.01  git: non_committed_changes: false
% 2.61/1.01  git: last_make_outside_of_git: false
% 2.61/1.01  
% 2.61/1.01  ------ 
% 2.61/1.01  
% 2.61/1.01  ------ Input Options
% 2.61/1.01  
% 2.61/1.01  --out_options                           all
% 2.61/1.01  --tptp_safe_out                         true
% 2.61/1.01  --problem_path                          ""
% 2.61/1.01  --include_path                          ""
% 2.61/1.01  --clausifier                            res/vclausify_rel
% 2.61/1.01  --clausifier_options                    --mode clausify
% 2.61/1.01  --stdin                                 false
% 2.61/1.01  --stats_out                             all
% 2.61/1.01  
% 2.61/1.01  ------ General Options
% 2.61/1.01  
% 2.61/1.01  --fof                                   false
% 2.61/1.01  --time_out_real                         305.
% 2.61/1.01  --time_out_virtual                      -1.
% 2.61/1.01  --symbol_type_check                     false
% 2.61/1.01  --clausify_out                          false
% 2.61/1.01  --sig_cnt_out                           false
% 2.61/1.01  --trig_cnt_out                          false
% 2.61/1.01  --trig_cnt_out_tolerance                1.
% 2.61/1.01  --trig_cnt_out_sk_spl                   false
% 2.61/1.01  --abstr_cl_out                          false
% 2.61/1.01  
% 2.61/1.01  ------ Global Options
% 2.61/1.01  
% 2.61/1.01  --schedule                              default
% 2.61/1.01  --add_important_lit                     false
% 2.61/1.01  --prop_solver_per_cl                    1000
% 2.61/1.01  --min_unsat_core                        false
% 2.61/1.01  --soft_assumptions                      false
% 2.61/1.01  --soft_lemma_size                       3
% 2.61/1.01  --prop_impl_unit_size                   0
% 2.61/1.01  --prop_impl_unit                        []
% 2.61/1.01  --share_sel_clauses                     true
% 2.61/1.01  --reset_solvers                         false
% 2.61/1.01  --bc_imp_inh                            [conj_cone]
% 2.61/1.01  --conj_cone_tolerance                   3.
% 2.61/1.01  --extra_neg_conj                        none
% 2.61/1.01  --large_theory_mode                     true
% 2.61/1.01  --prolific_symb_bound                   200
% 2.61/1.01  --lt_threshold                          2000
% 2.61/1.01  --clause_weak_htbl                      true
% 2.61/1.01  --gc_record_bc_elim                     false
% 2.61/1.01  
% 2.61/1.01  ------ Preprocessing Options
% 2.61/1.01  
% 2.61/1.01  --preprocessing_flag                    true
% 2.61/1.01  --time_out_prep_mult                    0.1
% 2.61/1.01  --splitting_mode                        input
% 2.61/1.01  --splitting_grd                         true
% 2.61/1.01  --splitting_cvd                         false
% 2.61/1.01  --splitting_cvd_svl                     false
% 2.61/1.01  --splitting_nvd                         32
% 2.61/1.01  --sub_typing                            true
% 2.61/1.01  --prep_gs_sim                           true
% 2.61/1.01  --prep_unflatten                        true
% 2.61/1.01  --prep_res_sim                          true
% 2.61/1.01  --prep_upred                            true
% 2.61/1.01  --prep_sem_filter                       exhaustive
% 2.61/1.01  --prep_sem_filter_out                   false
% 2.61/1.01  --pred_elim                             true
% 2.61/1.01  --res_sim_input                         true
% 2.61/1.01  --eq_ax_congr_red                       true
% 2.61/1.01  --pure_diseq_elim                       true
% 2.61/1.01  --brand_transform                       false
% 2.61/1.01  --non_eq_to_eq                          false
% 2.61/1.01  --prep_def_merge                        true
% 2.61/1.01  --prep_def_merge_prop_impl              false
% 2.61/1.01  --prep_def_merge_mbd                    true
% 2.61/1.01  --prep_def_merge_tr_red                 false
% 2.61/1.01  --prep_def_merge_tr_cl                  false
% 2.61/1.01  --smt_preprocessing                     true
% 2.61/1.01  --smt_ac_axioms                         fast
% 2.61/1.01  --preprocessed_out                      false
% 2.61/1.01  --preprocessed_stats                    false
% 2.61/1.01  
% 2.61/1.01  ------ Abstraction refinement Options
% 2.61/1.01  
% 2.61/1.01  --abstr_ref                             []
% 2.61/1.01  --abstr_ref_prep                        false
% 2.61/1.01  --abstr_ref_until_sat                   false
% 2.61/1.01  --abstr_ref_sig_restrict                funpre
% 2.61/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.61/1.01  --abstr_ref_under                       []
% 2.61/1.01  
% 2.61/1.01  ------ SAT Options
% 2.61/1.01  
% 2.61/1.01  --sat_mode                              false
% 2.61/1.01  --sat_fm_restart_options                ""
% 2.61/1.01  --sat_gr_def                            false
% 2.61/1.01  --sat_epr_types                         true
% 2.61/1.01  --sat_non_cyclic_types                  false
% 2.61/1.01  --sat_finite_models                     false
% 2.61/1.01  --sat_fm_lemmas                         false
% 2.61/1.01  --sat_fm_prep                           false
% 2.61/1.01  --sat_fm_uc_incr                        true
% 2.61/1.01  --sat_out_model                         small
% 2.61/1.01  --sat_out_clauses                       false
% 2.61/1.01  
% 2.61/1.01  ------ QBF Options
% 2.61/1.01  
% 2.61/1.01  --qbf_mode                              false
% 2.61/1.01  --qbf_elim_univ                         false
% 2.61/1.01  --qbf_dom_inst                          none
% 2.61/1.01  --qbf_dom_pre_inst                      false
% 2.61/1.01  --qbf_sk_in                             false
% 2.61/1.01  --qbf_pred_elim                         true
% 2.61/1.01  --qbf_split                             512
% 2.61/1.01  
% 2.61/1.01  ------ BMC1 Options
% 2.61/1.01  
% 2.61/1.01  --bmc1_incremental                      false
% 2.61/1.01  --bmc1_axioms                           reachable_all
% 2.61/1.01  --bmc1_min_bound                        0
% 2.61/1.01  --bmc1_max_bound                        -1
% 2.61/1.01  --bmc1_max_bound_default                -1
% 2.61/1.01  --bmc1_symbol_reachability              true
% 2.61/1.01  --bmc1_property_lemmas                  false
% 2.61/1.01  --bmc1_k_induction                      false
% 2.61/1.01  --bmc1_non_equiv_states                 false
% 2.61/1.01  --bmc1_deadlock                         false
% 2.61/1.01  --bmc1_ucm                              false
% 2.61/1.01  --bmc1_add_unsat_core                   none
% 2.61/1.01  --bmc1_unsat_core_children              false
% 2.61/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.61/1.01  --bmc1_out_stat                         full
% 2.61/1.01  --bmc1_ground_init                      false
% 2.61/1.01  --bmc1_pre_inst_next_state              false
% 2.61/1.01  --bmc1_pre_inst_state                   false
% 2.61/1.01  --bmc1_pre_inst_reach_state             false
% 2.61/1.01  --bmc1_out_unsat_core                   false
% 2.61/1.01  --bmc1_aig_witness_out                  false
% 2.61/1.01  --bmc1_verbose                          false
% 2.61/1.01  --bmc1_dump_clauses_tptp                false
% 2.61/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.61/1.01  --bmc1_dump_file                        -
% 2.61/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.61/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.61/1.01  --bmc1_ucm_extend_mode                  1
% 2.61/1.01  --bmc1_ucm_init_mode                    2
% 2.61/1.01  --bmc1_ucm_cone_mode                    none
% 2.61/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.61/1.01  --bmc1_ucm_relax_model                  4
% 2.61/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.61/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.61/1.01  --bmc1_ucm_layered_model                none
% 2.61/1.01  --bmc1_ucm_max_lemma_size               10
% 2.61/1.01  
% 2.61/1.01  ------ AIG Options
% 2.61/1.01  
% 2.61/1.01  --aig_mode                              false
% 2.61/1.01  
% 2.61/1.01  ------ Instantiation Options
% 2.61/1.01  
% 2.61/1.01  --instantiation_flag                    true
% 2.61/1.01  --inst_sos_flag                         false
% 2.61/1.01  --inst_sos_phase                        true
% 2.61/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.61/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.61/1.01  --inst_lit_sel_side                     num_symb
% 2.61/1.01  --inst_solver_per_active                1400
% 2.61/1.01  --inst_solver_calls_frac                1.
% 2.61/1.01  --inst_passive_queue_type               priority_queues
% 2.61/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.61/1.01  --inst_passive_queues_freq              [25;2]
% 2.61/1.01  --inst_dismatching                      true
% 2.61/1.01  --inst_eager_unprocessed_to_passive     true
% 2.61/1.01  --inst_prop_sim_given                   true
% 2.61/1.01  --inst_prop_sim_new                     false
% 2.61/1.01  --inst_subs_new                         false
% 2.61/1.01  --inst_eq_res_simp                      false
% 2.61/1.01  --inst_subs_given                       false
% 2.61/1.01  --inst_orphan_elimination               true
% 2.61/1.01  --inst_learning_loop_flag               true
% 2.61/1.01  --inst_learning_start                   3000
% 2.61/1.01  --inst_learning_factor                  2
% 2.61/1.01  --inst_start_prop_sim_after_learn       3
% 2.61/1.01  --inst_sel_renew                        solver
% 2.61/1.01  --inst_lit_activity_flag                true
% 2.61/1.01  --inst_restr_to_given                   false
% 2.61/1.01  --inst_activity_threshold               500
% 2.61/1.01  --inst_out_proof                        true
% 2.61/1.01  
% 2.61/1.01  ------ Resolution Options
% 2.61/1.01  
% 2.61/1.01  --resolution_flag                       true
% 2.61/1.01  --res_lit_sel                           adaptive
% 2.61/1.01  --res_lit_sel_side                      none
% 2.61/1.01  --res_ordering                          kbo
% 2.61/1.01  --res_to_prop_solver                    active
% 2.61/1.01  --res_prop_simpl_new                    false
% 2.61/1.01  --res_prop_simpl_given                  true
% 2.61/1.01  --res_passive_queue_type                priority_queues
% 2.61/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.61/1.01  --res_passive_queues_freq               [15;5]
% 2.61/1.01  --res_forward_subs                      full
% 2.61/1.01  --res_backward_subs                     full
% 2.61/1.01  --res_forward_subs_resolution           true
% 2.61/1.01  --res_backward_subs_resolution          true
% 2.61/1.01  --res_orphan_elimination                true
% 2.61/1.01  --res_time_limit                        2.
% 2.61/1.01  --res_out_proof                         true
% 2.61/1.01  
% 2.61/1.01  ------ Superposition Options
% 2.61/1.01  
% 2.61/1.01  --superposition_flag                    true
% 2.61/1.01  --sup_passive_queue_type                priority_queues
% 2.61/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.61/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.61/1.01  --demod_completeness_check              fast
% 2.61/1.01  --demod_use_ground                      true
% 2.61/1.01  --sup_to_prop_solver                    passive
% 2.61/1.01  --sup_prop_simpl_new                    true
% 2.61/1.01  --sup_prop_simpl_given                  true
% 2.61/1.01  --sup_fun_splitting                     false
% 2.61/1.01  --sup_smt_interval                      50000
% 2.61/1.01  
% 2.61/1.01  ------ Superposition Simplification Setup
% 2.61/1.01  
% 2.61/1.01  --sup_indices_passive                   []
% 2.61/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.61/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/1.01  --sup_full_bw                           [BwDemod]
% 2.61/1.01  --sup_immed_triv                        [TrivRules]
% 2.61/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.61/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/1.01  --sup_immed_bw_main                     []
% 2.61/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.61/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.61/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.61/1.01  
% 2.61/1.01  ------ Combination Options
% 2.61/1.01  
% 2.61/1.01  --comb_res_mult                         3
% 2.61/1.01  --comb_sup_mult                         2
% 2.61/1.01  --comb_inst_mult                        10
% 2.61/1.01  
% 2.61/1.01  ------ Debug Options
% 2.61/1.01  
% 2.61/1.01  --dbg_backtrace                         false
% 2.61/1.01  --dbg_dump_prop_clauses                 false
% 2.61/1.01  --dbg_dump_prop_clauses_file            -
% 2.61/1.01  --dbg_out_stat                          false
% 2.61/1.01  ------ Parsing...
% 2.61/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.61/1.01  
% 2.61/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 2.61/1.01  
% 2.61/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.61/1.01  
% 2.61/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.61/1.01  ------ Proving...
% 2.61/1.01  ------ Problem Properties 
% 2.61/1.01  
% 2.61/1.01  
% 2.61/1.01  clauses                                 16
% 2.61/1.01  conjectures                             3
% 2.61/1.01  EPR                                     0
% 2.61/1.01  Horn                                    16
% 2.61/1.01  unary                                   5
% 2.61/1.01  binary                                  9
% 2.61/1.01  lits                                    29
% 2.61/1.01  lits eq                                 14
% 2.61/1.01  fd_pure                                 0
% 2.61/1.01  fd_pseudo                               0
% 2.61/1.01  fd_cond                                 0
% 2.61/1.01  fd_pseudo_cond                          0
% 2.61/1.01  AC symbols                              0
% 2.61/1.01  
% 2.61/1.01  ------ Schedule dynamic 5 is on 
% 2.61/1.01  
% 2.61/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.61/1.01  
% 2.61/1.01  
% 2.61/1.01  ------ 
% 2.61/1.01  Current options:
% 2.61/1.01  ------ 
% 2.61/1.01  
% 2.61/1.01  ------ Input Options
% 2.61/1.01  
% 2.61/1.01  --out_options                           all
% 2.61/1.01  --tptp_safe_out                         true
% 2.61/1.01  --problem_path                          ""
% 2.61/1.01  --include_path                          ""
% 2.61/1.01  --clausifier                            res/vclausify_rel
% 2.61/1.01  --clausifier_options                    --mode clausify
% 2.61/1.01  --stdin                                 false
% 2.61/1.01  --stats_out                             all
% 2.61/1.01  
% 2.61/1.01  ------ General Options
% 2.61/1.01  
% 2.61/1.01  --fof                                   false
% 2.61/1.01  --time_out_real                         305.
% 2.61/1.01  --time_out_virtual                      -1.
% 2.61/1.01  --symbol_type_check                     false
% 2.61/1.01  --clausify_out                          false
% 2.61/1.01  --sig_cnt_out                           false
% 2.61/1.01  --trig_cnt_out                          false
% 2.61/1.01  --trig_cnt_out_tolerance                1.
% 2.61/1.01  --trig_cnt_out_sk_spl                   false
% 2.61/1.01  --abstr_cl_out                          false
% 2.61/1.01  
% 2.61/1.01  ------ Global Options
% 2.61/1.01  
% 2.61/1.01  --schedule                              default
% 2.61/1.01  --add_important_lit                     false
% 2.61/1.01  --prop_solver_per_cl                    1000
% 2.61/1.01  --min_unsat_core                        false
% 2.61/1.01  --soft_assumptions                      false
% 2.61/1.01  --soft_lemma_size                       3
% 2.61/1.01  --prop_impl_unit_size                   0
% 2.61/1.01  --prop_impl_unit                        []
% 2.61/1.01  --share_sel_clauses                     true
% 2.61/1.01  --reset_solvers                         false
% 2.61/1.01  --bc_imp_inh                            [conj_cone]
% 2.61/1.01  --conj_cone_tolerance                   3.
% 2.61/1.01  --extra_neg_conj                        none
% 2.61/1.01  --large_theory_mode                     true
% 2.61/1.01  --prolific_symb_bound                   200
% 2.61/1.01  --lt_threshold                          2000
% 2.61/1.01  --clause_weak_htbl                      true
% 2.61/1.01  --gc_record_bc_elim                     false
% 2.61/1.01  
% 2.61/1.01  ------ Preprocessing Options
% 2.61/1.01  
% 2.61/1.01  --preprocessing_flag                    true
% 2.61/1.01  --time_out_prep_mult                    0.1
% 2.61/1.01  --splitting_mode                        input
% 2.61/1.01  --splitting_grd                         true
% 2.61/1.01  --splitting_cvd                         false
% 2.61/1.01  --splitting_cvd_svl                     false
% 2.61/1.01  --splitting_nvd                         32
% 2.61/1.01  --sub_typing                            true
% 2.61/1.01  --prep_gs_sim                           true
% 2.61/1.01  --prep_unflatten                        true
% 2.61/1.01  --prep_res_sim                          true
% 2.61/1.01  --prep_upred                            true
% 2.61/1.01  --prep_sem_filter                       exhaustive
% 2.61/1.01  --prep_sem_filter_out                   false
% 2.61/1.01  --pred_elim                             true
% 2.61/1.01  --res_sim_input                         true
% 2.61/1.01  --eq_ax_congr_red                       true
% 2.61/1.01  --pure_diseq_elim                       true
% 2.61/1.01  --brand_transform                       false
% 2.61/1.01  --non_eq_to_eq                          false
% 2.61/1.01  --prep_def_merge                        true
% 2.61/1.01  --prep_def_merge_prop_impl              false
% 2.61/1.01  --prep_def_merge_mbd                    true
% 2.61/1.01  --prep_def_merge_tr_red                 false
% 2.61/1.01  --prep_def_merge_tr_cl                  false
% 2.61/1.01  --smt_preprocessing                     true
% 2.61/1.01  --smt_ac_axioms                         fast
% 2.61/1.01  --preprocessed_out                      false
% 2.61/1.01  --preprocessed_stats                    false
% 2.61/1.01  
% 2.61/1.01  ------ Abstraction refinement Options
% 2.61/1.01  
% 2.61/1.01  --abstr_ref                             []
% 2.61/1.01  --abstr_ref_prep                        false
% 2.61/1.01  --abstr_ref_until_sat                   false
% 2.61/1.01  --abstr_ref_sig_restrict                funpre
% 2.61/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.61/1.01  --abstr_ref_under                       []
% 2.61/1.01  
% 2.61/1.01  ------ SAT Options
% 2.61/1.01  
% 2.61/1.01  --sat_mode                              false
% 2.61/1.01  --sat_fm_restart_options                ""
% 2.61/1.01  --sat_gr_def                            false
% 2.61/1.01  --sat_epr_types                         true
% 2.61/1.01  --sat_non_cyclic_types                  false
% 2.61/1.01  --sat_finite_models                     false
% 2.61/1.01  --sat_fm_lemmas                         false
% 2.61/1.01  --sat_fm_prep                           false
% 2.61/1.01  --sat_fm_uc_incr                        true
% 2.61/1.01  --sat_out_model                         small
% 2.61/1.01  --sat_out_clauses                       false
% 2.61/1.01  
% 2.61/1.01  ------ QBF Options
% 2.61/1.01  
% 2.61/1.01  --qbf_mode                              false
% 2.61/1.01  --qbf_elim_univ                         false
% 2.61/1.01  --qbf_dom_inst                          none
% 2.61/1.01  --qbf_dom_pre_inst                      false
% 2.61/1.01  --qbf_sk_in                             false
% 2.61/1.01  --qbf_pred_elim                         true
% 2.61/1.01  --qbf_split                             512
% 2.61/1.01  
% 2.61/1.01  ------ BMC1 Options
% 2.61/1.01  
% 2.61/1.01  --bmc1_incremental                      false
% 2.61/1.01  --bmc1_axioms                           reachable_all
% 2.61/1.01  --bmc1_min_bound                        0
% 2.61/1.01  --bmc1_max_bound                        -1
% 2.61/1.01  --bmc1_max_bound_default                -1
% 2.61/1.01  --bmc1_symbol_reachability              true
% 2.61/1.01  --bmc1_property_lemmas                  false
% 2.61/1.01  --bmc1_k_induction                      false
% 2.61/1.01  --bmc1_non_equiv_states                 false
% 2.61/1.01  --bmc1_deadlock                         false
% 2.61/1.01  --bmc1_ucm                              false
% 2.61/1.01  --bmc1_add_unsat_core                   none
% 2.61/1.01  --bmc1_unsat_core_children              false
% 2.61/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.61/1.01  --bmc1_out_stat                         full
% 2.61/1.01  --bmc1_ground_init                      false
% 2.61/1.01  --bmc1_pre_inst_next_state              false
% 2.61/1.01  --bmc1_pre_inst_state                   false
% 2.61/1.01  --bmc1_pre_inst_reach_state             false
% 2.61/1.01  --bmc1_out_unsat_core                   false
% 2.61/1.01  --bmc1_aig_witness_out                  false
% 2.61/1.01  --bmc1_verbose                          false
% 2.61/1.01  --bmc1_dump_clauses_tptp                false
% 2.61/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.61/1.01  --bmc1_dump_file                        -
% 2.61/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.61/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.61/1.01  --bmc1_ucm_extend_mode                  1
% 2.61/1.01  --bmc1_ucm_init_mode                    2
% 2.61/1.01  --bmc1_ucm_cone_mode                    none
% 2.61/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.61/1.01  --bmc1_ucm_relax_model                  4
% 2.61/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.61/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.61/1.01  --bmc1_ucm_layered_model                none
% 2.61/1.01  --bmc1_ucm_max_lemma_size               10
% 2.61/1.01  
% 2.61/1.01  ------ AIG Options
% 2.61/1.01  
% 2.61/1.01  --aig_mode                              false
% 2.61/1.01  
% 2.61/1.01  ------ Instantiation Options
% 2.61/1.01  
% 2.61/1.01  --instantiation_flag                    true
% 2.61/1.01  --inst_sos_flag                         false
% 2.61/1.01  --inst_sos_phase                        true
% 2.61/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.61/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.61/1.01  --inst_lit_sel_side                     none
% 2.61/1.01  --inst_solver_per_active                1400
% 2.61/1.01  --inst_solver_calls_frac                1.
% 2.61/1.01  --inst_passive_queue_type               priority_queues
% 2.61/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.61/1.01  --inst_passive_queues_freq              [25;2]
% 2.61/1.01  --inst_dismatching                      true
% 2.61/1.01  --inst_eager_unprocessed_to_passive     true
% 2.61/1.01  --inst_prop_sim_given                   true
% 2.61/1.01  --inst_prop_sim_new                     false
% 2.61/1.01  --inst_subs_new                         false
% 2.61/1.01  --inst_eq_res_simp                      false
% 2.61/1.01  --inst_subs_given                       false
% 2.61/1.01  --inst_orphan_elimination               true
% 2.61/1.01  --inst_learning_loop_flag               true
% 2.61/1.01  --inst_learning_start                   3000
% 2.61/1.01  --inst_learning_factor                  2
% 2.61/1.01  --inst_start_prop_sim_after_learn       3
% 2.61/1.01  --inst_sel_renew                        solver
% 2.61/1.01  --inst_lit_activity_flag                true
% 2.61/1.01  --inst_restr_to_given                   false
% 2.61/1.01  --inst_activity_threshold               500
% 2.61/1.01  --inst_out_proof                        true
% 2.61/1.01  
% 2.61/1.01  ------ Resolution Options
% 2.61/1.01  
% 2.61/1.01  --resolution_flag                       false
% 2.61/1.01  --res_lit_sel                           adaptive
% 2.61/1.01  --res_lit_sel_side                      none
% 2.61/1.01  --res_ordering                          kbo
% 2.61/1.01  --res_to_prop_solver                    active
% 2.61/1.01  --res_prop_simpl_new                    false
% 2.61/1.01  --res_prop_simpl_given                  true
% 2.61/1.01  --res_passive_queue_type                priority_queues
% 2.61/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.61/1.01  --res_passive_queues_freq               [15;5]
% 2.61/1.01  --res_forward_subs                      full
% 2.61/1.01  --res_backward_subs                     full
% 2.61/1.01  --res_forward_subs_resolution           true
% 2.61/1.01  --res_backward_subs_resolution          true
% 2.61/1.01  --res_orphan_elimination                true
% 2.61/1.01  --res_time_limit                        2.
% 2.61/1.01  --res_out_proof                         true
% 2.61/1.01  
% 2.61/1.01  ------ Superposition Options
% 2.61/1.01  
% 2.61/1.01  --superposition_flag                    true
% 2.61/1.01  --sup_passive_queue_type                priority_queues
% 2.61/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.61/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.61/1.01  --demod_completeness_check              fast
% 2.61/1.01  --demod_use_ground                      true
% 2.61/1.01  --sup_to_prop_solver                    passive
% 2.61/1.01  --sup_prop_simpl_new                    true
% 2.61/1.01  --sup_prop_simpl_given                  true
% 2.61/1.01  --sup_fun_splitting                     false
% 2.61/1.01  --sup_smt_interval                      50000
% 2.61/1.01  
% 2.61/1.01  ------ Superposition Simplification Setup
% 2.61/1.01  
% 2.61/1.01  --sup_indices_passive                   []
% 2.61/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.61/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.61/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/1.01  --sup_full_bw                           [BwDemod]
% 2.61/1.01  --sup_immed_triv                        [TrivRules]
% 2.61/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.61/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/1.01  --sup_immed_bw_main                     []
% 2.61/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.61/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.61/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.61/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.61/1.01  
% 2.61/1.01  ------ Combination Options
% 2.61/1.01  
% 2.61/1.01  --comb_res_mult                         3
% 2.61/1.01  --comb_sup_mult                         2
% 2.61/1.01  --comb_inst_mult                        10
% 2.61/1.01  
% 2.61/1.01  ------ Debug Options
% 2.61/1.01  
% 2.61/1.01  --dbg_backtrace                         false
% 2.61/1.01  --dbg_dump_prop_clauses                 false
% 2.61/1.01  --dbg_dump_prop_clauses_file            -
% 2.61/1.01  --dbg_out_stat                          false
% 2.61/1.01  
% 2.61/1.01  
% 2.61/1.01  
% 2.61/1.01  
% 2.61/1.01  ------ Proving...
% 2.61/1.01  
% 2.61/1.01  
% 2.61/1.01  % SZS status Theorem for theBenchmark.p
% 2.61/1.01  
% 2.61/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.61/1.01  
% 2.61/1.01  fof(f11,axiom,(
% 2.61/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/1.01  
% 2.61/1.01  fof(f30,plain,(
% 2.61/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.61/1.01    inference(ennf_transformation,[],[f11])).
% 2.61/1.01  
% 2.61/1.01  fof(f31,plain,(
% 2.61/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.61/1.01    inference(flattening,[],[f30])).
% 2.61/1.01  
% 2.61/1.01  fof(f39,plain,(
% 2.61/1.01    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.61/1.01    inference(nnf_transformation,[],[f31])).
% 2.61/1.01  
% 2.61/1.01  fof(f56,plain,(
% 2.61/1.01    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.61/1.01    inference(cnf_transformation,[],[f39])).
% 2.61/1.01  
% 2.61/1.01  fof(f15,conjecture,(
% 2.61/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/1.01  
% 2.61/1.01  fof(f16,negated_conjecture,(
% 2.61/1.01    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.61/1.01    inference(negated_conjecture,[],[f15])).
% 2.61/1.01  
% 2.61/1.01  fof(f37,plain,(
% 2.61/1.01    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.61/1.01    inference(ennf_transformation,[],[f16])).
% 2.61/1.01  
% 2.61/1.01  fof(f38,plain,(
% 2.61/1.01    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.61/1.01    inference(flattening,[],[f37])).
% 2.61/1.01  
% 2.61/1.01  fof(f42,plain,(
% 2.61/1.01    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.61/1.01    introduced(choice_axiom,[])).
% 2.61/1.01  
% 2.61/1.01  fof(f41,plain,(
% 2.61/1.01    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.61/1.01    introduced(choice_axiom,[])).
% 2.61/1.01  
% 2.61/1.01  fof(f40,plain,(
% 2.61/1.01    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.61/1.01    introduced(choice_axiom,[])).
% 2.61/1.01  
% 2.61/1.01  fof(f43,plain,(
% 2.61/1.01    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.61/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f42,f41,f40])).
% 2.61/1.01  
% 2.61/1.01  fof(f65,plain,(
% 2.61/1.01    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.61/1.01    inference(cnf_transformation,[],[f43])).
% 2.61/1.01  
% 2.61/1.01  fof(f10,axiom,(
% 2.61/1.01    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/1.01  
% 2.61/1.01  fof(f28,plain,(
% 2.61/1.01    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.61/1.01    inference(ennf_transformation,[],[f10])).
% 2.61/1.01  
% 2.61/1.01  fof(f29,plain,(
% 2.61/1.01    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.61/1.01    inference(flattening,[],[f28])).
% 2.61/1.01  
% 2.61/1.01  fof(f55,plain,(
% 2.61/1.01    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.61/1.01    inference(cnf_transformation,[],[f29])).
% 2.61/1.01  
% 2.61/1.01  fof(f13,axiom,(
% 2.61/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 2.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/1.01  
% 2.61/1.01  fof(f33,plain,(
% 2.61/1.01    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.61/1.01    inference(ennf_transformation,[],[f13])).
% 2.61/1.01  
% 2.61/1.01  fof(f34,plain,(
% 2.61/1.01    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.61/1.01    inference(flattening,[],[f33])).
% 2.61/1.01  
% 2.61/1.01  fof(f59,plain,(
% 2.61/1.01    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.61/1.01    inference(cnf_transformation,[],[f34])).
% 2.61/1.01  
% 2.61/1.01  fof(f62,plain,(
% 2.61/1.01    ~v2_struct_0(sK1)),
% 2.61/1.01    inference(cnf_transformation,[],[f43])).
% 2.61/1.01  
% 2.61/1.01  fof(f63,plain,(
% 2.61/1.01    l1_struct_0(sK1)),
% 2.61/1.01    inference(cnf_transformation,[],[f43])).
% 2.61/1.01  
% 2.61/1.01  fof(f64,plain,(
% 2.61/1.01    v1_funct_1(sK2)),
% 2.61/1.01    inference(cnf_transformation,[],[f43])).
% 2.61/1.01  
% 2.61/1.01  fof(f12,axiom,(
% 2.61/1.01    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/1.01  
% 2.61/1.01  fof(f32,plain,(
% 2.61/1.01    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.61/1.01    inference(ennf_transformation,[],[f12])).
% 2.61/1.01  
% 2.61/1.01  fof(f58,plain,(
% 2.61/1.01    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.61/1.01    inference(cnf_transformation,[],[f32])).
% 2.61/1.01  
% 2.61/1.01  fof(f5,axiom,(
% 2.61/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/1.01  
% 2.61/1.01  fof(f17,plain,(
% 2.61/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.61/1.01    inference(pure_predicate_removal,[],[f5])).
% 2.61/1.01  
% 2.61/1.01  fof(f23,plain,(
% 2.61/1.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.61/1.01    inference(ennf_transformation,[],[f17])).
% 2.61/1.01  
% 2.61/1.01  fof(f49,plain,(
% 2.61/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.61/1.01    inference(cnf_transformation,[],[f23])).
% 2.61/1.01  
% 2.61/1.01  fof(f61,plain,(
% 2.61/1.01    l1_struct_0(sK0)),
% 2.61/1.01    inference(cnf_transformation,[],[f43])).
% 2.61/1.01  
% 2.61/1.01  fof(f66,plain,(
% 2.61/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.61/1.01    inference(cnf_transformation,[],[f43])).
% 2.61/1.01  
% 2.61/1.01  fof(f1,axiom,(
% 2.61/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/1.01  
% 2.61/1.01  fof(f18,plain,(
% 2.61/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.61/1.01    inference(ennf_transformation,[],[f1])).
% 2.61/1.01  
% 2.61/1.01  fof(f44,plain,(
% 2.61/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.61/1.01    inference(cnf_transformation,[],[f18])).
% 2.61/1.01  
% 2.61/1.01  fof(f2,axiom,(
% 2.61/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/1.01  
% 2.61/1.01  fof(f45,plain,(
% 2.61/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.61/1.01    inference(cnf_transformation,[],[f2])).
% 2.61/1.01  
% 2.61/1.01  fof(f8,axiom,(
% 2.61/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/1.01  
% 2.61/1.01  fof(f26,plain,(
% 2.61/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.61/1.01    inference(ennf_transformation,[],[f8])).
% 2.61/1.01  
% 2.61/1.01  fof(f52,plain,(
% 2.61/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.61/1.01    inference(cnf_transformation,[],[f26])).
% 2.61/1.01  
% 2.61/1.01  fof(f67,plain,(
% 2.61/1.01    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.61/1.01    inference(cnf_transformation,[],[f43])).
% 2.61/1.01  
% 2.61/1.01  fof(f6,axiom,(
% 2.61/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/1.01  
% 2.61/1.01  fof(f24,plain,(
% 2.61/1.01    ! [X0,X1,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.61/1.01    inference(ennf_transformation,[],[f6])).
% 2.61/1.01  
% 2.61/1.01  fof(f50,plain,(
% 2.61/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.61/1.01    inference(cnf_transformation,[],[f24])).
% 2.61/1.01  
% 2.61/1.01  fof(f4,axiom,(
% 2.61/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/1.01  
% 2.61/1.01  fof(f21,plain,(
% 2.61/1.01    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.61/1.01    inference(ennf_transformation,[],[f4])).
% 2.61/1.01  
% 2.61/1.01  fof(f22,plain,(
% 2.61/1.01    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.61/1.01    inference(flattening,[],[f21])).
% 2.61/1.01  
% 2.61/1.01  fof(f48,plain,(
% 2.61/1.01    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.61/1.01    inference(cnf_transformation,[],[f22])).
% 2.61/1.01  
% 2.61/1.01  fof(f68,plain,(
% 2.61/1.01    v2_funct_1(sK2)),
% 2.61/1.01    inference(cnf_transformation,[],[f43])).
% 2.61/1.01  
% 2.61/1.01  fof(f3,axiom,(
% 2.61/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(X0) = k4_relat_1(X0)))),
% 2.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/1.01  
% 2.61/1.01  fof(f19,plain,(
% 2.61/1.01    ! [X0] : ((k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.61/1.01    inference(ennf_transformation,[],[f3])).
% 2.61/1.01  
% 2.61/1.01  fof(f20,plain,(
% 2.61/1.01    ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.61/1.01    inference(flattening,[],[f19])).
% 2.61/1.01  
% 2.61/1.01  fof(f46,plain,(
% 2.61/1.01    ( ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.61/1.01    inference(cnf_transformation,[],[f20])).
% 2.61/1.01  
% 2.61/1.01  fof(f9,axiom,(
% 2.61/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k4_relat_1(X2) = k3_relset_1(X0,X1,X2))),
% 2.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/1.01  
% 2.61/1.01  fof(f27,plain,(
% 2.61/1.01    ! [X0,X1,X2] : (k4_relat_1(X2) = k3_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.61/1.01    inference(ennf_transformation,[],[f9])).
% 2.61/1.01  
% 2.61/1.01  fof(f53,plain,(
% 2.61/1.01    ( ! [X2,X0,X1] : (k4_relat_1(X2) = k3_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.61/1.01    inference(cnf_transformation,[],[f27])).
% 2.61/1.01  
% 2.61/1.01  fof(f7,axiom,(
% 2.61/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/1.01  
% 2.61/1.01  fof(f25,plain,(
% 2.61/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.61/1.01    inference(ennf_transformation,[],[f7])).
% 2.61/1.01  
% 2.61/1.01  fof(f51,plain,(
% 2.61/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.61/1.01    inference(cnf_transformation,[],[f25])).
% 2.61/1.01  
% 2.61/1.01  fof(f47,plain,(
% 2.61/1.01    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.61/1.01    inference(cnf_transformation,[],[f22])).
% 2.61/1.01  
% 2.61/1.01  fof(f69,plain,(
% 2.61/1.01    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 2.61/1.01    inference(cnf_transformation,[],[f43])).
% 2.61/1.01  
% 2.61/1.01  fof(f14,axiom,(
% 2.61/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.61/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.61/1.01  
% 2.61/1.01  fof(f35,plain,(
% 2.61/1.01    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.61/1.01    inference(ennf_transformation,[],[f14])).
% 2.61/1.01  
% 2.61/1.01  fof(f36,plain,(
% 2.61/1.01    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.61/1.01    inference(flattening,[],[f35])).
% 2.61/1.01  
% 2.61/1.01  fof(f60,plain,(
% 2.61/1.01    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.61/1.01    inference(cnf_transformation,[],[f36])).
% 2.61/1.01  
% 2.61/1.01  cnf(c_13,plain,
% 2.61/1.01      ( ~ v1_partfun1(X0,X1)
% 2.61/1.01      | ~ v4_relat_1(X0,X1)
% 2.61/1.01      | ~ v1_relat_1(X0)
% 2.61/1.01      | k1_relat_1(X0) = X1 ),
% 2.61/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_21,negated_conjecture,
% 2.61/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.61/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_10,plain,
% 2.61/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.61/1.01      | v1_partfun1(X0,X1)
% 2.61/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/1.01      | v1_xboole_0(X2)
% 2.61/1.01      | ~ v1_funct_1(X0) ),
% 2.61/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_15,plain,
% 2.61/1.01      ( v2_struct_0(X0)
% 2.61/1.01      | ~ l1_struct_0(X0)
% 2.61/1.01      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 2.61/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_24,negated_conjecture,
% 2.61/1.01      ( ~ v2_struct_0(sK1) ),
% 2.61/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_271,plain,
% 2.61/1.01      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 2.61/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_272,plain,
% 2.61/1.01      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.61/1.01      inference(unflattening,[status(thm)],[c_271]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_23,negated_conjecture,
% 2.61/1.01      ( l1_struct_0(sK1) ),
% 2.61/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_37,plain,
% 2.61/1.01      ( v2_struct_0(sK1)
% 2.61/1.01      | ~ l1_struct_0(sK1)
% 2.61/1.01      | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.61/1.01      inference(instantiation,[status(thm)],[c_15]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_274,plain,
% 2.61/1.01      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.61/1.01      inference(global_propositional_subsumption,
% 2.61/1.01                [status(thm)],
% 2.61/1.01                [c_272,c_24,c_23,c_37]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_296,plain,
% 2.61/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.61/1.01      | v1_partfun1(X0,X1)
% 2.61/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/1.01      | ~ v1_funct_1(X0)
% 2.61/1.01      | k2_struct_0(sK1) != X2 ),
% 2.61/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_274]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_297,plain,
% 2.61/1.01      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 2.61/1.01      | v1_partfun1(X0,X1)
% 2.61/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 2.61/1.01      | ~ v1_funct_1(X0) ),
% 2.61/1.01      inference(unflattening,[status(thm)],[c_296]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_369,plain,
% 2.61/1.01      ( v1_partfun1(X0,X1)
% 2.61/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 2.61/1.01      | ~ v1_funct_1(X0)
% 2.61/1.01      | u1_struct_0(sK0) != X1
% 2.61/1.01      | u1_struct_0(sK1) != k2_struct_0(sK1)
% 2.61/1.01      | sK2 != X0 ),
% 2.61/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_297]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_370,plain,
% 2.61/1.01      ( v1_partfun1(sK2,u1_struct_0(sK0))
% 2.61/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
% 2.61/1.01      | ~ v1_funct_1(sK2)
% 2.61/1.01      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 2.61/1.01      inference(unflattening,[status(thm)],[c_369]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_22,negated_conjecture,
% 2.61/1.01      ( v1_funct_1(sK2) ),
% 2.61/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_14,plain,
% 2.61/1.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.61/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_40,plain,
% 2.61/1.01      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.61/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_372,plain,
% 2.61/1.01      ( v1_partfun1(sK2,u1_struct_0(sK0))
% 2.61/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
% 2.61/1.01      inference(global_propositional_subsumption,
% 2.61/1.01                [status(thm)],
% 2.61/1.01                [c_370,c_23,c_22,c_40]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_441,plain,
% 2.61/1.01      ( ~ v4_relat_1(X0,X1)
% 2.61/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
% 2.61/1.01      | ~ v1_relat_1(X0)
% 2.61/1.01      | u1_struct_0(sK0) != X1
% 2.61/1.01      | k1_relat_1(X0) = X1
% 2.61/1.01      | sK2 != X0 ),
% 2.61/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_372]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_442,plain,
% 2.61/1.01      ( ~ v4_relat_1(sK2,u1_struct_0(sK0))
% 2.61/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
% 2.61/1.01      | ~ v1_relat_1(sK2)
% 2.61/1.01      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 2.61/1.01      inference(unflattening,[status(thm)],[c_441]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_5,plain,
% 2.61/1.01      ( v4_relat_1(X0,X1)
% 2.61/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.61/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_452,plain,
% 2.61/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
% 2.61/1.01      | ~ v1_relat_1(sK2)
% 2.61/1.01      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 2.61/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_442,c_5]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_550,plain,
% 2.61/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
% 2.61/1.01      | ~ v1_relat_1(sK2)
% 2.61/1.01      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 2.61/1.01      inference(subtyping,[status(esa)],[c_452]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_812,plain,
% 2.61/1.01      ( k1_relat_1(sK2) = u1_struct_0(sK0)
% 2.61/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.61/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.61/1.01      inference(predicate_to_equality,[status(thm)],[c_550]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_25,negated_conjecture,
% 2.61/1.01      ( l1_struct_0(sK0) ),
% 2.61/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_289,plain,
% 2.61/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.61/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_290,plain,
% 2.61/1.01      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.61/1.01      inference(unflattening,[status(thm)],[c_289]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_555,plain,
% 2.61/1.01      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.61/1.01      inference(subtyping,[status(esa)],[c_290]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_863,plain,
% 2.61/1.01      ( u1_struct_0(sK0) = k1_relat_1(sK2)
% 2.61/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.61/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.61/1.01      inference(light_normalisation,[status(thm)],[c_812,c_555]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_864,plain,
% 2.61/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.61/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.61/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.61/1.01      inference(demodulation,[status(thm)],[c_863,c_555]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_20,negated_conjecture,
% 2.61/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.61/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_557,negated_conjecture,
% 2.61/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.61/1.01      inference(subtyping,[status(esa)],[c_20]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_808,plain,
% 2.61/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.61/1.01      inference(predicate_to_equality,[status(thm)],[c_557]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_284,plain,
% 2.61/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.61/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_285,plain,
% 2.61/1.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.61/1.01      inference(unflattening,[status(thm)],[c_284]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_556,plain,
% 2.61/1.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.61/1.01      inference(subtyping,[status(esa)],[c_285]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_822,plain,
% 2.61/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.61/1.01      inference(light_normalisation,[status(thm)],[c_808,c_555,c_556]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_868,plain,
% 2.61/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.61/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.61/1.01      inference(forward_subsumption_resolution,
% 2.61/1.01                [status(thm)],
% 2.61/1.01                [c_864,c_822]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_876,plain,
% 2.61/1.01      ( ~ v1_relat_1(sK2) | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.61/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_868]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_0,plain,
% 2.61/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.61/1.01      | ~ v1_relat_1(X1)
% 2.61/1.01      | v1_relat_1(X0) ),
% 2.61/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_565,plain,
% 2.61/1.01      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 2.61/1.01      | ~ v1_relat_1(X1_53)
% 2.61/1.01      | v1_relat_1(X0_53) ),
% 2.61/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_902,plain,
% 2.61/1.01      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.61/1.01      | v1_relat_1(X0_53)
% 2.61/1.01      | ~ v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) ),
% 2.61/1.01      inference(instantiation,[status(thm)],[c_565]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_980,plain,
% 2.61/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.61/1.01      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.61/1.01      | v1_relat_1(sK2) ),
% 2.61/1.01      inference(instantiation,[status(thm)],[c_902]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1,plain,
% 2.61/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.61/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_564,plain,
% 2.61/1.01      ( v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) ),
% 2.61/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_992,plain,
% 2.61/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.61/1.01      inference(instantiation,[status(thm)],[c_564]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1723,plain,
% 2.61/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.61/1.01      inference(global_propositional_subsumption,
% 2.61/1.01                [status(thm)],
% 2.61/1.01                [c_868,c_20,c_876,c_980,c_992]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_8,plain,
% 2.61/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.61/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_561,plain,
% 2.61/1.01      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.61/1.01      | k2_relset_1(X0_55,X1_55,X0_53) = k2_relat_1(X0_53) ),
% 2.61/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_806,plain,
% 2.61/1.01      ( k2_relset_1(X0_55,X1_55,X0_53) = k2_relat_1(X0_53)
% 2.61/1.01      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 2.61/1.01      inference(predicate_to_equality,[status(thm)],[c_561]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1066,plain,
% 2.61/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.61/1.01      inference(superposition,[status(thm)],[c_822,c_806]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_19,negated_conjecture,
% 2.61/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.61/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_558,negated_conjecture,
% 2.61/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.61/1.01      inference(subtyping,[status(esa)],[c_19]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_819,plain,
% 2.61/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.61/1.01      inference(light_normalisation,[status(thm)],[c_558,c_555,c_556]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1158,plain,
% 2.61/1.01      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.61/1.01      inference(demodulation,[status(thm)],[c_1066,c_819]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1194,plain,
% 2.61/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.61/1.01      inference(demodulation,[status(thm)],[c_1158,c_822]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1726,plain,
% 2.61/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 2.61/1.01      inference(demodulation,[status(thm)],[c_1723,c_1194]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_6,plain,
% 2.61/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/1.01      | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.61/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_563,plain,
% 2.61/1.01      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.61/1.01      | m1_subset_1(k3_relset_1(X0_55,X1_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) ),
% 2.61/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_804,plain,
% 2.61/1.01      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.61/1.01      | m1_subset_1(k3_relset_1(X0_55,X1_55,X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) = iProver_top ),
% 2.61/1.01      inference(predicate_to_equality,[status(thm)],[c_563]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1289,plain,
% 2.61/1.01      ( k2_relset_1(X0_55,X1_55,k3_relset_1(X1_55,X0_55,X0_53)) = k2_relat_1(k3_relset_1(X1_55,X0_55,X0_53))
% 2.61/1.01      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) != iProver_top ),
% 2.61/1.01      inference(superposition,[status(thm)],[c_804,c_806]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_2233,plain,
% 2.61/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k3_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) = k2_relat_1(k3_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) ),
% 2.61/1.01      inference(superposition,[status(thm)],[c_1726,c_1289]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_802,plain,
% 2.61/1.01      ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
% 2.61/1.01      | v1_relat_1(X1_53) != iProver_top
% 2.61/1.01      | v1_relat_1(X0_53) = iProver_top ),
% 2.61/1.01      inference(predicate_to_equality,[status(thm)],[c_565]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1020,plain,
% 2.61/1.01      ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != iProver_top
% 2.61/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.61/1.01      inference(superposition,[status(thm)],[c_822,c_802]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_31,plain,
% 2.61/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.61/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_981,plain,
% 2.61/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.61/1.01      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.61/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.61/1.01      inference(predicate_to_equality,[status(thm)],[c_980]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_993,plain,
% 2.61/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.61/1.01      inference(predicate_to_equality,[status(thm)],[c_992]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1354,plain,
% 2.61/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 2.61/1.01      inference(global_propositional_subsumption,
% 2.61/1.01                [status(thm)],
% 2.61/1.01                [c_1020,c_31,c_981,c_993]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_3,plain,
% 2.61/1.01      ( ~ v1_funct_1(X0)
% 2.61/1.01      | ~ v2_funct_1(X0)
% 2.61/1.01      | ~ v1_relat_1(X0)
% 2.61/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.61/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_18,negated_conjecture,
% 2.61/1.01      ( v2_funct_1(sK2) ),
% 2.61/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_402,plain,
% 2.61/1.01      ( ~ v1_funct_1(X0)
% 2.61/1.01      | ~ v1_relat_1(X0)
% 2.61/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.61/1.01      | sK2 != X0 ),
% 2.61/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_18]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_403,plain,
% 2.61/1.01      ( ~ v1_funct_1(sK2)
% 2.61/1.01      | ~ v1_relat_1(sK2)
% 2.61/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.61/1.01      inference(unflattening,[status(thm)],[c_402]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_405,plain,
% 2.61/1.01      ( ~ v1_relat_1(sK2)
% 2.61/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.61/1.01      inference(global_propositional_subsumption,
% 2.61/1.01                [status(thm)],
% 2.61/1.01                [c_403,c_22]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_552,plain,
% 2.61/1.01      ( ~ v1_relat_1(sK2)
% 2.61/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.61/1.01      inference(subtyping,[status(esa)],[c_405]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_810,plain,
% 2.61/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.61/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.61/1.01      inference(predicate_to_equality,[status(thm)],[c_552]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1359,plain,
% 2.61/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.61/1.01      inference(superposition,[status(thm)],[c_1354,c_810]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_2,plain,
% 2.61/1.01      ( ~ v1_funct_1(X0)
% 2.61/1.01      | ~ v2_funct_1(X0)
% 2.61/1.01      | ~ v1_relat_1(X0)
% 2.61/1.01      | k4_relat_1(X0) = k2_funct_1(X0) ),
% 2.61/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_416,plain,
% 2.61/1.01      ( ~ v1_funct_1(X0)
% 2.61/1.01      | ~ v1_relat_1(X0)
% 2.61/1.01      | k4_relat_1(X0) = k2_funct_1(X0)
% 2.61/1.01      | sK2 != X0 ),
% 2.61/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_18]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_417,plain,
% 2.61/1.01      ( ~ v1_funct_1(sK2)
% 2.61/1.01      | ~ v1_relat_1(sK2)
% 2.61/1.01      | k4_relat_1(sK2) = k2_funct_1(sK2) ),
% 2.61/1.01      inference(unflattening,[status(thm)],[c_416]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_419,plain,
% 2.61/1.01      ( ~ v1_relat_1(sK2) | k4_relat_1(sK2) = k2_funct_1(sK2) ),
% 2.61/1.01      inference(global_propositional_subsumption,
% 2.61/1.01                [status(thm)],
% 2.61/1.01                [c_417,c_22]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_551,plain,
% 2.61/1.01      ( ~ v1_relat_1(sK2) | k4_relat_1(sK2) = k2_funct_1(sK2) ),
% 2.61/1.01      inference(subtyping,[status(esa)],[c_419]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_811,plain,
% 2.61/1.01      ( k4_relat_1(sK2) = k2_funct_1(sK2)
% 2.61/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.61/1.01      inference(predicate_to_equality,[status(thm)],[c_551]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1361,plain,
% 2.61/1.01      ( k4_relat_1(sK2) = k2_funct_1(sK2) ),
% 2.61/1.01      inference(superposition,[status(thm)],[c_1354,c_811]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_9,plain,
% 2.61/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/1.01      | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
% 2.61/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_560,plain,
% 2.61/1.01      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.61/1.01      | k3_relset_1(X0_55,X1_55,X0_53) = k4_relat_1(X0_53) ),
% 2.61/1.01      inference(subtyping,[status(esa)],[c_9]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_807,plain,
% 2.61/1.01      ( k3_relset_1(X0_55,X1_55,X0_53) = k4_relat_1(X0_53)
% 2.61/1.01      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 2.61/1.01      inference(predicate_to_equality,[status(thm)],[c_560]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1116,plain,
% 2.61/1.01      ( k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k4_relat_1(sK2) ),
% 2.61/1.01      inference(superposition,[status(thm)],[c_822,c_807]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1244,plain,
% 2.61/1.01      ( k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k4_relat_1(sK2) ),
% 2.61/1.01      inference(light_normalisation,[status(thm)],[c_1116,c_1158]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1506,plain,
% 2.61/1.01      ( k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.61/1.01      inference(demodulation,[status(thm)],[c_1361,c_1244]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_2060,plain,
% 2.61/1.01      ( k3_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.61/1.01      inference(light_normalisation,[status(thm)],[c_1506,c_1723]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_2239,plain,
% 2.61/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.61/1.01      inference(light_normalisation,[status(thm)],[c_2233,c_1359,c_2060]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1287,plain,
% 2.61/1.01      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 2.61/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 2.61/1.01      inference(superposition,[status(thm)],[c_1244,c_804]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1369,plain,
% 2.61/1.01      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 2.61/1.01      inference(global_propositional_subsumption,
% 2.61/1.01                [status(thm)],
% 2.61/1.01                [c_1287,c_1194]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_7,plain,
% 2.61/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.61/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_562,plain,
% 2.61/1.01      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.61/1.01      | k1_relset_1(X0_55,X1_55,X0_53) = k1_relat_1(X0_53) ),
% 2.61/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_805,plain,
% 2.61/1.01      ( k1_relset_1(X0_55,X1_55,X0_53) = k1_relat_1(X0_53)
% 2.61/1.01      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 2.61/1.01      inference(predicate_to_equality,[status(thm)],[c_562]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1376,plain,
% 2.61/1.01      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
% 2.61/1.01      inference(superposition,[status(thm)],[c_1369,c_805]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_4,plain,
% 2.61/1.01      ( ~ v1_funct_1(X0)
% 2.61/1.01      | ~ v2_funct_1(X0)
% 2.61/1.01      | ~ v1_relat_1(X0)
% 2.61/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.61/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_388,plain,
% 2.61/1.01      ( ~ v1_funct_1(X0)
% 2.61/1.01      | ~ v1_relat_1(X0)
% 2.61/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.61/1.01      | sK2 != X0 ),
% 2.61/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_18]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_389,plain,
% 2.61/1.01      ( ~ v1_funct_1(sK2)
% 2.61/1.01      | ~ v1_relat_1(sK2)
% 2.61/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.61/1.01      inference(unflattening,[status(thm)],[c_388]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_391,plain,
% 2.61/1.01      ( ~ v1_relat_1(sK2)
% 2.61/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.61/1.01      inference(global_propositional_subsumption,
% 2.61/1.01                [status(thm)],
% 2.61/1.01                [c_389,c_22]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_553,plain,
% 2.61/1.01      ( ~ v1_relat_1(sK2)
% 2.61/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.61/1.01      inference(subtyping,[status(esa)],[c_391]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_809,plain,
% 2.61/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.61/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.61/1.01      inference(predicate_to_equality,[status(thm)],[c_553]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1360,plain,
% 2.61/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.61/1.01      inference(superposition,[status(thm)],[c_1354,c_809]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1846,plain,
% 2.61/1.01      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.61/1.01      inference(light_normalisation,
% 2.61/1.01                [status(thm)],
% 2.61/1.01                [c_1376,c_1360,c_1361,c_1723]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_17,negated_conjecture,
% 2.61/1.01      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.61/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.61/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_559,negated_conjecture,
% 2.61/1.01      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.61/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.61/1.01      inference(subtyping,[status(esa)],[c_17]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_16,plain,
% 2.61/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.61/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/1.01      | ~ v1_funct_1(X0)
% 2.61/1.01      | ~ v2_funct_1(X0)
% 2.61/1.01      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.61/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.61/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_358,plain,
% 2.61/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.61/1.01      | ~ v1_funct_1(X0)
% 2.61/1.01      | ~ v2_funct_1(X0)
% 2.61/1.01      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.61/1.01      | k2_relset_1(X1,X2,X0) != X2
% 2.61/1.01      | u1_struct_0(sK0) != X1
% 2.61/1.01      | u1_struct_0(sK1) != X2
% 2.61/1.01      | sK2 != X0 ),
% 2.61/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_359,plain,
% 2.61/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.61/1.01      | ~ v1_funct_1(sK2)
% 2.61/1.01      | ~ v2_funct_1(sK2)
% 2.61/1.01      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.61/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 2.61/1.01      inference(unflattening,[status(thm)],[c_358]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_361,plain,
% 2.61/1.01      ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.61/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 2.61/1.01      inference(global_propositional_subsumption,
% 2.61/1.01                [status(thm)],
% 2.61/1.01                [c_359,c_22,c_20,c_18]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_554,plain,
% 2.61/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 2.61/1.01      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.61/1.01      inference(subtyping,[status(esa)],[c_361]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_855,plain,
% 2.61/1.01      ( k2_struct_0(sK1) != k2_struct_0(sK1)
% 2.61/1.01      | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.61/1.01      inference(light_normalisation,
% 2.61/1.01                [status(thm)],
% 2.61/1.01                [c_554,c_555,c_556,c_819]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_856,plain,
% 2.61/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.61/1.01      inference(equality_resolution_simp,[status(thm)],[c_855]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_871,plain,
% 2.61/1.01      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.61/1.01      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
% 2.61/1.01      inference(light_normalisation,
% 2.61/1.01                [status(thm)],
% 2.61/1.01                [c_559,c_555,c_556,c_856]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1195,plain,
% 2.61/1.01      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.61/1.01      | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 2.61/1.01      inference(demodulation,[status(thm)],[c_1158,c_871]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(c_1730,plain,
% 2.61/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2)
% 2.61/1.01      | k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 2.61/1.01      inference(demodulation,[status(thm)],[c_1723,c_1195]) ).
% 2.61/1.01  
% 2.61/1.01  cnf(contradiction,plain,
% 2.61/1.01      ( $false ),
% 2.61/1.01      inference(minisat,[status(thm)],[c_2239,c_1846,c_1730]) ).
% 2.61/1.01  
% 2.61/1.01  
% 2.61/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.61/1.01  
% 2.61/1.01  ------                               Statistics
% 2.61/1.01  
% 2.61/1.01  ------ General
% 2.61/1.01  
% 2.61/1.01  abstr_ref_over_cycles:                  0
% 2.61/1.01  abstr_ref_under_cycles:                 0
% 2.61/1.01  gc_basic_clause_elim:                   0
% 2.61/1.01  forced_gc_time:                         0
% 2.61/1.01  parsing_time:                           0.018
% 2.61/1.01  unif_index_cands_time:                  0.
% 2.61/1.01  unif_index_add_time:                    0.
% 2.61/1.01  orderings_time:                         0.
% 2.61/1.01  out_proof_time:                         0.016
% 2.61/1.01  total_time:                             0.161
% 2.61/1.01  num_of_symbols:                         57
% 2.61/1.01  num_of_terms:                           2072
% 2.61/1.01  
% 2.61/1.01  ------ Preprocessing
% 2.61/1.01  
% 2.61/1.01  num_of_splits:                          0
% 2.61/1.01  num_of_split_atoms:                     0
% 2.61/1.01  num_of_reused_defs:                     0
% 2.61/1.01  num_eq_ax_congr_red:                    15
% 2.61/1.01  num_of_sem_filtered_clauses:            1
% 2.61/1.01  num_of_subtypes:                        4
% 2.61/1.01  monotx_restored_types:                  0
% 2.61/1.01  sat_num_of_epr_types:                   0
% 2.61/1.01  sat_num_of_non_cyclic_types:            0
% 2.61/1.01  sat_guarded_non_collapsed_types:        0
% 2.61/1.01  num_pure_diseq_elim:                    0
% 2.61/1.01  simp_replaced_by:                       0
% 2.61/1.01  res_preprocessed:                       106
% 2.61/1.01  prep_upred:                             0
% 2.61/1.01  prep_unflattend:                        18
% 2.61/1.01  smt_new_axioms:                         0
% 2.61/1.01  pred_elim_cands:                        2
% 2.61/1.01  pred_elim:                              8
% 2.61/1.01  pred_elim_cl:                           9
% 2.61/1.01  pred_elim_cycles:                       11
% 2.61/1.01  merged_defs:                            0
% 2.61/1.01  merged_defs_ncl:                        0
% 2.61/1.01  bin_hyper_res:                          0
% 2.61/1.01  prep_cycles:                            4
% 2.61/1.01  pred_elim_time:                         0.004
% 2.61/1.01  splitting_time:                         0.
% 2.61/1.01  sem_filter_time:                        0.
% 2.61/1.01  monotx_time:                            0.
% 2.61/1.01  subtype_inf_time:                       0.
% 2.61/1.01  
% 2.61/1.01  ------ Problem properties
% 2.61/1.01  
% 2.61/1.01  clauses:                                16
% 2.61/1.01  conjectures:                            3
% 2.61/1.01  epr:                                    0
% 2.61/1.01  horn:                                   16
% 2.61/1.01  ground:                                 10
% 2.61/1.01  unary:                                  5
% 2.61/1.01  binary:                                 9
% 2.61/1.01  lits:                                   29
% 2.61/1.01  lits_eq:                                14
% 2.61/1.01  fd_pure:                                0
% 2.61/1.01  fd_pseudo:                              0
% 2.61/1.01  fd_cond:                                0
% 2.61/1.01  fd_pseudo_cond:                         0
% 2.61/1.01  ac_symbols:                             0
% 2.61/1.01  
% 2.61/1.01  ------ Propositional Solver
% 2.61/1.01  
% 2.61/1.01  prop_solver_calls:                      31
% 2.61/1.01  prop_fast_solver_calls:                 578
% 2.61/1.01  smt_solver_calls:                       0
% 2.61/1.01  smt_fast_solver_calls:                  0
% 2.61/1.01  prop_num_of_clauses:                    789
% 2.61/1.01  prop_preprocess_simplified:             2951
% 2.61/1.01  prop_fo_subsumed:                       13
% 2.61/1.01  prop_solver_time:                       0.
% 2.61/1.01  smt_solver_time:                        0.
% 2.61/1.01  smt_fast_solver_time:                   0.
% 2.61/1.01  prop_fast_solver_time:                  0.
% 2.61/1.01  prop_unsat_core_time:                   0.
% 2.61/1.01  
% 2.61/1.01  ------ QBF
% 2.61/1.01  
% 2.61/1.01  qbf_q_res:                              0
% 2.61/1.01  qbf_num_tautologies:                    0
% 2.61/1.01  qbf_prep_cycles:                        0
% 2.61/1.01  
% 2.61/1.01  ------ BMC1
% 2.61/1.01  
% 2.61/1.01  bmc1_current_bound:                     -1
% 2.61/1.01  bmc1_last_solved_bound:                 -1
% 2.61/1.01  bmc1_unsat_core_size:                   -1
% 2.61/1.01  bmc1_unsat_core_parents_size:           -1
% 2.61/1.01  bmc1_merge_next_fun:                    0
% 2.61/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.61/1.01  
% 2.61/1.01  ------ Instantiation
% 2.61/1.01  
% 2.61/1.01  inst_num_of_clauses:                    346
% 2.61/1.01  inst_num_in_passive:                    73
% 2.61/1.01  inst_num_in_active:                     214
% 2.61/1.01  inst_num_in_unprocessed:                61
% 2.61/1.01  inst_num_of_loops:                      230
% 2.61/1.01  inst_num_of_learning_restarts:          0
% 2.61/1.01  inst_num_moves_active_passive:          9
% 2.61/1.01  inst_lit_activity:                      0
% 2.61/1.01  inst_lit_activity_moves:                0
% 2.61/1.01  inst_num_tautologies:                   0
% 2.61/1.01  inst_num_prop_implied:                  0
% 2.61/1.01  inst_num_existing_simplified:           0
% 2.61/1.01  inst_num_eq_res_simplified:             0
% 2.61/1.01  inst_num_child_elim:                    0
% 2.61/1.01  inst_num_of_dismatching_blockings:      109
% 2.61/1.01  inst_num_of_non_proper_insts:           371
% 2.61/1.01  inst_num_of_duplicates:                 0
% 2.61/1.01  inst_inst_num_from_inst_to_res:         0
% 2.61/1.01  inst_dismatching_checking_time:         0.
% 2.61/1.01  
% 2.61/1.01  ------ Resolution
% 2.61/1.01  
% 2.61/1.01  res_num_of_clauses:                     0
% 2.61/1.01  res_num_in_passive:                     0
% 2.61/1.01  res_num_in_active:                      0
% 2.61/1.01  res_num_of_loops:                       110
% 2.61/1.01  res_forward_subset_subsumed:            59
% 2.61/1.01  res_backward_subset_subsumed:           10
% 2.61/1.01  res_forward_subsumed:                   0
% 2.61/1.01  res_backward_subsumed:                  0
% 2.61/1.01  res_forward_subsumption_resolution:     1
% 2.61/1.01  res_backward_subsumption_resolution:    0
% 2.61/1.01  res_clause_to_clause_subsumption:       73
% 2.61/1.01  res_orphan_elimination:                 0
% 2.61/1.01  res_tautology_del:                      67
% 2.61/1.01  res_num_eq_res_simplified:              0
% 2.61/1.01  res_num_sel_changes:                    0
% 2.61/1.01  res_moves_from_active_to_pass:          0
% 2.61/1.01  
% 2.61/1.01  ------ Superposition
% 2.61/1.01  
% 2.61/1.01  sup_time_total:                         0.
% 2.61/1.01  sup_time_generating:                    0.
% 2.61/1.01  sup_time_sim_full:                      0.
% 2.61/1.01  sup_time_sim_immed:                     0.
% 2.61/1.01  
% 2.61/1.01  sup_num_of_clauses:                     35
% 2.61/1.01  sup_num_in_active:                      25
% 2.61/1.01  sup_num_in_passive:                     10
% 2.61/1.01  sup_num_of_loops:                       44
% 2.61/1.01  sup_fw_superposition:                   8
% 2.61/1.01  sup_bw_superposition:                   24
% 2.61/1.01  sup_immediate_simplified:               1
% 2.61/1.01  sup_given_eliminated:                   0
% 2.61/1.01  comparisons_done:                       0
% 2.61/1.01  comparisons_avoided:                    0
% 2.61/1.01  
% 2.61/1.01  ------ Simplifications
% 2.61/1.01  
% 2.61/1.01  
% 2.61/1.01  sim_fw_subset_subsumed:                 2
% 2.61/1.01  sim_bw_subset_subsumed:                 3
% 2.61/1.01  sim_fw_subsumed:                        0
% 2.61/1.01  sim_bw_subsumed:                        0
% 2.61/1.01  sim_fw_subsumption_res:                 2
% 2.61/1.01  sim_bw_subsumption_res:                 0
% 2.61/1.01  sim_tautology_del:                      0
% 2.61/1.01  sim_eq_tautology_del:                   2
% 2.61/1.01  sim_eq_res_simp:                        1
% 2.61/1.01  sim_fw_demodulated:                     1
% 2.61/1.01  sim_bw_demodulated:                     17
% 2.61/1.01  sim_light_normalised:                   13
% 2.61/1.01  sim_joinable_taut:                      0
% 2.61/1.01  sim_joinable_simp:                      0
% 2.61/1.01  sim_ac_normalised:                      0
% 2.61/1.01  sim_smt_subsumption:                    0
% 2.61/1.01  
%------------------------------------------------------------------------------
