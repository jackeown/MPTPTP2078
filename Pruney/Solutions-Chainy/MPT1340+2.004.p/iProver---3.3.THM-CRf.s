%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:21 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :  241 (14291 expanded)
%              Number of clauses        :  158 (4364 expanded)
%              Number of leaves         :   22 (3961 expanded)
%              Depth                    :   34
%              Number of atoms          :  847 (88948 expanded)
%              Number of equality atoms :  347 (14673 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,
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

fof(f54,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f53,f52,f51])).

fof(f86,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f78,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f81,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f83,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f35])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f82,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f85,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f55,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f57,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f88,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f59,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f58,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f64,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f14,axiom,(
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

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f56,plain,(
    ! [X0] :
      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f66,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f89,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_716,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1255,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_23,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_34,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_405,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_34])).

cnf(c_406,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_711,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_406])).

cnf(c_32,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_400,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_401,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_712,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_401])).

cnf(c_1280,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1255,c_711,c_712])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_24,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_387,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_33])).

cnf(c_388,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_47,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_390,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_388,c_33,c_32,c_47])).

cnf(c_412,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_390])).

cnf(c_413,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_18,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_470,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_13,c_18])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_474,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_470,c_18,c_13,c_12])).

cnf(c_475,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_474])).

cnf(c_514,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_413,c_475])).

cnf(c_709,plain,
    ( ~ v1_funct_2(X0_54,X0_55,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_54)
    | k1_relat_1(X0_54) = X0_55 ),
    inference(subtyping,[status(esa)],[c_514])).

cnf(c_1261,plain,
    ( k1_relat_1(X0_54) = X0_55
    | v1_funct_2(X0_54,X0_55,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_709])).

cnf(c_1358,plain,
    ( k1_relat_1(X0_54) = X0_55
    | v1_funct_2(X0_54,X0_55,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1261,c_712])).

cnf(c_1678,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_55))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1280,c_1358])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_38,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_715,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1256,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_715])).

cnf(c_1274,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1256,c_711,c_712])).

cnf(c_1683,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_55))) != iProver_top
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1678,c_38,c_1274])).

cnf(c_1684,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_55))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1683])).

cnf(c_1691,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1280,c_1684])).

cnf(c_1771,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1691,c_1280])).

cnf(c_723,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1249,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_relat_1(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_723])).

cnf(c_1977,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1771,c_1249])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_734,plain,
    ( ~ v1_relat_1(X0_54)
    | k1_relat_1(k4_relat_1(X0_54)) = k2_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1238,plain,
    ( k1_relat_1(k4_relat_1(X0_54)) = k2_relat_1(X0_54)
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_734])).

cnf(c_2414,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1977,c_1238])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X1,X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_728,plain,
    ( ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54)
    | v2_funct_1(X0_54)
    | ~ v2_funct_1(k5_relat_1(X1_54,X0_54))
    | ~ v1_relat_1(X0_54)
    | ~ v1_relat_1(X1_54)
    | k1_relat_1(X0_54) != k2_relat_1(X1_54) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1244,plain,
    ( k1_relat_1(X0_54) != k2_relat_1(X1_54)
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v2_funct_1(X0_54) = iProver_top
    | v2_funct_1(k5_relat_1(X1_54,X0_54)) != iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_relat_1(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_3505,plain,
    ( k2_relat_1(X0_54) != k2_relat_1(sK2)
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v2_funct_1(k5_relat_1(X0_54,k4_relat_1(sK2))) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2414,c_1244])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1509,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_723])).

cnf(c_1510,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1509])).

cnf(c_714,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1257,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_714])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_733,plain,
    ( ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | k2_funct_1(X0_54) = k4_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1239,plain,
    ( k2_funct_1(X0_54) = k4_relat_1(X0_54)
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_733])).

cnf(c_1605,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1257,c_1239])).

cnf(c_27,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_785,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_733])).

cnf(c_1663,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1605,c_31,c_29,c_27,c_785,c_1509])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_732,plain,
    ( ~ v1_funct_1(X0_54)
    | v1_funct_1(k2_funct_1(X0_54))
    | ~ v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1240,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k2_funct_1(X0_54)) = iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_1921,plain,
    ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_1240])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_731,plain,
    ( ~ v1_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | v1_relat_1(k2_funct_1(X0_54)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1241,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_relat_1(k2_funct_1(X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_1983,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1663,c_1241])).

cnf(c_5463,plain,
    ( v1_relat_1(X0_54) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) = iProver_top
    | v2_funct_1(k5_relat_1(X0_54,k4_relat_1(sK2))) != iProver_top
    | k2_relat_1(X0_54) != k2_relat_1(sK2)
    | v1_funct_1(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3505,c_38,c_40,c_1510,c_1921,c_1983])).

cnf(c_5464,plain,
    ( k2_relat_1(X0_54) != k2_relat_1(sK2)
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(k5_relat_1(X0_54,k4_relat_1(sK2))) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_5463])).

cnf(c_5477,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,k4_relat_1(sK2))) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5464])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_725,plain,
    ( ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | k5_relat_1(X0_54,k2_funct_1(X0_54)) = k6_relat_1(k1_relat_1(X0_54)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1247,plain,
    ( k5_relat_1(X0_54,k2_funct_1(X0_54)) = k6_relat_1(k1_relat_1(X0_54))
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_725])).

cnf(c_2702,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1257,c_1247])).

cnf(c_2725,plain,
    ( k5_relat_1(sK2,k4_relat_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2702,c_1663])).

cnf(c_41,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2967,plain,
    ( k5_relat_1(sK2,k4_relat_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2725,c_40,c_41,c_1510])).

cnf(c_5482,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5477,c_2967])).

cnf(c_5929,plain,
    ( v2_funct_1(k4_relat_1(sK2)) = iProver_top
    | v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5482,c_38,c_40,c_1510])).

cnf(c_5930,plain,
    ( v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5929])).

cnf(c_5,plain,
    ( v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_730,plain,
    ( v2_funct_1(k6_relat_1(X0_55)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1242,plain,
    ( v2_funct_1(k6_relat_1(X0_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_730])).

cnf(c_5935,plain,
    ( v2_funct_1(k4_relat_1(sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5930,c_1242])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_722,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1250,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_722])).

cnf(c_2100,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1771,c_1250])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_717,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1277,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_717,c_711,c_712])).

cnf(c_1773,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1691,c_1277])).

cnf(c_3026,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2100,c_1773])).

cnf(c_3094,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3026,c_2100])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_721,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55)))
    | ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1251,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_721])).

cnf(c_3700,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3094,c_1251])).

cnf(c_3713,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3700,c_1663])).

cnf(c_3097,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3026,c_1771])).

cnf(c_1772,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1691,c_1274])).

cnf(c_3098,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3026,c_1772])).

cnf(c_3875,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3713,c_38,c_41,c_3097,c_3098])).

cnf(c_3880,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3875,c_1250])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_735,plain,
    ( ~ v1_relat_1(X0_54)
    | k2_relat_1(k4_relat_1(X0_54)) = k1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1237,plain,
    ( k2_relat_1(k4_relat_1(X0_54)) = k1_relat_1(X0_54)
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_735])).

cnf(c_2415,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1977,c_1237])).

cnf(c_3883,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3880,c_2415])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_719,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1253,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54)
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_719])).

cnf(c_4676,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_funct_1(k4_relat_1(sK2))
    | v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3883,c_1253])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_724,plain,
    ( ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | k2_funct_1(k2_funct_1(X0_54)) = X0_54 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1248,plain,
    ( k2_funct_1(k2_funct_1(X0_54)) = X0_54
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_724])).

cnf(c_2106,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1257,c_1248])).

cnf(c_2121,plain,
    ( k2_funct_1(k4_relat_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2106,c_1663])).

cnf(c_2289,plain,
    ( k2_funct_1(k4_relat_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2121,c_40,c_41,c_1510])).

cnf(c_4696,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = sK2
    | v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4676,c_2289])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_720,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1252,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_720])).

cnf(c_2890,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1773,c_1252])).

cnf(c_2891,plain,
    ( v1_funct_2(k4_relat_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2890,c_1663])).

cnf(c_3020,plain,
    ( v1_funct_2(k4_relat_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2891,c_38,c_41,c_1771,c_1772])).

cnf(c_3095,plain,
    ( v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3026,c_3020])).

cnf(c_4827,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = sK2
    | v2_funct_1(k4_relat_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4696,c_38,c_40,c_41,c_1510,c_1921,c_3095,c_3097,c_3098,c_3713])).

cnf(c_5937,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_5935,c_4827])).

cnf(c_19,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_26,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_435,plain,
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
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_436,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_710,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_436])).

cnf(c_737,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sP0_iProver_split
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_710])).

cnf(c_1259,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_1433,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1259,c_711,c_712])).

cnf(c_736,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_54)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_710])).

cnf(c_1260,plain,
    ( v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_736])).

cnf(c_1349,plain,
    ( v1_funct_2(X0_54,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1260,c_711,c_712])).

cnf(c_1439,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1433,c_1349])).

cnf(c_2295,plain,
    ( k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_relat_1(sK2),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1439,c_1691])).

cnf(c_3096,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3026,c_2295])).

cnf(c_3699,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3094,c_1253])).

cnf(c_3724,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k4_relat_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3699,c_1663])).

cnf(c_3871,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3724,c_38,c_41,c_3097,c_3098])).

cnf(c_4475,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3096,c_3871])).

cnf(c_6054,plain,
    ( sK2 != sK2
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5937,c_4475])).

cnf(c_739,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_774,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_739])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6054,c_3098,c_3097,c_774,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:06:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.03/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/0.99  
% 3.03/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.03/0.99  
% 3.03/0.99  ------  iProver source info
% 3.03/0.99  
% 3.03/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.03/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.03/0.99  git: non_committed_changes: false
% 3.03/0.99  git: last_make_outside_of_git: false
% 3.03/0.99  
% 3.03/0.99  ------ 
% 3.03/0.99  
% 3.03/0.99  ------ Input Options
% 3.03/0.99  
% 3.03/0.99  --out_options                           all
% 3.03/0.99  --tptp_safe_out                         true
% 3.03/0.99  --problem_path                          ""
% 3.03/0.99  --include_path                          ""
% 3.03/0.99  --clausifier                            res/vclausify_rel
% 3.03/0.99  --clausifier_options                    --mode clausify
% 3.03/0.99  --stdin                                 false
% 3.03/0.99  --stats_out                             all
% 3.03/0.99  
% 3.03/0.99  ------ General Options
% 3.03/0.99  
% 3.03/0.99  --fof                                   false
% 3.03/0.99  --time_out_real                         305.
% 3.03/0.99  --time_out_virtual                      -1.
% 3.03/0.99  --symbol_type_check                     false
% 3.03/0.99  --clausify_out                          false
% 3.03/0.99  --sig_cnt_out                           false
% 3.03/0.99  --trig_cnt_out                          false
% 3.03/0.99  --trig_cnt_out_tolerance                1.
% 3.03/0.99  --trig_cnt_out_sk_spl                   false
% 3.03/0.99  --abstr_cl_out                          false
% 3.03/0.99  
% 3.03/0.99  ------ Global Options
% 3.03/0.99  
% 3.03/0.99  --schedule                              default
% 3.03/0.99  --add_important_lit                     false
% 3.03/0.99  --prop_solver_per_cl                    1000
% 3.03/0.99  --min_unsat_core                        false
% 3.03/0.99  --soft_assumptions                      false
% 3.03/0.99  --soft_lemma_size                       3
% 3.03/0.99  --prop_impl_unit_size                   0
% 3.03/0.99  --prop_impl_unit                        []
% 3.03/0.99  --share_sel_clauses                     true
% 3.03/0.99  --reset_solvers                         false
% 3.03/0.99  --bc_imp_inh                            [conj_cone]
% 3.03/0.99  --conj_cone_tolerance                   3.
% 3.03/0.99  --extra_neg_conj                        none
% 3.03/0.99  --large_theory_mode                     true
% 3.03/0.99  --prolific_symb_bound                   200
% 3.03/0.99  --lt_threshold                          2000
% 3.03/0.99  --clause_weak_htbl                      true
% 3.03/0.99  --gc_record_bc_elim                     false
% 3.03/0.99  
% 3.03/0.99  ------ Preprocessing Options
% 3.03/0.99  
% 3.03/0.99  --preprocessing_flag                    true
% 3.03/0.99  --time_out_prep_mult                    0.1
% 3.03/0.99  --splitting_mode                        input
% 3.03/0.99  --splitting_grd                         true
% 3.03/0.99  --splitting_cvd                         false
% 3.03/0.99  --splitting_cvd_svl                     false
% 3.03/0.99  --splitting_nvd                         32
% 3.03/0.99  --sub_typing                            true
% 3.03/0.99  --prep_gs_sim                           true
% 3.03/0.99  --prep_unflatten                        true
% 3.03/0.99  --prep_res_sim                          true
% 3.03/0.99  --prep_upred                            true
% 3.03/0.99  --prep_sem_filter                       exhaustive
% 3.03/0.99  --prep_sem_filter_out                   false
% 3.03/0.99  --pred_elim                             true
% 3.03/0.99  --res_sim_input                         true
% 3.03/0.99  --eq_ax_congr_red                       true
% 3.03/0.99  --pure_diseq_elim                       true
% 3.03/0.99  --brand_transform                       false
% 3.03/0.99  --non_eq_to_eq                          false
% 3.03/0.99  --prep_def_merge                        true
% 3.03/0.99  --prep_def_merge_prop_impl              false
% 3.03/0.99  --prep_def_merge_mbd                    true
% 3.03/0.99  --prep_def_merge_tr_red                 false
% 3.03/0.99  --prep_def_merge_tr_cl                  false
% 3.03/0.99  --smt_preprocessing                     true
% 3.03/0.99  --smt_ac_axioms                         fast
% 3.03/0.99  --preprocessed_out                      false
% 3.03/0.99  --preprocessed_stats                    false
% 3.03/0.99  
% 3.03/0.99  ------ Abstraction refinement Options
% 3.03/0.99  
% 3.03/0.99  --abstr_ref                             []
% 3.03/0.99  --abstr_ref_prep                        false
% 3.03/0.99  --abstr_ref_until_sat                   false
% 3.03/0.99  --abstr_ref_sig_restrict                funpre
% 3.03/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.03/0.99  --abstr_ref_under                       []
% 3.03/0.99  
% 3.03/0.99  ------ SAT Options
% 3.03/0.99  
% 3.03/0.99  --sat_mode                              false
% 3.03/0.99  --sat_fm_restart_options                ""
% 3.03/0.99  --sat_gr_def                            false
% 3.03/0.99  --sat_epr_types                         true
% 3.03/0.99  --sat_non_cyclic_types                  false
% 3.03/0.99  --sat_finite_models                     false
% 3.03/0.99  --sat_fm_lemmas                         false
% 3.03/0.99  --sat_fm_prep                           false
% 3.03/0.99  --sat_fm_uc_incr                        true
% 3.03/0.99  --sat_out_model                         small
% 3.03/0.99  --sat_out_clauses                       false
% 3.03/0.99  
% 3.03/0.99  ------ QBF Options
% 3.03/0.99  
% 3.03/0.99  --qbf_mode                              false
% 3.03/0.99  --qbf_elim_univ                         false
% 3.03/0.99  --qbf_dom_inst                          none
% 3.03/0.99  --qbf_dom_pre_inst                      false
% 3.03/0.99  --qbf_sk_in                             false
% 3.03/0.99  --qbf_pred_elim                         true
% 3.03/0.99  --qbf_split                             512
% 3.03/0.99  
% 3.03/0.99  ------ BMC1 Options
% 3.03/0.99  
% 3.03/0.99  --bmc1_incremental                      false
% 3.03/0.99  --bmc1_axioms                           reachable_all
% 3.03/0.99  --bmc1_min_bound                        0
% 3.03/0.99  --bmc1_max_bound                        -1
% 3.03/0.99  --bmc1_max_bound_default                -1
% 3.03/0.99  --bmc1_symbol_reachability              true
% 3.03/0.99  --bmc1_property_lemmas                  false
% 3.03/0.99  --bmc1_k_induction                      false
% 3.03/0.99  --bmc1_non_equiv_states                 false
% 3.03/0.99  --bmc1_deadlock                         false
% 3.03/0.99  --bmc1_ucm                              false
% 3.03/0.99  --bmc1_add_unsat_core                   none
% 3.03/0.99  --bmc1_unsat_core_children              false
% 3.03/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.03/0.99  --bmc1_out_stat                         full
% 3.03/0.99  --bmc1_ground_init                      false
% 3.03/0.99  --bmc1_pre_inst_next_state              false
% 3.03/0.99  --bmc1_pre_inst_state                   false
% 3.03/0.99  --bmc1_pre_inst_reach_state             false
% 3.03/0.99  --bmc1_out_unsat_core                   false
% 3.03/0.99  --bmc1_aig_witness_out                  false
% 3.03/0.99  --bmc1_verbose                          false
% 3.03/0.99  --bmc1_dump_clauses_tptp                false
% 3.03/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.03/0.99  --bmc1_dump_file                        -
% 3.03/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.03/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.03/0.99  --bmc1_ucm_extend_mode                  1
% 3.03/0.99  --bmc1_ucm_init_mode                    2
% 3.03/0.99  --bmc1_ucm_cone_mode                    none
% 3.03/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.03/0.99  --bmc1_ucm_relax_model                  4
% 3.03/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.03/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.03/0.99  --bmc1_ucm_layered_model                none
% 3.03/0.99  --bmc1_ucm_max_lemma_size               10
% 3.03/0.99  
% 3.03/0.99  ------ AIG Options
% 3.03/0.99  
% 3.03/0.99  --aig_mode                              false
% 3.03/0.99  
% 3.03/0.99  ------ Instantiation Options
% 3.03/0.99  
% 3.03/0.99  --instantiation_flag                    true
% 3.03/0.99  --inst_sos_flag                         false
% 3.03/0.99  --inst_sos_phase                        true
% 3.03/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.03/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.03/0.99  --inst_lit_sel_side                     num_symb
% 3.03/0.99  --inst_solver_per_active                1400
% 3.03/0.99  --inst_solver_calls_frac                1.
% 3.03/0.99  --inst_passive_queue_type               priority_queues
% 3.03/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.03/0.99  --inst_passive_queues_freq              [25;2]
% 3.03/0.99  --inst_dismatching                      true
% 3.03/0.99  --inst_eager_unprocessed_to_passive     true
% 3.03/0.99  --inst_prop_sim_given                   true
% 3.03/0.99  --inst_prop_sim_new                     false
% 3.03/0.99  --inst_subs_new                         false
% 3.03/0.99  --inst_eq_res_simp                      false
% 3.03/0.99  --inst_subs_given                       false
% 3.03/0.99  --inst_orphan_elimination               true
% 3.03/0.99  --inst_learning_loop_flag               true
% 3.03/0.99  --inst_learning_start                   3000
% 3.03/0.99  --inst_learning_factor                  2
% 3.03/0.99  --inst_start_prop_sim_after_learn       3
% 3.03/0.99  --inst_sel_renew                        solver
% 3.03/0.99  --inst_lit_activity_flag                true
% 3.03/0.99  --inst_restr_to_given                   false
% 3.03/0.99  --inst_activity_threshold               500
% 3.03/0.99  --inst_out_proof                        true
% 3.03/0.99  
% 3.03/0.99  ------ Resolution Options
% 3.03/0.99  
% 3.03/0.99  --resolution_flag                       true
% 3.03/0.99  --res_lit_sel                           adaptive
% 3.03/0.99  --res_lit_sel_side                      none
% 3.03/0.99  --res_ordering                          kbo
% 3.03/0.99  --res_to_prop_solver                    active
% 3.03/0.99  --res_prop_simpl_new                    false
% 3.03/0.99  --res_prop_simpl_given                  true
% 3.03/0.99  --res_passive_queue_type                priority_queues
% 3.03/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.03/0.99  --res_passive_queues_freq               [15;5]
% 3.03/0.99  --res_forward_subs                      full
% 3.03/0.99  --res_backward_subs                     full
% 3.03/0.99  --res_forward_subs_resolution           true
% 3.03/0.99  --res_backward_subs_resolution          true
% 3.03/0.99  --res_orphan_elimination                true
% 3.03/0.99  --res_time_limit                        2.
% 3.03/0.99  --res_out_proof                         true
% 3.03/0.99  
% 3.03/0.99  ------ Superposition Options
% 3.03/0.99  
% 3.03/0.99  --superposition_flag                    true
% 3.03/0.99  --sup_passive_queue_type                priority_queues
% 3.03/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.03/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.03/0.99  --demod_completeness_check              fast
% 3.03/0.99  --demod_use_ground                      true
% 3.03/0.99  --sup_to_prop_solver                    passive
% 3.03/0.99  --sup_prop_simpl_new                    true
% 3.03/0.99  --sup_prop_simpl_given                  true
% 3.03/0.99  --sup_fun_splitting                     false
% 3.03/0.99  --sup_smt_interval                      50000
% 3.03/0.99  
% 3.03/0.99  ------ Superposition Simplification Setup
% 3.03/0.99  
% 3.03/0.99  --sup_indices_passive                   []
% 3.03/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.03/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.99  --sup_full_bw                           [BwDemod]
% 3.03/0.99  --sup_immed_triv                        [TrivRules]
% 3.03/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.03/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.99  --sup_immed_bw_main                     []
% 3.03/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.03/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/0.99  
% 3.03/0.99  ------ Combination Options
% 3.03/0.99  
% 3.03/0.99  --comb_res_mult                         3
% 3.03/0.99  --comb_sup_mult                         2
% 3.03/0.99  --comb_inst_mult                        10
% 3.03/0.99  
% 3.03/0.99  ------ Debug Options
% 3.03/0.99  
% 3.03/0.99  --dbg_backtrace                         false
% 3.03/0.99  --dbg_dump_prop_clauses                 false
% 3.03/0.99  --dbg_dump_prop_clauses_file            -
% 3.03/0.99  --dbg_out_stat                          false
% 3.03/0.99  ------ Parsing...
% 3.03/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.03/0.99  
% 3.03/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.03/0.99  
% 3.03/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.03/0.99  
% 3.03/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.03/0.99  ------ Proving...
% 3.03/0.99  ------ Problem Properties 
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  clauses                                 28
% 3.03/0.99  conjectures                             5
% 3.03/0.99  EPR                                     2
% 3.03/0.99  Horn                                    28
% 3.03/0.99  unary                                   9
% 3.03/0.99  binary                                  4
% 3.03/0.99  lits                                    88
% 3.03/0.99  lits eq                                 18
% 3.03/0.99  fd_pure                                 0
% 3.03/0.99  fd_pseudo                               0
% 3.03/0.99  fd_cond                                 0
% 3.03/0.99  fd_pseudo_cond                          1
% 3.03/0.99  AC symbols                              0
% 3.03/0.99  
% 3.03/0.99  ------ Schedule dynamic 5 is on 
% 3.03/0.99  
% 3.03/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  ------ 
% 3.03/0.99  Current options:
% 3.03/0.99  ------ 
% 3.03/0.99  
% 3.03/0.99  ------ Input Options
% 3.03/0.99  
% 3.03/0.99  --out_options                           all
% 3.03/0.99  --tptp_safe_out                         true
% 3.03/0.99  --problem_path                          ""
% 3.03/0.99  --include_path                          ""
% 3.03/0.99  --clausifier                            res/vclausify_rel
% 3.03/0.99  --clausifier_options                    --mode clausify
% 3.03/0.99  --stdin                                 false
% 3.03/0.99  --stats_out                             all
% 3.03/0.99  
% 3.03/0.99  ------ General Options
% 3.03/0.99  
% 3.03/0.99  --fof                                   false
% 3.03/0.99  --time_out_real                         305.
% 3.03/0.99  --time_out_virtual                      -1.
% 3.03/0.99  --symbol_type_check                     false
% 3.03/0.99  --clausify_out                          false
% 3.03/0.99  --sig_cnt_out                           false
% 3.03/0.99  --trig_cnt_out                          false
% 3.03/0.99  --trig_cnt_out_tolerance                1.
% 3.03/0.99  --trig_cnt_out_sk_spl                   false
% 3.03/0.99  --abstr_cl_out                          false
% 3.03/0.99  
% 3.03/0.99  ------ Global Options
% 3.03/0.99  
% 3.03/0.99  --schedule                              default
% 3.03/0.99  --add_important_lit                     false
% 3.03/0.99  --prop_solver_per_cl                    1000
% 3.03/0.99  --min_unsat_core                        false
% 3.03/0.99  --soft_assumptions                      false
% 3.03/0.99  --soft_lemma_size                       3
% 3.03/0.99  --prop_impl_unit_size                   0
% 3.03/0.99  --prop_impl_unit                        []
% 3.03/0.99  --share_sel_clauses                     true
% 3.03/0.99  --reset_solvers                         false
% 3.03/0.99  --bc_imp_inh                            [conj_cone]
% 3.03/0.99  --conj_cone_tolerance                   3.
% 3.03/0.99  --extra_neg_conj                        none
% 3.03/0.99  --large_theory_mode                     true
% 3.03/0.99  --prolific_symb_bound                   200
% 3.03/0.99  --lt_threshold                          2000
% 3.03/0.99  --clause_weak_htbl                      true
% 3.03/0.99  --gc_record_bc_elim                     false
% 3.03/0.99  
% 3.03/0.99  ------ Preprocessing Options
% 3.03/0.99  
% 3.03/0.99  --preprocessing_flag                    true
% 3.03/0.99  --time_out_prep_mult                    0.1
% 3.03/0.99  --splitting_mode                        input
% 3.03/0.99  --splitting_grd                         true
% 3.03/0.99  --splitting_cvd                         false
% 3.03/0.99  --splitting_cvd_svl                     false
% 3.03/0.99  --splitting_nvd                         32
% 3.03/0.99  --sub_typing                            true
% 3.03/0.99  --prep_gs_sim                           true
% 3.03/0.99  --prep_unflatten                        true
% 3.03/0.99  --prep_res_sim                          true
% 3.03/0.99  --prep_upred                            true
% 3.03/0.99  --prep_sem_filter                       exhaustive
% 3.03/0.99  --prep_sem_filter_out                   false
% 3.03/0.99  --pred_elim                             true
% 3.03/0.99  --res_sim_input                         true
% 3.03/0.99  --eq_ax_congr_red                       true
% 3.03/0.99  --pure_diseq_elim                       true
% 3.03/0.99  --brand_transform                       false
% 3.03/0.99  --non_eq_to_eq                          false
% 3.03/0.99  --prep_def_merge                        true
% 3.03/0.99  --prep_def_merge_prop_impl              false
% 3.03/0.99  --prep_def_merge_mbd                    true
% 3.03/0.99  --prep_def_merge_tr_red                 false
% 3.03/0.99  --prep_def_merge_tr_cl                  false
% 3.03/0.99  --smt_preprocessing                     true
% 3.03/0.99  --smt_ac_axioms                         fast
% 3.03/0.99  --preprocessed_out                      false
% 3.03/0.99  --preprocessed_stats                    false
% 3.03/0.99  
% 3.03/0.99  ------ Abstraction refinement Options
% 3.03/0.99  
% 3.03/0.99  --abstr_ref                             []
% 3.03/0.99  --abstr_ref_prep                        false
% 3.03/0.99  --abstr_ref_until_sat                   false
% 3.03/0.99  --abstr_ref_sig_restrict                funpre
% 3.03/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.03/0.99  --abstr_ref_under                       []
% 3.03/0.99  
% 3.03/0.99  ------ SAT Options
% 3.03/0.99  
% 3.03/0.99  --sat_mode                              false
% 3.03/0.99  --sat_fm_restart_options                ""
% 3.03/0.99  --sat_gr_def                            false
% 3.03/0.99  --sat_epr_types                         true
% 3.03/0.99  --sat_non_cyclic_types                  false
% 3.03/0.99  --sat_finite_models                     false
% 3.03/0.99  --sat_fm_lemmas                         false
% 3.03/0.99  --sat_fm_prep                           false
% 3.03/0.99  --sat_fm_uc_incr                        true
% 3.03/0.99  --sat_out_model                         small
% 3.03/0.99  --sat_out_clauses                       false
% 3.03/0.99  
% 3.03/0.99  ------ QBF Options
% 3.03/0.99  
% 3.03/0.99  --qbf_mode                              false
% 3.03/0.99  --qbf_elim_univ                         false
% 3.03/0.99  --qbf_dom_inst                          none
% 3.03/0.99  --qbf_dom_pre_inst                      false
% 3.03/0.99  --qbf_sk_in                             false
% 3.03/0.99  --qbf_pred_elim                         true
% 3.03/0.99  --qbf_split                             512
% 3.03/0.99  
% 3.03/0.99  ------ BMC1 Options
% 3.03/0.99  
% 3.03/0.99  --bmc1_incremental                      false
% 3.03/0.99  --bmc1_axioms                           reachable_all
% 3.03/0.99  --bmc1_min_bound                        0
% 3.03/0.99  --bmc1_max_bound                        -1
% 3.03/0.99  --bmc1_max_bound_default                -1
% 3.03/0.99  --bmc1_symbol_reachability              true
% 3.03/0.99  --bmc1_property_lemmas                  false
% 3.03/0.99  --bmc1_k_induction                      false
% 3.03/0.99  --bmc1_non_equiv_states                 false
% 3.03/0.99  --bmc1_deadlock                         false
% 3.03/0.99  --bmc1_ucm                              false
% 3.03/0.99  --bmc1_add_unsat_core                   none
% 3.03/0.99  --bmc1_unsat_core_children              false
% 3.03/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.03/0.99  --bmc1_out_stat                         full
% 3.03/0.99  --bmc1_ground_init                      false
% 3.03/0.99  --bmc1_pre_inst_next_state              false
% 3.03/0.99  --bmc1_pre_inst_state                   false
% 3.03/0.99  --bmc1_pre_inst_reach_state             false
% 3.03/0.99  --bmc1_out_unsat_core                   false
% 3.03/0.99  --bmc1_aig_witness_out                  false
% 3.03/0.99  --bmc1_verbose                          false
% 3.03/0.99  --bmc1_dump_clauses_tptp                false
% 3.03/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.03/0.99  --bmc1_dump_file                        -
% 3.03/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.03/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.03/0.99  --bmc1_ucm_extend_mode                  1
% 3.03/0.99  --bmc1_ucm_init_mode                    2
% 3.03/0.99  --bmc1_ucm_cone_mode                    none
% 3.03/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.03/0.99  --bmc1_ucm_relax_model                  4
% 3.03/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.03/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.03/0.99  --bmc1_ucm_layered_model                none
% 3.03/0.99  --bmc1_ucm_max_lemma_size               10
% 3.03/0.99  
% 3.03/0.99  ------ AIG Options
% 3.03/0.99  
% 3.03/0.99  --aig_mode                              false
% 3.03/0.99  
% 3.03/0.99  ------ Instantiation Options
% 3.03/0.99  
% 3.03/0.99  --instantiation_flag                    true
% 3.03/0.99  --inst_sos_flag                         false
% 3.03/0.99  --inst_sos_phase                        true
% 3.03/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.03/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.03/0.99  --inst_lit_sel_side                     none
% 3.03/0.99  --inst_solver_per_active                1400
% 3.03/0.99  --inst_solver_calls_frac                1.
% 3.03/0.99  --inst_passive_queue_type               priority_queues
% 3.03/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.03/0.99  --inst_passive_queues_freq              [25;2]
% 3.03/0.99  --inst_dismatching                      true
% 3.03/0.99  --inst_eager_unprocessed_to_passive     true
% 3.03/0.99  --inst_prop_sim_given                   true
% 3.03/0.99  --inst_prop_sim_new                     false
% 3.03/0.99  --inst_subs_new                         false
% 3.03/0.99  --inst_eq_res_simp                      false
% 3.03/0.99  --inst_subs_given                       false
% 3.03/0.99  --inst_orphan_elimination               true
% 3.03/0.99  --inst_learning_loop_flag               true
% 3.03/0.99  --inst_learning_start                   3000
% 3.03/0.99  --inst_learning_factor                  2
% 3.03/0.99  --inst_start_prop_sim_after_learn       3
% 3.03/0.99  --inst_sel_renew                        solver
% 3.03/0.99  --inst_lit_activity_flag                true
% 3.03/0.99  --inst_restr_to_given                   false
% 3.03/0.99  --inst_activity_threshold               500
% 3.03/0.99  --inst_out_proof                        true
% 3.03/0.99  
% 3.03/0.99  ------ Resolution Options
% 3.03/0.99  
% 3.03/0.99  --resolution_flag                       false
% 3.03/0.99  --res_lit_sel                           adaptive
% 3.03/0.99  --res_lit_sel_side                      none
% 3.03/0.99  --res_ordering                          kbo
% 3.03/0.99  --res_to_prop_solver                    active
% 3.03/0.99  --res_prop_simpl_new                    false
% 3.03/0.99  --res_prop_simpl_given                  true
% 3.03/0.99  --res_passive_queue_type                priority_queues
% 3.03/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.03/0.99  --res_passive_queues_freq               [15;5]
% 3.03/0.99  --res_forward_subs                      full
% 3.03/0.99  --res_backward_subs                     full
% 3.03/0.99  --res_forward_subs_resolution           true
% 3.03/0.99  --res_backward_subs_resolution          true
% 3.03/0.99  --res_orphan_elimination                true
% 3.03/0.99  --res_time_limit                        2.
% 3.03/0.99  --res_out_proof                         true
% 3.03/0.99  
% 3.03/0.99  ------ Superposition Options
% 3.03/0.99  
% 3.03/0.99  --superposition_flag                    true
% 3.03/0.99  --sup_passive_queue_type                priority_queues
% 3.03/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.03/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.03/0.99  --demod_completeness_check              fast
% 3.03/0.99  --demod_use_ground                      true
% 3.03/0.99  --sup_to_prop_solver                    passive
% 3.03/0.99  --sup_prop_simpl_new                    true
% 3.03/0.99  --sup_prop_simpl_given                  true
% 3.03/0.99  --sup_fun_splitting                     false
% 3.03/0.99  --sup_smt_interval                      50000
% 3.03/0.99  
% 3.03/0.99  ------ Superposition Simplification Setup
% 3.03/0.99  
% 3.03/0.99  --sup_indices_passive                   []
% 3.03/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.03/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.03/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.99  --sup_full_bw                           [BwDemod]
% 3.03/0.99  --sup_immed_triv                        [TrivRules]
% 3.03/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.03/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.99  --sup_immed_bw_main                     []
% 3.03/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.03/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.03/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.03/0.99  
% 3.03/0.99  ------ Combination Options
% 3.03/0.99  
% 3.03/0.99  --comb_res_mult                         3
% 3.03/0.99  --comb_sup_mult                         2
% 3.03/0.99  --comb_inst_mult                        10
% 3.03/0.99  
% 3.03/0.99  ------ Debug Options
% 3.03/0.99  
% 3.03/0.99  --dbg_backtrace                         false
% 3.03/0.99  --dbg_dump_prop_clauses                 false
% 3.03/0.99  --dbg_dump_prop_clauses_file            -
% 3.03/0.99  --dbg_out_stat                          false
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  ------ Proving...
% 3.03/0.99  
% 3.03/0.99  
% 3.03/0.99  % SZS status Theorem for theBenchmark.p
% 3.03/0.99  
% 3.03/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.03/0.99  
% 3.03/0.99  fof(f18,conjecture,(
% 3.03/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f19,negated_conjecture,(
% 3.03/1.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 3.03/1.00    inference(negated_conjecture,[],[f18])).
% 3.03/1.00  
% 3.03/1.00  fof(f48,plain,(
% 3.03/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 3.03/1.00    inference(ennf_transformation,[],[f19])).
% 3.03/1.00  
% 3.03/1.00  fof(f49,plain,(
% 3.03/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 3.03/1.00    inference(flattening,[],[f48])).
% 3.03/1.00  
% 3.03/1.00  fof(f53,plain,(
% 3.03/1.00    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 3.03/1.00    introduced(choice_axiom,[])).
% 3.03/1.00  
% 3.03/1.00  fof(f52,plain,(
% 3.03/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 3.03/1.00    introduced(choice_axiom,[])).
% 3.03/1.00  
% 3.03/1.00  fof(f51,plain,(
% 3.03/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 3.03/1.00    introduced(choice_axiom,[])).
% 3.03/1.00  
% 3.03/1.00  fof(f54,plain,(
% 3.03/1.00    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 3.03/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f53,f52,f51])).
% 3.03/1.00  
% 3.03/1.00  fof(f86,plain,(
% 3.03/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.03/1.00    inference(cnf_transformation,[],[f54])).
% 3.03/1.00  
% 3.03/1.00  fof(f15,axiom,(
% 3.03/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f43,plain,(
% 3.03/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.03/1.00    inference(ennf_transformation,[],[f15])).
% 3.03/1.00  
% 3.03/1.00  fof(f78,plain,(
% 3.03/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f43])).
% 3.03/1.00  
% 3.03/1.00  fof(f81,plain,(
% 3.03/1.00    l1_struct_0(sK0)),
% 3.03/1.00    inference(cnf_transformation,[],[f54])).
% 3.03/1.00  
% 3.03/1.00  fof(f83,plain,(
% 3.03/1.00    l1_struct_0(sK1)),
% 3.03/1.00    inference(cnf_transformation,[],[f54])).
% 3.03/1.00  
% 3.03/1.00  fof(f11,axiom,(
% 3.03/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f35,plain,(
% 3.03/1.00    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.03/1.00    inference(ennf_transformation,[],[f11])).
% 3.03/1.00  
% 3.03/1.00  fof(f36,plain,(
% 3.03/1.00    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.03/1.00    inference(flattening,[],[f35])).
% 3.03/1.00  
% 3.03/1.00  fof(f71,plain,(
% 3.03/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f36])).
% 3.03/1.00  
% 3.03/1.00  fof(f16,axiom,(
% 3.03/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f44,plain,(
% 3.03/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.03/1.00    inference(ennf_transformation,[],[f16])).
% 3.03/1.00  
% 3.03/1.00  fof(f45,plain,(
% 3.03/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.03/1.00    inference(flattening,[],[f44])).
% 3.03/1.00  
% 3.03/1.00  fof(f79,plain,(
% 3.03/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f45])).
% 3.03/1.00  
% 3.03/1.00  fof(f82,plain,(
% 3.03/1.00    ~v2_struct_0(sK1)),
% 3.03/1.00    inference(cnf_transformation,[],[f54])).
% 3.03/1.00  
% 3.03/1.00  fof(f9,axiom,(
% 3.03/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f20,plain,(
% 3.03/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.03/1.00    inference(pure_predicate_removal,[],[f9])).
% 3.03/1.00  
% 3.03/1.00  fof(f33,plain,(
% 3.03/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/1.00    inference(ennf_transformation,[],[f20])).
% 3.03/1.00  
% 3.03/1.00  fof(f68,plain,(
% 3.03/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/1.00    inference(cnf_transformation,[],[f33])).
% 3.03/1.00  
% 3.03/1.00  fof(f12,axiom,(
% 3.03/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f37,plain,(
% 3.03/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.03/1.00    inference(ennf_transformation,[],[f12])).
% 3.03/1.00  
% 3.03/1.00  fof(f38,plain,(
% 3.03/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.03/1.00    inference(flattening,[],[f37])).
% 3.03/1.00  
% 3.03/1.00  fof(f50,plain,(
% 3.03/1.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.03/1.00    inference(nnf_transformation,[],[f38])).
% 3.03/1.00  
% 3.03/1.00  fof(f72,plain,(
% 3.03/1.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f50])).
% 3.03/1.00  
% 3.03/1.00  fof(f8,axiom,(
% 3.03/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f32,plain,(
% 3.03/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/1.00    inference(ennf_transformation,[],[f8])).
% 3.03/1.00  
% 3.03/1.00  fof(f67,plain,(
% 3.03/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/1.00    inference(cnf_transformation,[],[f32])).
% 3.03/1.00  
% 3.03/1.00  fof(f84,plain,(
% 3.03/1.00    v1_funct_1(sK2)),
% 3.03/1.00    inference(cnf_transformation,[],[f54])).
% 3.03/1.00  
% 3.03/1.00  fof(f85,plain,(
% 3.03/1.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.03/1.00    inference(cnf_transformation,[],[f54])).
% 3.03/1.00  
% 3.03/1.00  fof(f1,axiom,(
% 3.03/1.00    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f21,plain,(
% 3.03/1.00    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.03/1.00    inference(ennf_transformation,[],[f1])).
% 3.03/1.00  
% 3.03/1.00  fof(f55,plain,(
% 3.03/1.00    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f21])).
% 3.03/1.00  
% 3.03/1.00  fof(f5,axiom,(
% 3.03/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f26,plain,(
% 3.03/1.00    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.03/1.00    inference(ennf_transformation,[],[f5])).
% 3.03/1.00  
% 3.03/1.00  fof(f27,plain,(
% 3.03/1.00    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.03/1.00    inference(flattening,[],[f26])).
% 3.03/1.00  
% 3.03/1.00  fof(f63,plain,(
% 3.03/1.00    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f27])).
% 3.03/1.00  
% 3.03/1.00  fof(f2,axiom,(
% 3.03/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f22,plain,(
% 3.03/1.00    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.03/1.00    inference(ennf_transformation,[],[f2])).
% 3.03/1.00  
% 3.03/1.00  fof(f23,plain,(
% 3.03/1.00    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.03/1.00    inference(flattening,[],[f22])).
% 3.03/1.00  
% 3.03/1.00  fof(f57,plain,(
% 3.03/1.00    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f23])).
% 3.03/1.00  
% 3.03/1.00  fof(f88,plain,(
% 3.03/1.00    v2_funct_1(sK2)),
% 3.03/1.00    inference(cnf_transformation,[],[f54])).
% 3.03/1.00  
% 3.03/1.00  fof(f3,axiom,(
% 3.03/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f24,plain,(
% 3.03/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.03/1.00    inference(ennf_transformation,[],[f3])).
% 3.03/1.00  
% 3.03/1.00  fof(f25,plain,(
% 3.03/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.03/1.00    inference(flattening,[],[f24])).
% 3.03/1.00  
% 3.03/1.00  fof(f59,plain,(
% 3.03/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f25])).
% 3.03/1.00  
% 3.03/1.00  fof(f58,plain,(
% 3.03/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f25])).
% 3.03/1.00  
% 3.03/1.00  fof(f6,axiom,(
% 3.03/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f28,plain,(
% 3.03/1.00    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.03/1.00    inference(ennf_transformation,[],[f6])).
% 3.03/1.00  
% 3.03/1.00  fof(f29,plain,(
% 3.03/1.00    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.03/1.00    inference(flattening,[],[f28])).
% 3.03/1.00  
% 3.03/1.00  fof(f64,plain,(
% 3.03/1.00    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f29])).
% 3.03/1.00  
% 3.03/1.00  fof(f4,axiom,(
% 3.03/1.00    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f61,plain,(
% 3.03/1.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.03/1.00    inference(cnf_transformation,[],[f4])).
% 3.03/1.00  
% 3.03/1.00  fof(f10,axiom,(
% 3.03/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f34,plain,(
% 3.03/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.03/1.00    inference(ennf_transformation,[],[f10])).
% 3.03/1.00  
% 3.03/1.00  fof(f69,plain,(
% 3.03/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.03/1.00    inference(cnf_transformation,[],[f34])).
% 3.03/1.00  
% 3.03/1.00  fof(f87,plain,(
% 3.03/1.00    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 3.03/1.00    inference(cnf_transformation,[],[f54])).
% 3.03/1.00  
% 3.03/1.00  fof(f14,axiom,(
% 3.03/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f41,plain,(
% 3.03/1.00    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.03/1.00    inference(ennf_transformation,[],[f14])).
% 3.03/1.00  
% 3.03/1.00  fof(f42,plain,(
% 3.03/1.00    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.03/1.00    inference(flattening,[],[f41])).
% 3.03/1.00  
% 3.03/1.00  fof(f77,plain,(
% 3.03/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f42])).
% 3.03/1.00  
% 3.03/1.00  fof(f56,plain,(
% 3.03/1.00    ( ! [X0] : (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f21])).
% 3.03/1.00  
% 3.03/1.00  fof(f17,axiom,(
% 3.03/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f46,plain,(
% 3.03/1.00    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.03/1.00    inference(ennf_transformation,[],[f17])).
% 3.03/1.00  
% 3.03/1.00  fof(f47,plain,(
% 3.03/1.00    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.03/1.00    inference(flattening,[],[f46])).
% 3.03/1.00  
% 3.03/1.00  fof(f80,plain,(
% 3.03/1.00    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f47])).
% 3.03/1.00  
% 3.03/1.00  fof(f7,axiom,(
% 3.03/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f30,plain,(
% 3.03/1.00    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.03/1.00    inference(ennf_transformation,[],[f7])).
% 3.03/1.00  
% 3.03/1.00  fof(f31,plain,(
% 3.03/1.00    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.03/1.00    inference(flattening,[],[f30])).
% 3.03/1.00  
% 3.03/1.00  fof(f66,plain,(
% 3.03/1.00    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f31])).
% 3.03/1.00  
% 3.03/1.00  fof(f76,plain,(
% 3.03/1.00    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f42])).
% 3.03/1.00  
% 3.03/1.00  fof(f13,axiom,(
% 3.03/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 3.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.03/1.00  
% 3.03/1.00  fof(f39,plain,(
% 3.03/1.00    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.03/1.00    inference(ennf_transformation,[],[f13])).
% 3.03/1.00  
% 3.03/1.00  fof(f40,plain,(
% 3.03/1.00    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.03/1.00    inference(flattening,[],[f39])).
% 3.03/1.00  
% 3.03/1.00  fof(f74,plain,(
% 3.03/1.00    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.03/1.00    inference(cnf_transformation,[],[f40])).
% 3.03/1.00  
% 3.03/1.00  fof(f89,plain,(
% 3.03/1.00    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 3.03/1.00    inference(cnf_transformation,[],[f54])).
% 3.03/1.00  
% 3.03/1.00  cnf(c_29,negated_conjecture,
% 3.03/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.03/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_716,negated_conjecture,
% 3.03/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_29]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1255,plain,
% 3.03/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_716]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_23,plain,
% 3.03/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_34,negated_conjecture,
% 3.03/1.00      ( l1_struct_0(sK0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_405,plain,
% 3.03/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 3.03/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_34]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_406,plain,
% 3.03/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.03/1.00      inference(unflattening,[status(thm)],[c_405]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_711,plain,
% 3.03/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_406]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_32,negated_conjecture,
% 3.03/1.00      ( l1_struct_0(sK1) ),
% 3.03/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_400,plain,
% 3.03/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 3.03/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_32]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_401,plain,
% 3.03/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.03/1.00      inference(unflattening,[status(thm)],[c_400]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_712,plain,
% 3.03/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_401]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1280,plain,
% 3.03/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 3.03/1.00      inference(light_normalisation,[status(thm)],[c_1255,c_711,c_712]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_15,plain,
% 3.03/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.03/1.00      | v1_partfun1(X0,X1)
% 3.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/1.00      | v1_xboole_0(X2)
% 3.03/1.00      | ~ v1_funct_1(X0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_24,plain,
% 3.03/1.00      ( v2_struct_0(X0)
% 3.03/1.00      | ~ l1_struct_0(X0)
% 3.03/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.03/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_33,negated_conjecture,
% 3.03/1.00      ( ~ v2_struct_0(sK1) ),
% 3.03/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_387,plain,
% 3.03/1.00      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 3.03/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_33]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_388,plain,
% 3.03/1.00      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 3.03/1.00      inference(unflattening,[status(thm)],[c_387]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_47,plain,
% 3.03/1.00      ( v2_struct_0(sK1)
% 3.03/1.00      | ~ l1_struct_0(sK1)
% 3.03/1.00      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_390,plain,
% 3.03/1.00      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_388,c_33,c_32,c_47]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_412,plain,
% 3.03/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.03/1.00      | v1_partfun1(X0,X1)
% 3.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/1.00      | ~ v1_funct_1(X0)
% 3.03/1.00      | u1_struct_0(sK1) != X2 ),
% 3.03/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_390]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_413,plain,
% 3.03/1.00      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 3.03/1.00      | v1_partfun1(X0,X1)
% 3.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 3.03/1.00      | ~ v1_funct_1(X0) ),
% 3.03/1.00      inference(unflattening,[status(thm)],[c_412]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_13,plain,
% 3.03/1.00      ( v4_relat_1(X0,X1)
% 3.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.03/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_18,plain,
% 3.03/1.00      ( ~ v1_partfun1(X0,X1)
% 3.03/1.00      | ~ v4_relat_1(X0,X1)
% 3.03/1.00      | ~ v1_relat_1(X0)
% 3.03/1.00      | k1_relat_1(X0) = X1 ),
% 3.03/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_470,plain,
% 3.03/1.00      ( ~ v1_partfun1(X0,X1)
% 3.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/1.00      | ~ v1_relat_1(X0)
% 3.03/1.00      | k1_relat_1(X0) = X1 ),
% 3.03/1.00      inference(resolution,[status(thm)],[c_13,c_18]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_12,plain,
% 3.03/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/1.00      | v1_relat_1(X0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_474,plain,
% 3.03/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/1.00      | ~ v1_partfun1(X0,X1)
% 3.03/1.00      | k1_relat_1(X0) = X1 ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_470,c_18,c_13,c_12]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_475,plain,
% 3.03/1.00      ( ~ v1_partfun1(X0,X1)
% 3.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/1.00      | k1_relat_1(X0) = X1 ),
% 3.03/1.00      inference(renaming,[status(thm)],[c_474]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_514,plain,
% 3.03/1.00      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 3.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 3.03/1.00      | ~ v1_funct_1(X0)
% 3.03/1.00      | k1_relat_1(X0) = X1 ),
% 3.03/1.00      inference(resolution,[status(thm)],[c_413,c_475]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_709,plain,
% 3.03/1.00      ( ~ v1_funct_2(X0_54,X0_55,u1_struct_0(sK1))
% 3.03/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.03/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,u1_struct_0(sK1))))
% 3.03/1.00      | ~ v1_funct_1(X0_54)
% 3.03/1.00      | k1_relat_1(X0_54) = X0_55 ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_514]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1261,plain,
% 3.03/1.00      ( k1_relat_1(X0_54) = X0_55
% 3.03/1.00      | v1_funct_2(X0_54,X0_55,u1_struct_0(sK1)) != iProver_top
% 3.03/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 3.03/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,u1_struct_0(sK1)))) != iProver_top
% 3.03/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_709]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1358,plain,
% 3.03/1.00      ( k1_relat_1(X0_54) = X0_55
% 3.03/1.00      | v1_funct_2(X0_54,X0_55,k2_struct_0(sK1)) != iProver_top
% 3.03/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 3.03/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,k2_struct_0(sK1)))) != iProver_top
% 3.03/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 3.03/1.00      inference(light_normalisation,[status(thm)],[c_1261,c_712]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1678,plain,
% 3.03/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 3.03/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.03/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_55))) != iProver_top
% 3.03/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_1280,c_1358]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_31,negated_conjecture,
% 3.03/1.00      ( v1_funct_1(sK2) ),
% 3.03/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_38,plain,
% 3.03/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_30,negated_conjecture,
% 3.03/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.03/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_715,negated_conjecture,
% 3.03/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_30]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1256,plain,
% 3.03/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_715]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1274,plain,
% 3.03/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 3.03/1.00      inference(light_normalisation,[status(thm)],[c_1256,c_711,c_712]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1683,plain,
% 3.03/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_55))) != iProver_top
% 3.03/1.00      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_1678,c_38,c_1274]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1684,plain,
% 3.03/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 3.03/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_55))) != iProver_top ),
% 3.03/1.00      inference(renaming,[status(thm)],[c_1683]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1691,plain,
% 3.03/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_1280,c_1684]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1771,plain,
% 3.03/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) = iProver_top ),
% 3.03/1.00      inference(demodulation,[status(thm)],[c_1691,c_1280]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_723,plain,
% 3.03/1.00      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.03/1.00      | v1_relat_1(X0_54) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1249,plain,
% 3.03/1.00      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 3.03/1.00      | v1_relat_1(X0_54) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_723]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1977,plain,
% 3.03/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_1771,c_1249]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1,plain,
% 3.03/1.00      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_734,plain,
% 3.03/1.00      ( ~ v1_relat_1(X0_54)
% 3.03/1.00      | k1_relat_1(k4_relat_1(X0_54)) = k2_relat_1(X0_54) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1238,plain,
% 3.03/1.00      ( k1_relat_1(k4_relat_1(X0_54)) = k2_relat_1(X0_54)
% 3.03/1.00      | v1_relat_1(X0_54) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_734]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2414,plain,
% 3.03/1.00      ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_1977,c_1238]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_7,plain,
% 3.03/1.00      ( ~ v1_funct_1(X0)
% 3.03/1.00      | ~ v1_funct_1(X1)
% 3.03/1.00      | v2_funct_1(X0)
% 3.03/1.00      | ~ v2_funct_1(k5_relat_1(X1,X0))
% 3.03/1.00      | ~ v1_relat_1(X0)
% 3.03/1.00      | ~ v1_relat_1(X1)
% 3.03/1.00      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 3.03/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_728,plain,
% 3.03/1.00      ( ~ v1_funct_1(X0_54)
% 3.03/1.00      | ~ v1_funct_1(X1_54)
% 3.03/1.00      | v2_funct_1(X0_54)
% 3.03/1.00      | ~ v2_funct_1(k5_relat_1(X1_54,X0_54))
% 3.03/1.00      | ~ v1_relat_1(X0_54)
% 3.03/1.00      | ~ v1_relat_1(X1_54)
% 3.03/1.00      | k1_relat_1(X0_54) != k2_relat_1(X1_54) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1244,plain,
% 3.03/1.00      ( k1_relat_1(X0_54) != k2_relat_1(X1_54)
% 3.03/1.00      | v1_funct_1(X0_54) != iProver_top
% 3.03/1.00      | v1_funct_1(X1_54) != iProver_top
% 3.03/1.00      | v2_funct_1(X0_54) = iProver_top
% 3.03/1.00      | v2_funct_1(k5_relat_1(X1_54,X0_54)) != iProver_top
% 3.03/1.00      | v1_relat_1(X0_54) != iProver_top
% 3.03/1.00      | v1_relat_1(X1_54) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3505,plain,
% 3.03/1.00      ( k2_relat_1(X0_54) != k2_relat_1(sK2)
% 3.03/1.00      | v1_funct_1(X0_54) != iProver_top
% 3.03/1.00      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 3.03/1.00      | v2_funct_1(k5_relat_1(X0_54,k4_relat_1(sK2))) != iProver_top
% 3.03/1.00      | v2_funct_1(k4_relat_1(sK2)) = iProver_top
% 3.03/1.00      | v1_relat_1(X0_54) != iProver_top
% 3.03/1.00      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_2414,c_1244]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_40,plain,
% 3.03/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1509,plain,
% 3.03/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.03/1.00      | v1_relat_1(sK2) ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_723]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1510,plain,
% 3.03/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.03/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_1509]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_714,negated_conjecture,
% 3.03/1.00      ( v1_funct_1(sK2) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_31]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1257,plain,
% 3.03/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_714]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2,plain,
% 3.03/1.00      ( ~ v1_funct_1(X0)
% 3.03/1.00      | ~ v2_funct_1(X0)
% 3.03/1.00      | ~ v1_relat_1(X0)
% 3.03/1.00      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_733,plain,
% 3.03/1.00      ( ~ v1_funct_1(X0_54)
% 3.03/1.00      | ~ v2_funct_1(X0_54)
% 3.03/1.00      | ~ v1_relat_1(X0_54)
% 3.03/1.00      | k2_funct_1(X0_54) = k4_relat_1(X0_54) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1239,plain,
% 3.03/1.00      ( k2_funct_1(X0_54) = k4_relat_1(X0_54)
% 3.03/1.00      | v1_funct_1(X0_54) != iProver_top
% 3.03/1.00      | v2_funct_1(X0_54) != iProver_top
% 3.03/1.00      | v1_relat_1(X0_54) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_733]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1605,plain,
% 3.03/1.00      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 3.03/1.00      | v2_funct_1(sK2) != iProver_top
% 3.03/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_1257,c_1239]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_27,negated_conjecture,
% 3.03/1.00      ( v2_funct_1(sK2) ),
% 3.03/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_785,plain,
% 3.03/1.00      ( ~ v1_funct_1(sK2)
% 3.03/1.00      | ~ v2_funct_1(sK2)
% 3.03/1.00      | ~ v1_relat_1(sK2)
% 3.03/1.00      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_733]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1663,plain,
% 3.03/1.00      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_1605,c_31,c_29,c_27,c_785,c_1509]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3,plain,
% 3.03/1.00      ( ~ v1_funct_1(X0)
% 3.03/1.00      | v1_funct_1(k2_funct_1(X0))
% 3.03/1.00      | ~ v1_relat_1(X0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_732,plain,
% 3.03/1.00      ( ~ v1_funct_1(X0_54)
% 3.03/1.00      | v1_funct_1(k2_funct_1(X0_54))
% 3.03/1.00      | ~ v1_relat_1(X0_54) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1240,plain,
% 3.03/1.00      ( v1_funct_1(X0_54) != iProver_top
% 3.03/1.00      | v1_funct_1(k2_funct_1(X0_54)) = iProver_top
% 3.03/1.00      | v1_relat_1(X0_54) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_732]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1921,plain,
% 3.03/1.00      ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
% 3.03/1.00      | v1_funct_1(sK2) != iProver_top
% 3.03/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_1663,c_1240]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4,plain,
% 3.03/1.00      ( ~ v1_funct_1(X0)
% 3.03/1.00      | ~ v1_relat_1(X0)
% 3.03/1.00      | v1_relat_1(k2_funct_1(X0)) ),
% 3.03/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_731,plain,
% 3.03/1.00      ( ~ v1_funct_1(X0_54)
% 3.03/1.00      | ~ v1_relat_1(X0_54)
% 3.03/1.00      | v1_relat_1(k2_funct_1(X0_54)) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1241,plain,
% 3.03/1.00      ( v1_funct_1(X0_54) != iProver_top
% 3.03/1.00      | v1_relat_1(X0_54) != iProver_top
% 3.03/1.00      | v1_relat_1(k2_funct_1(X0_54)) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_731]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1983,plain,
% 3.03/1.00      ( v1_funct_1(sK2) != iProver_top
% 3.03/1.00      | v1_relat_1(k4_relat_1(sK2)) = iProver_top
% 3.03/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_1663,c_1241]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5463,plain,
% 3.03/1.00      ( v1_relat_1(X0_54) != iProver_top
% 3.03/1.00      | v2_funct_1(k4_relat_1(sK2)) = iProver_top
% 3.03/1.00      | v2_funct_1(k5_relat_1(X0_54,k4_relat_1(sK2))) != iProver_top
% 3.03/1.00      | k2_relat_1(X0_54) != k2_relat_1(sK2)
% 3.03/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_3505,c_38,c_40,c_1510,c_1921,c_1983]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5464,plain,
% 3.03/1.00      ( k2_relat_1(X0_54) != k2_relat_1(sK2)
% 3.03/1.00      | v1_funct_1(X0_54) != iProver_top
% 3.03/1.00      | v2_funct_1(k5_relat_1(X0_54,k4_relat_1(sK2))) != iProver_top
% 3.03/1.00      | v2_funct_1(k4_relat_1(sK2)) = iProver_top
% 3.03/1.00      | v1_relat_1(X0_54) != iProver_top ),
% 3.03/1.00      inference(renaming,[status(thm)],[c_5463]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5477,plain,
% 3.03/1.00      ( v1_funct_1(sK2) != iProver_top
% 3.03/1.00      | v2_funct_1(k5_relat_1(sK2,k4_relat_1(sK2))) != iProver_top
% 3.03/1.00      | v2_funct_1(k4_relat_1(sK2)) = iProver_top
% 3.03/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.03/1.00      inference(equality_resolution,[status(thm)],[c_5464]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_10,plain,
% 3.03/1.00      ( ~ v1_funct_1(X0)
% 3.03/1.00      | ~ v2_funct_1(X0)
% 3.03/1.00      | ~ v1_relat_1(X0)
% 3.03/1.00      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
% 3.03/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_725,plain,
% 3.03/1.00      ( ~ v1_funct_1(X0_54)
% 3.03/1.00      | ~ v2_funct_1(X0_54)
% 3.03/1.00      | ~ v1_relat_1(X0_54)
% 3.03/1.00      | k5_relat_1(X0_54,k2_funct_1(X0_54)) = k6_relat_1(k1_relat_1(X0_54)) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1247,plain,
% 3.03/1.00      ( k5_relat_1(X0_54,k2_funct_1(X0_54)) = k6_relat_1(k1_relat_1(X0_54))
% 3.03/1.00      | v1_funct_1(X0_54) != iProver_top
% 3.03/1.00      | v2_funct_1(X0_54) != iProver_top
% 3.03/1.00      | v1_relat_1(X0_54) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_725]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2702,plain,
% 3.03/1.00      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
% 3.03/1.00      | v2_funct_1(sK2) != iProver_top
% 3.03/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_1257,c_1247]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2725,plain,
% 3.03/1.00      ( k5_relat_1(sK2,k4_relat_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
% 3.03/1.00      | v2_funct_1(sK2) != iProver_top
% 3.03/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.03/1.00      inference(light_normalisation,[status(thm)],[c_2702,c_1663]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_41,plain,
% 3.03/1.00      ( v2_funct_1(sK2) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2967,plain,
% 3.03/1.00      ( k5_relat_1(sK2,k4_relat_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_2725,c_40,c_41,c_1510]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5482,plain,
% 3.03/1.00      ( v1_funct_1(sK2) != iProver_top
% 3.03/1.00      | v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top
% 3.03/1.00      | v2_funct_1(k4_relat_1(sK2)) = iProver_top
% 3.03/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.03/1.00      inference(light_normalisation,[status(thm)],[c_5477,c_2967]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5929,plain,
% 3.03/1.00      ( v2_funct_1(k4_relat_1(sK2)) = iProver_top
% 3.03/1.00      | v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_5482,c_38,c_40,c_1510]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5930,plain,
% 3.03/1.00      ( v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top
% 3.03/1.00      | v2_funct_1(k4_relat_1(sK2)) = iProver_top ),
% 3.03/1.00      inference(renaming,[status(thm)],[c_5929]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5,plain,
% 3.03/1.00      ( v2_funct_1(k6_relat_1(X0)) ),
% 3.03/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_730,plain,
% 3.03/1.00      ( v2_funct_1(k6_relat_1(X0_55)) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1242,plain,
% 3.03/1.00      ( v2_funct_1(k6_relat_1(X0_55)) = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_730]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5935,plain,
% 3.03/1.00      ( v2_funct_1(k4_relat_1(sK2)) = iProver_top ),
% 3.03/1.00      inference(forward_subsumption_resolution,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_5930,c_1242]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_14,plain,
% 3.03/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_722,plain,
% 3.03/1.00      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.03/1.00      | k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1250,plain,
% 3.03/1.00      ( k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54)
% 3.03/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_722]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2100,plain,
% 3.03/1.00      ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_1771,c_1250]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_28,negated_conjecture,
% 3.03/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.03/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_717,negated_conjecture,
% 3.03/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_28]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1277,plain,
% 3.03/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.03/1.00      inference(light_normalisation,[status(thm)],[c_717,c_711,c_712]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1773,plain,
% 3.03/1.00      ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.03/1.00      inference(demodulation,[status(thm)],[c_1691,c_1277]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3026,plain,
% 3.03/1.00      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 3.03/1.00      inference(demodulation,[status(thm)],[c_2100,c_1773]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3094,plain,
% 3.03/1.00      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 3.03/1.00      inference(demodulation,[status(thm)],[c_3026,c_2100]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_20,plain,
% 3.03/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/1.00      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.03/1.00      | ~ v1_funct_1(X0)
% 3.03/1.00      | ~ v2_funct_1(X0)
% 3.03/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.03/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_721,plain,
% 3.03/1.00      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 3.03/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.03/1.00      | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55)))
% 3.03/1.00      | ~ v1_funct_1(X0_54)
% 3.03/1.00      | ~ v2_funct_1(X0_54)
% 3.03/1.00      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1251,plain,
% 3.03/1.00      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 3.03/1.00      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 3.03/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 3.03/1.00      | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) = iProver_top
% 3.03/1.00      | v1_funct_1(X0_54) != iProver_top
% 3.03/1.00      | v2_funct_1(X0_54) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_721]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3700,plain,
% 3.03/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.03/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 3.03/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.03/1.00      | v1_funct_1(sK2) != iProver_top
% 3.03/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_3094,c_1251]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3713,plain,
% 3.03/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.03/1.00      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 3.03/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.03/1.00      | v1_funct_1(sK2) != iProver_top
% 3.03/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.03/1.00      inference(light_normalisation,[status(thm)],[c_3700,c_1663]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3097,plain,
% 3.03/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 3.03/1.00      inference(demodulation,[status(thm)],[c_3026,c_1771]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1772,plain,
% 3.03/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) = iProver_top ),
% 3.03/1.00      inference(demodulation,[status(thm)],[c_1691,c_1274]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3098,plain,
% 3.03/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 3.03/1.00      inference(demodulation,[status(thm)],[c_3026,c_1772]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3875,plain,
% 3.03/1.00      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_3713,c_38,c_41,c_3097,c_3098]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3880,plain,
% 3.03/1.00      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2)) ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_3875,c_1250]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_0,plain,
% 3.03/1.00      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 3.03/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_735,plain,
% 3.03/1.00      ( ~ v1_relat_1(X0_54)
% 3.03/1.00      | k2_relat_1(k4_relat_1(X0_54)) = k1_relat_1(X0_54) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1237,plain,
% 3.03/1.00      ( k2_relat_1(k4_relat_1(X0_54)) = k1_relat_1(X0_54)
% 3.03/1.00      | v1_relat_1(X0_54) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_735]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2415,plain,
% 3.03/1.00      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_1977,c_1237]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3883,plain,
% 3.03/1.00      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 3.03/1.00      inference(light_normalisation,[status(thm)],[c_3880,c_2415]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_25,plain,
% 3.03/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/1.00      | ~ v1_funct_1(X0)
% 3.03/1.00      | ~ v2_funct_1(X0)
% 3.03/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.03/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.03/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_719,plain,
% 3.03/1.00      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 3.03/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.03/1.00      | ~ v1_funct_1(X0_54)
% 3.03/1.00      | ~ v2_funct_1(X0_54)
% 3.03/1.00      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 3.03/1.00      | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_25]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1253,plain,
% 3.03/1.00      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 3.03/1.00      | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54)
% 3.03/1.00      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 3.03/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 3.03/1.00      | v1_funct_1(X0_54) != iProver_top
% 3.03/1.00      | v2_funct_1(X0_54) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_719]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4676,plain,
% 3.03/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_funct_1(k4_relat_1(sK2))
% 3.03/1.00      | v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.03/1.00      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.03/1.00      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 3.03/1.00      | v2_funct_1(k4_relat_1(sK2)) != iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_3883,c_1253]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_11,plain,
% 3.03/1.00      ( ~ v1_funct_1(X0)
% 3.03/1.00      | ~ v2_funct_1(X0)
% 3.03/1.00      | ~ v1_relat_1(X0)
% 3.03/1.00      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 3.03/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_724,plain,
% 3.03/1.00      ( ~ v1_funct_1(X0_54)
% 3.03/1.00      | ~ v2_funct_1(X0_54)
% 3.03/1.00      | ~ v1_relat_1(X0_54)
% 3.03/1.00      | k2_funct_1(k2_funct_1(X0_54)) = X0_54 ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1248,plain,
% 3.03/1.00      ( k2_funct_1(k2_funct_1(X0_54)) = X0_54
% 3.03/1.00      | v1_funct_1(X0_54) != iProver_top
% 3.03/1.00      | v2_funct_1(X0_54) != iProver_top
% 3.03/1.00      | v1_relat_1(X0_54) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_724]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2106,plain,
% 3.03/1.00      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.03/1.00      | v2_funct_1(sK2) != iProver_top
% 3.03/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_1257,c_1248]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2121,plain,
% 3.03/1.00      ( k2_funct_1(k4_relat_1(sK2)) = sK2
% 3.03/1.00      | v2_funct_1(sK2) != iProver_top
% 3.03/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.03/1.00      inference(light_normalisation,[status(thm)],[c_2106,c_1663]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2289,plain,
% 3.03/1.00      ( k2_funct_1(k4_relat_1(sK2)) = sK2 ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_2121,c_40,c_41,c_1510]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4696,plain,
% 3.03/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = sK2
% 3.03/1.00      | v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.03/1.00      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.03/1.00      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 3.03/1.00      | v2_funct_1(k4_relat_1(sK2)) != iProver_top ),
% 3.03/1.00      inference(light_normalisation,[status(thm)],[c_4676,c_2289]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_21,plain,
% 3.03/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.03/1.00      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 3.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/1.00      | ~ v1_funct_1(X0)
% 3.03/1.00      | ~ v2_funct_1(X0)
% 3.03/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.03/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_720,plain,
% 3.03/1.00      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 3.03/1.00      | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55)
% 3.03/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.03/1.00      | ~ v1_funct_1(X0_54)
% 3.03/1.00      | ~ v2_funct_1(X0_54)
% 3.03/1.00      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1252,plain,
% 3.03/1.00      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 3.03/1.00      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 3.03/1.00      | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55) = iProver_top
% 3.03/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 3.03/1.00      | v1_funct_1(X0_54) != iProver_top
% 3.03/1.00      | v2_funct_1(X0_54) != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_720]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2890,plain,
% 3.03/1.00      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) = iProver_top
% 3.03/1.00      | v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) != iProver_top
% 3.03/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) != iProver_top
% 3.03/1.00      | v1_funct_1(sK2) != iProver_top
% 3.03/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_1773,c_1252]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2891,plain,
% 3.03/1.00      ( v1_funct_2(k4_relat_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) = iProver_top
% 3.03/1.00      | v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) != iProver_top
% 3.03/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) != iProver_top
% 3.03/1.00      | v1_funct_1(sK2) != iProver_top
% 3.03/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.03/1.00      inference(light_normalisation,[status(thm)],[c_2890,c_1663]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3020,plain,
% 3.03/1.00      ( v1_funct_2(k4_relat_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) = iProver_top ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_2891,c_38,c_41,c_1771,c_1772]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3095,plain,
% 3.03/1.00      ( v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
% 3.03/1.00      inference(demodulation,[status(thm)],[c_3026,c_3020]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4827,plain,
% 3.03/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = sK2
% 3.03/1.00      | v2_funct_1(k4_relat_1(sK2)) != iProver_top ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_4696,c_38,c_40,c_41,c_1510,c_1921,c_3095,c_3097,
% 3.03/1.00                 c_3098,c_3713]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_5937,plain,
% 3.03/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = sK2 ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_5935,c_4827]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_19,plain,
% 3.03/1.00      ( r2_funct_2(X0,X1,X2,X2)
% 3.03/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.03/1.00      | ~ v1_funct_2(X3,X0,X1)
% 3.03/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.03/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.03/1.00      | ~ v1_funct_1(X2)
% 3.03/1.00      | ~ v1_funct_1(X3) ),
% 3.03/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_26,negated_conjecture,
% 3.03/1.00      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 3.03/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_435,plain,
% 3.03/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.03/1.00      | ~ v1_funct_2(X3,X1,X2)
% 3.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.03/1.00      | ~ v1_funct_1(X0)
% 3.03/1.00      | ~ v1_funct_1(X3)
% 3.03/1.00      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 3.03/1.00      | u1_struct_0(sK1) != X2
% 3.03/1.00      | u1_struct_0(sK0) != X1
% 3.03/1.00      | sK2 != X0 ),
% 3.03/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_436,plain,
% 3.03/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.03/1.00      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.03/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.03/1.00      | ~ v1_funct_1(X0)
% 3.03/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.03/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.03/1.00      inference(unflattening,[status(thm)],[c_435]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_710,plain,
% 3.03/1.00      ( ~ v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.03/1.00      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.03/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.03/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.03/1.00      | ~ v1_funct_1(X0_54)
% 3.03/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.03/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.03/1.00      inference(subtyping,[status(esa)],[c_436]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_737,plain,
% 3.03/1.00      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.03/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.03/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.03/1.00      | sP0_iProver_split
% 3.03/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.03/1.00      inference(splitting,
% 3.03/1.00                [splitting(split),new_symbols(definition,[])],
% 3.03/1.00                [c_710]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1259,plain,
% 3.03/1.00      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.03/1.00      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.03/1.00      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.03/1.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
% 3.03/1.00      | sP0_iProver_split = iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_737]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1433,plain,
% 3.03/1.00      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 3.03/1.00      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.03/1.00      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.03/1.00      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
% 3.03/1.00      | sP0_iProver_split = iProver_top ),
% 3.03/1.00      inference(light_normalisation,[status(thm)],[c_1259,c_711,c_712]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_736,plain,
% 3.03/1.00      ( ~ v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.03/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.03/1.00      | ~ v1_funct_1(X0_54)
% 3.03/1.00      | ~ sP0_iProver_split ),
% 3.03/1.00      inference(splitting,
% 3.03/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.03/1.00                [c_710]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1260,plain,
% 3.03/1.00      ( v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.03/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.03/1.00      | v1_funct_1(X0_54) != iProver_top
% 3.03/1.00      | sP0_iProver_split != iProver_top ),
% 3.03/1.00      inference(predicate_to_equality,[status(thm)],[c_736]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1349,plain,
% 3.03/1.00      ( v1_funct_2(X0_54,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.03/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.03/1.00      | v1_funct_1(X0_54) != iProver_top
% 3.03/1.00      | sP0_iProver_split != iProver_top ),
% 3.03/1.00      inference(light_normalisation,[status(thm)],[c_1260,c_711,c_712]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_1439,plain,
% 3.03/1.00      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 3.03/1.00      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.03/1.00      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.03/1.00      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 3.03/1.00      inference(forward_subsumption_resolution,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_1433,c_1349]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_2295,plain,
% 3.03/1.00      ( k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) != sK2
% 3.03/1.00      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_relat_1(sK2),k2_struct_0(sK1)) != iProver_top
% 3.03/1.00      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) != iProver_top
% 3.03/1.00      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))) != iProver_top ),
% 3.03/1.00      inference(light_normalisation,[status(thm)],[c_1439,c_1691]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3096,plain,
% 3.03/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
% 3.03/1.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.03/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.03/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
% 3.03/1.00      inference(demodulation,[status(thm)],[c_3026,c_2295]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3699,plain,
% 3.03/1.00      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 3.03/1.00      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.03/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.03/1.00      | v1_funct_1(sK2) != iProver_top
% 3.03/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.03/1.00      inference(superposition,[status(thm)],[c_3094,c_1253]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3724,plain,
% 3.03/1.00      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k4_relat_1(sK2)
% 3.03/1.00      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.03/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.03/1.00      | v1_funct_1(sK2) != iProver_top
% 3.03/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.03/1.00      inference(light_normalisation,[status(thm)],[c_3699,c_1663]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_3871,plain,
% 3.03/1.00      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k4_relat_1(sK2) ),
% 3.03/1.00      inference(global_propositional_subsumption,
% 3.03/1.00                [status(thm)],
% 3.03/1.00                [c_3724,c_38,c_41,c_3097,c_3098]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_4475,plain,
% 3.03/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) != sK2
% 3.03/1.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.03/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.03/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))) != iProver_top ),
% 3.03/1.00      inference(light_normalisation,[status(thm)],[c_3096,c_3871]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_6054,plain,
% 3.03/1.00      ( sK2 != sK2
% 3.03/1.00      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.03/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.03/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.03/1.00      inference(demodulation,[status(thm)],[c_5937,c_4475]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_739,plain,( X0_54 = X0_54 ),theory(equality) ).
% 3.03/1.00  
% 3.03/1.00  cnf(c_774,plain,
% 3.03/1.00      ( sK2 = sK2 ),
% 3.03/1.00      inference(instantiation,[status(thm)],[c_739]) ).
% 3.03/1.00  
% 3.03/1.00  cnf(contradiction,plain,
% 3.03/1.00      ( $false ),
% 3.03/1.00      inference(minisat,[status(thm)],[c_6054,c_3098,c_3097,c_774,c_38]) ).
% 3.03/1.00  
% 3.03/1.00  
% 3.03/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.03/1.00  
% 3.03/1.00  ------                               Statistics
% 3.03/1.00  
% 3.03/1.00  ------ General
% 3.03/1.00  
% 3.03/1.00  abstr_ref_over_cycles:                  0
% 3.03/1.00  abstr_ref_under_cycles:                 0
% 3.03/1.00  gc_basic_clause_elim:                   0
% 3.03/1.00  forced_gc_time:                         0
% 3.03/1.00  parsing_time:                           0.011
% 3.03/1.00  unif_index_cands_time:                  0.
% 3.03/1.00  unif_index_add_time:                    0.
% 3.03/1.00  orderings_time:                         0.
% 3.03/1.00  out_proof_time:                         0.015
% 3.03/1.00  total_time:                             0.237
% 3.03/1.00  num_of_symbols:                         63
% 3.03/1.00  num_of_terms:                           5182
% 3.03/1.00  
% 3.03/1.00  ------ Preprocessing
% 3.03/1.00  
% 3.03/1.00  num_of_splits:                          1
% 3.03/1.00  num_of_split_atoms:                     1
% 3.03/1.00  num_of_reused_defs:                     0
% 3.03/1.00  num_eq_ax_congr_red:                    7
% 3.03/1.00  num_of_sem_filtered_clauses:            2
% 3.03/1.00  num_of_subtypes:                        5
% 3.03/1.00  monotx_restored_types:                  1
% 3.03/1.00  sat_num_of_epr_types:                   0
% 3.03/1.00  sat_num_of_non_cyclic_types:            0
% 3.03/1.00  sat_guarded_non_collapsed_types:        1
% 3.03/1.00  num_pure_diseq_elim:                    0
% 3.03/1.00  simp_replaced_by:                       0
% 3.03/1.00  res_preprocessed:                       157
% 3.03/1.00  prep_upred:                             0
% 3.03/1.00  prep_unflattend:                        11
% 3.03/1.00  smt_new_axioms:                         0
% 3.03/1.00  pred_elim_cands:                        5
% 3.03/1.00  pred_elim:                              6
% 3.03/1.00  pred_elim_cl:                           7
% 3.03/1.00  pred_elim_cycles:                       8
% 3.03/1.00  merged_defs:                            0
% 3.03/1.00  merged_defs_ncl:                        0
% 3.03/1.00  bin_hyper_res:                          0
% 3.03/1.00  prep_cycles:                            4
% 3.03/1.00  pred_elim_time:                         0.011
% 3.03/1.00  splitting_time:                         0.
% 3.03/1.00  sem_filter_time:                        0.
% 3.03/1.00  monotx_time:                            0.001
% 3.03/1.00  subtype_inf_time:                       0.001
% 3.03/1.00  
% 3.03/1.00  ------ Problem properties
% 3.03/1.00  
% 3.03/1.00  clauses:                                28
% 3.03/1.00  conjectures:                            5
% 3.03/1.00  epr:                                    2
% 3.03/1.00  horn:                                   28
% 3.03/1.00  ground:                                 8
% 3.03/1.00  unary:                                  9
% 3.03/1.00  binary:                                 4
% 3.03/1.00  lits:                                   88
% 3.03/1.00  lits_eq:                                18
% 3.03/1.00  fd_pure:                                0
% 3.03/1.00  fd_pseudo:                              0
% 3.03/1.00  fd_cond:                                0
% 3.03/1.00  fd_pseudo_cond:                         1
% 3.03/1.00  ac_symbols:                             0
% 3.03/1.00  
% 3.03/1.00  ------ Propositional Solver
% 3.03/1.00  
% 3.03/1.00  prop_solver_calls:                      29
% 3.03/1.00  prop_fast_solver_calls:                 1348
% 3.03/1.00  smt_solver_calls:                       0
% 3.03/1.00  smt_fast_solver_calls:                  0
% 3.03/1.00  prop_num_of_clauses:                    2196
% 3.03/1.00  prop_preprocess_simplified:             6747
% 3.03/1.00  prop_fo_subsumed:                       66
% 3.03/1.00  prop_solver_time:                       0.
% 3.03/1.00  smt_solver_time:                        0.
% 3.03/1.00  smt_fast_solver_time:                   0.
% 3.03/1.00  prop_fast_solver_time:                  0.
% 3.03/1.00  prop_unsat_core_time:                   0.
% 3.03/1.00  
% 3.03/1.00  ------ QBF
% 3.03/1.00  
% 3.03/1.00  qbf_q_res:                              0
% 3.03/1.00  qbf_num_tautologies:                    0
% 3.03/1.00  qbf_prep_cycles:                        0
% 3.03/1.00  
% 3.03/1.00  ------ BMC1
% 3.03/1.00  
% 3.03/1.00  bmc1_current_bound:                     -1
% 3.03/1.00  bmc1_last_solved_bound:                 -1
% 3.03/1.00  bmc1_unsat_core_size:                   -1
% 3.03/1.00  bmc1_unsat_core_parents_size:           -1
% 3.03/1.00  bmc1_merge_next_fun:                    0
% 3.03/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.03/1.00  
% 3.03/1.00  ------ Instantiation
% 3.03/1.00  
% 3.03/1.00  inst_num_of_clauses:                    771
% 3.03/1.00  inst_num_in_passive:                    326
% 3.03/1.00  inst_num_in_active:                     408
% 3.03/1.00  inst_num_in_unprocessed:                37
% 3.03/1.00  inst_num_of_loops:                      430
% 3.03/1.00  inst_num_of_learning_restarts:          0
% 3.03/1.00  inst_num_moves_active_passive:          17
% 3.03/1.00  inst_lit_activity:                      0
% 3.03/1.00  inst_lit_activity_moves:                0
% 3.03/1.00  inst_num_tautologies:                   0
% 3.03/1.00  inst_num_prop_implied:                  0
% 3.03/1.00  inst_num_existing_simplified:           0
% 3.03/1.00  inst_num_eq_res_simplified:             0
% 3.03/1.00  inst_num_child_elim:                    0
% 3.03/1.00  inst_num_of_dismatching_blockings:      143
% 3.03/1.00  inst_num_of_non_proper_insts:           757
% 3.03/1.00  inst_num_of_duplicates:                 0
% 3.03/1.00  inst_inst_num_from_inst_to_res:         0
% 3.03/1.00  inst_dismatching_checking_time:         0.
% 3.03/1.00  
% 3.03/1.00  ------ Resolution
% 3.03/1.00  
% 3.03/1.00  res_num_of_clauses:                     0
% 3.03/1.00  res_num_in_passive:                     0
% 3.03/1.00  res_num_in_active:                      0
% 3.03/1.00  res_num_of_loops:                       161
% 3.03/1.00  res_forward_subset_subsumed:            73
% 3.03/1.00  res_backward_subset_subsumed:           0
% 3.03/1.00  res_forward_subsumed:                   0
% 3.03/1.00  res_backward_subsumed:                  0
% 3.03/1.00  res_forward_subsumption_resolution:     1
% 3.03/1.00  res_backward_subsumption_resolution:    0
% 3.03/1.00  res_clause_to_clause_subsumption:       358
% 3.03/1.00  res_orphan_elimination:                 0
% 3.03/1.00  res_tautology_del:                      83
% 3.03/1.00  res_num_eq_res_simplified:              0
% 3.03/1.00  res_num_sel_changes:                    0
% 3.03/1.00  res_moves_from_active_to_pass:          0
% 3.03/1.00  
% 3.03/1.00  ------ Superposition
% 3.03/1.00  
% 3.03/1.00  sup_time_total:                         0.
% 3.03/1.00  sup_time_generating:                    0.
% 3.03/1.00  sup_time_sim_full:                      0.
% 3.03/1.00  sup_time_sim_immed:                     0.
% 3.03/1.00  
% 3.03/1.00  sup_num_of_clauses:                     86
% 3.03/1.00  sup_num_in_active:                      63
% 3.03/1.00  sup_num_in_passive:                     23
% 3.03/1.00  sup_num_of_loops:                       85
% 3.03/1.00  sup_fw_superposition:                   69
% 3.03/1.00  sup_bw_superposition:                   38
% 3.03/1.00  sup_immediate_simplified:               52
% 3.03/1.00  sup_given_eliminated:                   0
% 3.03/1.00  comparisons_done:                       0
% 3.03/1.00  comparisons_avoided:                    0
% 3.03/1.00  
% 3.03/1.00  ------ Simplifications
% 3.03/1.00  
% 3.03/1.00  
% 3.03/1.00  sim_fw_subset_subsumed:                 8
% 3.03/1.00  sim_bw_subset_subsumed:                 4
% 3.03/1.00  sim_fw_subsumed:                        6
% 3.03/1.00  sim_bw_subsumed:                        0
% 3.03/1.00  sim_fw_subsumption_res:                 2
% 3.03/1.00  sim_bw_subsumption_res:                 0
% 3.03/1.00  sim_tautology_del:                      0
% 3.03/1.00  sim_eq_tautology_del:                   29
% 3.03/1.00  sim_eq_res_simp:                        0
% 3.03/1.00  sim_fw_demodulated:                     0
% 3.03/1.00  sim_bw_demodulated:                     19
% 3.03/1.00  sim_light_normalised:                   59
% 3.03/1.00  sim_joinable_taut:                      0
% 3.03/1.00  sim_joinable_simp:                      0
% 3.03/1.00  sim_ac_normalised:                      0
% 3.03/1.00  sim_smt_subsumption:                    0
% 3.03/1.00  
%------------------------------------------------------------------------------
