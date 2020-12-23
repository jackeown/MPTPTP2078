%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:31 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :  245 (16762 expanded)
%              Number of clauses        :  160 (5162 expanded)
%              Number of leaves         :   23 (4643 expanded)
%              Depth                    :   34
%              Number of atoms          :  861 (105538 expanded)
%              Number of equality atoms :  345 (16532 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

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
    inference(ennf_transformation,[],[f20])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f54,plain,(
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

fof(f53,plain,(
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

fof(f52,plain,
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

fof(f55,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f50,f54,f53,f52])).

fof(f88,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f55])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f80,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f83,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f85,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f86,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f60,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f90,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f61,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f67,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f36])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f84,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f55])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f89,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f59,plain,(
    ! [X0] :
      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f69,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_722,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1275,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_722])).

cnf(c_24,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_35,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_407,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_35])).

cnf(c_408,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_718,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_408])).

cnf(c_33,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_402,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_33])).

cnf(c_403,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_719,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_403])).

cnf(c_1301,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1275,c_718,c_719])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_743,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | ~ v1_relat_1(X1_54)
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1255,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top
    | v1_relat_1(X1_54) != iProver_top
    | v1_relat_1(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_743])).

cnf(c_1694,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1301,c_1255])).

cnf(c_41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1560,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | v1_relat_1(X0_54)
    | ~ v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_1774,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1560])).

cnf(c_1775,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1774])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_742,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1789,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_742])).

cnf(c_1790,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1789])).

cnf(c_1793,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1694,c_41,c_1775,c_1790])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_740,plain,
    ( ~ v1_relat_1(X0_54)
    | k1_relat_1(k4_relat_1(X0_54)) = k2_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1258,plain,
    ( k1_relat_1(k4_relat_1(X0_54)) = k2_relat_1(X0_54)
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_740])).

cnf(c_1982,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1793,c_1258])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X1,X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_734,plain,
    ( ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54)
    | v2_funct_1(X0_54)
    | ~ v2_funct_1(k5_relat_1(X1_54,X0_54))
    | ~ v1_relat_1(X0_54)
    | ~ v1_relat_1(X1_54)
    | k1_relat_1(X0_54) != k2_relat_1(X1_54) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1264,plain,
    ( k1_relat_1(X0_54) != k2_relat_1(X1_54)
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v2_funct_1(X0_54) = iProver_top
    | v2_funct_1(k5_relat_1(X1_54,X0_54)) != iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_relat_1(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_734])).

cnf(c_2477,plain,
    ( k2_relat_1(X0_54) != k2_relat_1(sK2)
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v2_funct_1(k5_relat_1(X0_54,k4_relat_1(sK2))) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1982,c_1264])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_39,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_720,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_1277,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_720])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_739,plain,
    ( ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | k2_funct_1(X0_54) = k4_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1259,plain,
    ( k2_funct_1(X0_54) = k4_relat_1(X0_54)
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_739])).

cnf(c_1923,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1277,c_1259])).

cnf(c_28,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_795,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_739])).

cnf(c_2177,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1923,c_32,c_30,c_28,c_795,c_1774,c_1789])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_737,plain,
    ( ~ v1_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | v1_relat_1(k2_funct_1(X0_54)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1261,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_relat_1(k2_funct_1(X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_2180,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2177,c_1261])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_738,plain,
    ( ~ v1_funct_1(X0_54)
    | v1_funct_1(k2_funct_1(X0_54))
    | ~ v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1260,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k2_funct_1(X0_54)) = iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_738])).

cnf(c_2181,plain,
    ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2177,c_1260])).

cnf(c_4863,plain,
    ( v1_relat_1(X0_54) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) = iProver_top
    | v2_funct_1(k5_relat_1(X0_54,k4_relat_1(sK2))) != iProver_top
    | k2_relat_1(X0_54) != k2_relat_1(sK2)
    | v1_funct_1(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2477,c_39,c_41,c_1775,c_1790,c_2180,c_2181])).

cnf(c_4864,plain,
    ( k2_relat_1(X0_54) != k2_relat_1(sK2)
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(k5_relat_1(X0_54,k4_relat_1(sK2))) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_4863])).

cnf(c_4878,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,k4_relat_1(sK2))) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4864])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_731,plain,
    ( ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | k5_relat_1(X0_54,k2_funct_1(X0_54)) = k6_relat_1(k1_relat_1(X0_54)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1267,plain,
    ( k5_relat_1(X0_54,k2_funct_1(X0_54)) = k6_relat_1(k1_relat_1(X0_54))
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_2663,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1277,c_1267])).

cnf(c_2686,plain,
    ( k5_relat_1(sK2,k4_relat_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2663,c_2177])).

cnf(c_42,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2999,plain,
    ( k5_relat_1(sK2,k4_relat_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2686,c_41,c_42,c_1775,c_1790])).

cnf(c_4883,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4878,c_2999])).

cnf(c_4925,plain,
    ( v2_funct_1(k4_relat_1(sK2)) = iProver_top
    | v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4883,c_39,c_41,c_1775,c_1790])).

cnf(c_4926,plain,
    ( v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4925])).

cnf(c_7,plain,
    ( v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_736,plain,
    ( v2_funct_1(k6_relat_1(X0_55)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1262,plain,
    ( v2_funct_1(k6_relat_1(X0_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_736])).

cnf(c_4931,plain,
    ( v2_funct_1(k4_relat_1(sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4926,c_1262])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_25,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_389,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_34])).

cnf(c_390,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_48,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_392,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_390,c_34,c_33,c_48])).

cnf(c_414,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_392])).

cnf(c_415,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_19,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_511,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_415,c_19])).

cnf(c_14,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_527,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_511,c_14])).

cnf(c_716,plain,
    ( ~ v1_funct_2(X0_54,X0_55,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | k1_relat_1(X0_54) = X0_55 ),
    inference(subtyping,[status(esa)],[c_527])).

cnf(c_1280,plain,
    ( k1_relat_1(X0_54) = X0_55
    | v1_funct_2(X0_54,X0_55,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_1375,plain,
    ( k1_relat_1(X0_54) = X0_55
    | v1_funct_2(X0_54,X0_55,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1280,c_719])).

cnf(c_1772,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1301,c_1375])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_721,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1276,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_721])).

cnf(c_1295,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1276,c_718,c_719])).

cnf(c_1483,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1295])).

cnf(c_1773,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1772])).

cnf(c_1800,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1772,c_32,c_30,c_1483,c_1773,c_1774,c_1789])).

cnf(c_1803,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1800,c_1301])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_729,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1269,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_2082,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1803,c_1269])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_723,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1298,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_723,c_718,c_719])).

cnf(c_1805,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1800,c_1298])).

cnf(c_2422,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2082,c_1805])).

cnf(c_2827,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2422,c_2082])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_728,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55)))
    | ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1270,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_3176,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2827,c_1270])).

cnf(c_3177,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3176,c_2177])).

cnf(c_2829,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2422,c_1803])).

cnf(c_1804,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1800,c_1295])).

cnf(c_2830,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2422,c_1804])).

cnf(c_3836,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3177,c_39,c_42,c_2829,c_2830])).

cnf(c_3842,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3836,c_1269])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_741,plain,
    ( ~ v1_relat_1(X0_54)
    | k2_relat_1(k4_relat_1(X0_54)) = k1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1257,plain,
    ( k2_relat_1(k4_relat_1(X0_54)) = k1_relat_1(X0_54)
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(c_1798,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1793,c_1257])).

cnf(c_3845,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3842,c_1798])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_725,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1273,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54)
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_725])).

cnf(c_4124,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_funct_1(k4_relat_1(sK2))
    | v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3845,c_1273])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_730,plain,
    ( ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | k2_funct_1(k2_funct_1(X0_54)) = X0_54 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1268,plain,
    ( k2_funct_1(k2_funct_1(X0_54)) = X0_54
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_730])).

cnf(c_2550,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1277,c_1268])).

cnf(c_2572,plain,
    ( k2_funct_1(k4_relat_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2550,c_2177])).

cnf(c_2937,plain,
    ( k2_funct_1(k4_relat_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2572,c_41,c_42,c_1775,c_1790])).

cnf(c_4144,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = sK2
    | v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4124,c_2937])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_727,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X0_54)
    | ~ v2_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1271,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v2_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_727])).

cnf(c_3327,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2827,c_1271])).

cnf(c_3328,plain,
    ( v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3327,c_2177])).

cnf(c_4481,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = sK2
    | v2_funct_1(k4_relat_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4144,c_39,c_41,c_42,c_1775,c_1790,c_2181,c_2829,c_2830,c_3177,c_3328])).

cnf(c_4933,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_4931,c_4481])).

cnf(c_20,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_27,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_437,plain,
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
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_438,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_717,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_438])).

cnf(c_745,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sP0_iProver_split
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_717])).

cnf(c_1278,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_745])).

cnf(c_1462,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1278,c_718,c_719])).

cnf(c_744,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_54)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_717])).

cnf(c_1279,plain,
    ( v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_1366,plain,
    ( v1_funct_2(X0_54,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1279,c_718,c_719])).

cnf(c_1468,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1462,c_1366])).

cnf(c_1912,plain,
    ( k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_relat_1(sK2),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1468,c_1800])).

cnf(c_2828,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2422,c_1912])).

cnf(c_3481,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2827,c_1273])).

cnf(c_3482,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k4_relat_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3481,c_2177])).

cnf(c_3741,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3482,c_39,c_42,c_2829,c_2830])).

cnf(c_4007,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2828,c_3741])).

cnf(c_5378,plain,
    ( sK2 != sK2
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4933,c_4007])).

cnf(c_747,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_781,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_747])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5378,c_2830,c_2829,c_781,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:09:05 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.80/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/0.98  
% 2.80/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.80/0.98  
% 2.80/0.98  ------  iProver source info
% 2.80/0.98  
% 2.80/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.80/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.80/0.98  git: non_committed_changes: false
% 2.80/0.98  git: last_make_outside_of_git: false
% 2.80/0.98  
% 2.80/0.98  ------ 
% 2.80/0.98  
% 2.80/0.98  ------ Input Options
% 2.80/0.98  
% 2.80/0.98  --out_options                           all
% 2.80/0.98  --tptp_safe_out                         true
% 2.80/0.98  --problem_path                          ""
% 2.80/0.98  --include_path                          ""
% 2.80/0.98  --clausifier                            res/vclausify_rel
% 2.80/0.98  --clausifier_options                    --mode clausify
% 2.80/0.98  --stdin                                 false
% 2.80/0.98  --stats_out                             all
% 2.80/0.98  
% 2.80/0.98  ------ General Options
% 2.80/0.98  
% 2.80/0.98  --fof                                   false
% 2.80/0.98  --time_out_real                         305.
% 2.80/0.98  --time_out_virtual                      -1.
% 2.80/0.98  --symbol_type_check                     false
% 2.80/0.98  --clausify_out                          false
% 2.80/0.98  --sig_cnt_out                           false
% 2.80/0.98  --trig_cnt_out                          false
% 2.80/0.98  --trig_cnt_out_tolerance                1.
% 2.80/0.98  --trig_cnt_out_sk_spl                   false
% 2.80/0.98  --abstr_cl_out                          false
% 2.80/0.98  
% 2.80/0.98  ------ Global Options
% 2.80/0.98  
% 2.80/0.98  --schedule                              default
% 2.80/0.98  --add_important_lit                     false
% 2.80/0.98  --prop_solver_per_cl                    1000
% 2.80/0.98  --min_unsat_core                        false
% 2.80/0.98  --soft_assumptions                      false
% 2.80/0.98  --soft_lemma_size                       3
% 2.80/0.98  --prop_impl_unit_size                   0
% 2.80/0.98  --prop_impl_unit                        []
% 2.80/0.98  --share_sel_clauses                     true
% 2.80/0.98  --reset_solvers                         false
% 2.80/0.98  --bc_imp_inh                            [conj_cone]
% 2.80/0.98  --conj_cone_tolerance                   3.
% 2.80/0.98  --extra_neg_conj                        none
% 2.80/0.98  --large_theory_mode                     true
% 2.80/0.98  --prolific_symb_bound                   200
% 2.80/0.98  --lt_threshold                          2000
% 2.80/0.98  --clause_weak_htbl                      true
% 2.80/0.98  --gc_record_bc_elim                     false
% 2.80/0.99  
% 2.80/0.99  ------ Preprocessing Options
% 2.80/0.99  
% 2.80/0.99  --preprocessing_flag                    true
% 2.80/0.99  --time_out_prep_mult                    0.1
% 2.80/0.99  --splitting_mode                        input
% 2.80/0.99  --splitting_grd                         true
% 2.80/0.99  --splitting_cvd                         false
% 2.80/0.99  --splitting_cvd_svl                     false
% 2.80/0.99  --splitting_nvd                         32
% 2.80/0.99  --sub_typing                            true
% 2.80/0.99  --prep_gs_sim                           true
% 2.80/0.99  --prep_unflatten                        true
% 2.80/0.99  --prep_res_sim                          true
% 2.80/0.99  --prep_upred                            true
% 2.80/0.99  --prep_sem_filter                       exhaustive
% 2.80/0.99  --prep_sem_filter_out                   false
% 2.80/0.99  --pred_elim                             true
% 2.80/0.99  --res_sim_input                         true
% 2.80/0.99  --eq_ax_congr_red                       true
% 2.80/0.99  --pure_diseq_elim                       true
% 2.80/0.99  --brand_transform                       false
% 2.80/0.99  --non_eq_to_eq                          false
% 2.80/0.99  --prep_def_merge                        true
% 2.80/0.99  --prep_def_merge_prop_impl              false
% 2.80/0.99  --prep_def_merge_mbd                    true
% 2.80/0.99  --prep_def_merge_tr_red                 false
% 2.80/0.99  --prep_def_merge_tr_cl                  false
% 2.80/0.99  --smt_preprocessing                     true
% 2.80/0.99  --smt_ac_axioms                         fast
% 2.80/0.99  --preprocessed_out                      false
% 2.80/0.99  --preprocessed_stats                    false
% 2.80/0.99  
% 2.80/0.99  ------ Abstraction refinement Options
% 2.80/0.99  
% 2.80/0.99  --abstr_ref                             []
% 2.80/0.99  --abstr_ref_prep                        false
% 2.80/0.99  --abstr_ref_until_sat                   false
% 2.80/0.99  --abstr_ref_sig_restrict                funpre
% 2.80/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.80/0.99  --abstr_ref_under                       []
% 2.80/0.99  
% 2.80/0.99  ------ SAT Options
% 2.80/0.99  
% 2.80/0.99  --sat_mode                              false
% 2.80/0.99  --sat_fm_restart_options                ""
% 2.80/0.99  --sat_gr_def                            false
% 2.80/0.99  --sat_epr_types                         true
% 2.80/0.99  --sat_non_cyclic_types                  false
% 2.80/0.99  --sat_finite_models                     false
% 2.80/0.99  --sat_fm_lemmas                         false
% 2.80/0.99  --sat_fm_prep                           false
% 2.80/0.99  --sat_fm_uc_incr                        true
% 2.80/0.99  --sat_out_model                         small
% 2.80/0.99  --sat_out_clauses                       false
% 2.80/0.99  
% 2.80/0.99  ------ QBF Options
% 2.80/0.99  
% 2.80/0.99  --qbf_mode                              false
% 2.80/0.99  --qbf_elim_univ                         false
% 2.80/0.99  --qbf_dom_inst                          none
% 2.80/0.99  --qbf_dom_pre_inst                      false
% 2.80/0.99  --qbf_sk_in                             false
% 2.80/0.99  --qbf_pred_elim                         true
% 2.80/0.99  --qbf_split                             512
% 2.80/0.99  
% 2.80/0.99  ------ BMC1 Options
% 2.80/0.99  
% 2.80/0.99  --bmc1_incremental                      false
% 2.80/0.99  --bmc1_axioms                           reachable_all
% 2.80/0.99  --bmc1_min_bound                        0
% 2.80/0.99  --bmc1_max_bound                        -1
% 2.80/0.99  --bmc1_max_bound_default                -1
% 2.80/0.99  --bmc1_symbol_reachability              true
% 2.80/0.99  --bmc1_property_lemmas                  false
% 2.80/0.99  --bmc1_k_induction                      false
% 2.80/0.99  --bmc1_non_equiv_states                 false
% 2.80/0.99  --bmc1_deadlock                         false
% 2.80/0.99  --bmc1_ucm                              false
% 2.80/0.99  --bmc1_add_unsat_core                   none
% 2.80/0.99  --bmc1_unsat_core_children              false
% 2.80/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.80/0.99  --bmc1_out_stat                         full
% 2.80/0.99  --bmc1_ground_init                      false
% 2.80/0.99  --bmc1_pre_inst_next_state              false
% 2.80/0.99  --bmc1_pre_inst_state                   false
% 2.80/0.99  --bmc1_pre_inst_reach_state             false
% 2.80/0.99  --bmc1_out_unsat_core                   false
% 2.80/0.99  --bmc1_aig_witness_out                  false
% 2.80/0.99  --bmc1_verbose                          false
% 2.80/0.99  --bmc1_dump_clauses_tptp                false
% 2.80/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.80/0.99  --bmc1_dump_file                        -
% 2.80/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.80/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.80/0.99  --bmc1_ucm_extend_mode                  1
% 2.80/0.99  --bmc1_ucm_init_mode                    2
% 2.80/0.99  --bmc1_ucm_cone_mode                    none
% 2.80/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.80/0.99  --bmc1_ucm_relax_model                  4
% 2.80/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.80/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.80/0.99  --bmc1_ucm_layered_model                none
% 2.80/0.99  --bmc1_ucm_max_lemma_size               10
% 2.80/0.99  
% 2.80/0.99  ------ AIG Options
% 2.80/0.99  
% 2.80/0.99  --aig_mode                              false
% 2.80/0.99  
% 2.80/0.99  ------ Instantiation Options
% 2.80/0.99  
% 2.80/0.99  --instantiation_flag                    true
% 2.80/0.99  --inst_sos_flag                         false
% 2.80/0.99  --inst_sos_phase                        true
% 2.80/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.80/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.80/0.99  --inst_lit_sel_side                     num_symb
% 2.80/0.99  --inst_solver_per_active                1400
% 2.80/0.99  --inst_solver_calls_frac                1.
% 2.80/0.99  --inst_passive_queue_type               priority_queues
% 2.80/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.80/0.99  --inst_passive_queues_freq              [25;2]
% 2.80/0.99  --inst_dismatching                      true
% 2.80/0.99  --inst_eager_unprocessed_to_passive     true
% 2.80/0.99  --inst_prop_sim_given                   true
% 2.80/0.99  --inst_prop_sim_new                     false
% 2.80/0.99  --inst_subs_new                         false
% 2.80/0.99  --inst_eq_res_simp                      false
% 2.80/0.99  --inst_subs_given                       false
% 2.80/0.99  --inst_orphan_elimination               true
% 2.80/0.99  --inst_learning_loop_flag               true
% 2.80/0.99  --inst_learning_start                   3000
% 2.80/0.99  --inst_learning_factor                  2
% 2.80/0.99  --inst_start_prop_sim_after_learn       3
% 2.80/0.99  --inst_sel_renew                        solver
% 2.80/0.99  --inst_lit_activity_flag                true
% 2.80/0.99  --inst_restr_to_given                   false
% 2.80/0.99  --inst_activity_threshold               500
% 2.80/0.99  --inst_out_proof                        true
% 2.80/0.99  
% 2.80/0.99  ------ Resolution Options
% 2.80/0.99  
% 2.80/0.99  --resolution_flag                       true
% 2.80/0.99  --res_lit_sel                           adaptive
% 2.80/0.99  --res_lit_sel_side                      none
% 2.80/0.99  --res_ordering                          kbo
% 2.80/0.99  --res_to_prop_solver                    active
% 2.80/0.99  --res_prop_simpl_new                    false
% 2.80/0.99  --res_prop_simpl_given                  true
% 2.80/0.99  --res_passive_queue_type                priority_queues
% 2.80/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.80/0.99  --res_passive_queues_freq               [15;5]
% 2.80/0.99  --res_forward_subs                      full
% 2.80/0.99  --res_backward_subs                     full
% 2.80/0.99  --res_forward_subs_resolution           true
% 2.80/0.99  --res_backward_subs_resolution          true
% 2.80/0.99  --res_orphan_elimination                true
% 2.80/0.99  --res_time_limit                        2.
% 2.80/0.99  --res_out_proof                         true
% 2.80/0.99  
% 2.80/0.99  ------ Superposition Options
% 2.80/0.99  
% 2.80/0.99  --superposition_flag                    true
% 2.80/0.99  --sup_passive_queue_type                priority_queues
% 2.80/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.80/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.80/0.99  --demod_completeness_check              fast
% 2.80/0.99  --demod_use_ground                      true
% 2.80/0.99  --sup_to_prop_solver                    passive
% 2.80/0.99  --sup_prop_simpl_new                    true
% 2.80/0.99  --sup_prop_simpl_given                  true
% 2.80/0.99  --sup_fun_splitting                     false
% 2.80/0.99  --sup_smt_interval                      50000
% 2.80/0.99  
% 2.80/0.99  ------ Superposition Simplification Setup
% 2.80/0.99  
% 2.80/0.99  --sup_indices_passive                   []
% 2.80/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.80/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.99  --sup_full_bw                           [BwDemod]
% 2.80/0.99  --sup_immed_triv                        [TrivRules]
% 2.80/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.80/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.99  --sup_immed_bw_main                     []
% 2.80/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.80/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.99  
% 2.80/0.99  ------ Combination Options
% 2.80/0.99  
% 2.80/0.99  --comb_res_mult                         3
% 2.80/0.99  --comb_sup_mult                         2
% 2.80/0.99  --comb_inst_mult                        10
% 2.80/0.99  
% 2.80/0.99  ------ Debug Options
% 2.80/0.99  
% 2.80/0.99  --dbg_backtrace                         false
% 2.80/0.99  --dbg_dump_prop_clauses                 false
% 2.80/0.99  --dbg_dump_prop_clauses_file            -
% 2.80/0.99  --dbg_out_stat                          false
% 2.80/0.99  ------ Parsing...
% 2.80/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.80/0.99  
% 2.80/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.80/0.99  
% 2.80/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.80/0.99  
% 2.80/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.80/0.99  ------ Proving...
% 2.80/0.99  ------ Problem Properties 
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  clauses                                 29
% 2.80/0.99  conjectures                             5
% 2.80/0.99  EPR                                     2
% 2.80/0.99  Horn                                    29
% 2.80/0.99  unary                                   10
% 2.80/0.99  binary                                  3
% 2.80/0.99  lits                                    93
% 2.80/0.99  lits eq                                 19
% 2.80/0.99  fd_pure                                 0
% 2.80/0.99  fd_pseudo                               0
% 2.80/0.99  fd_cond                                 0
% 2.80/0.99  fd_pseudo_cond                          1
% 2.80/0.99  AC symbols                              0
% 2.80/0.99  
% 2.80/0.99  ------ Schedule dynamic 5 is on 
% 2.80/0.99  
% 2.80/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  ------ 
% 2.80/0.99  Current options:
% 2.80/0.99  ------ 
% 2.80/0.99  
% 2.80/0.99  ------ Input Options
% 2.80/0.99  
% 2.80/0.99  --out_options                           all
% 2.80/0.99  --tptp_safe_out                         true
% 2.80/0.99  --problem_path                          ""
% 2.80/0.99  --include_path                          ""
% 2.80/0.99  --clausifier                            res/vclausify_rel
% 2.80/0.99  --clausifier_options                    --mode clausify
% 2.80/0.99  --stdin                                 false
% 2.80/0.99  --stats_out                             all
% 2.80/0.99  
% 2.80/0.99  ------ General Options
% 2.80/0.99  
% 2.80/0.99  --fof                                   false
% 2.80/0.99  --time_out_real                         305.
% 2.80/0.99  --time_out_virtual                      -1.
% 2.80/0.99  --symbol_type_check                     false
% 2.80/0.99  --clausify_out                          false
% 2.80/0.99  --sig_cnt_out                           false
% 2.80/0.99  --trig_cnt_out                          false
% 2.80/0.99  --trig_cnt_out_tolerance                1.
% 2.80/0.99  --trig_cnt_out_sk_spl                   false
% 2.80/0.99  --abstr_cl_out                          false
% 2.80/0.99  
% 2.80/0.99  ------ Global Options
% 2.80/0.99  
% 2.80/0.99  --schedule                              default
% 2.80/0.99  --add_important_lit                     false
% 2.80/0.99  --prop_solver_per_cl                    1000
% 2.80/0.99  --min_unsat_core                        false
% 2.80/0.99  --soft_assumptions                      false
% 2.80/0.99  --soft_lemma_size                       3
% 2.80/0.99  --prop_impl_unit_size                   0
% 2.80/0.99  --prop_impl_unit                        []
% 2.80/0.99  --share_sel_clauses                     true
% 2.80/0.99  --reset_solvers                         false
% 2.80/0.99  --bc_imp_inh                            [conj_cone]
% 2.80/0.99  --conj_cone_tolerance                   3.
% 2.80/0.99  --extra_neg_conj                        none
% 2.80/0.99  --large_theory_mode                     true
% 2.80/0.99  --prolific_symb_bound                   200
% 2.80/0.99  --lt_threshold                          2000
% 2.80/0.99  --clause_weak_htbl                      true
% 2.80/0.99  --gc_record_bc_elim                     false
% 2.80/0.99  
% 2.80/0.99  ------ Preprocessing Options
% 2.80/0.99  
% 2.80/0.99  --preprocessing_flag                    true
% 2.80/0.99  --time_out_prep_mult                    0.1
% 2.80/0.99  --splitting_mode                        input
% 2.80/0.99  --splitting_grd                         true
% 2.80/0.99  --splitting_cvd                         false
% 2.80/0.99  --splitting_cvd_svl                     false
% 2.80/0.99  --splitting_nvd                         32
% 2.80/0.99  --sub_typing                            true
% 2.80/0.99  --prep_gs_sim                           true
% 2.80/0.99  --prep_unflatten                        true
% 2.80/0.99  --prep_res_sim                          true
% 2.80/0.99  --prep_upred                            true
% 2.80/0.99  --prep_sem_filter                       exhaustive
% 2.80/0.99  --prep_sem_filter_out                   false
% 2.80/0.99  --pred_elim                             true
% 2.80/0.99  --res_sim_input                         true
% 2.80/0.99  --eq_ax_congr_red                       true
% 2.80/0.99  --pure_diseq_elim                       true
% 2.80/0.99  --brand_transform                       false
% 2.80/0.99  --non_eq_to_eq                          false
% 2.80/0.99  --prep_def_merge                        true
% 2.80/0.99  --prep_def_merge_prop_impl              false
% 2.80/0.99  --prep_def_merge_mbd                    true
% 2.80/0.99  --prep_def_merge_tr_red                 false
% 2.80/0.99  --prep_def_merge_tr_cl                  false
% 2.80/0.99  --smt_preprocessing                     true
% 2.80/0.99  --smt_ac_axioms                         fast
% 2.80/0.99  --preprocessed_out                      false
% 2.80/0.99  --preprocessed_stats                    false
% 2.80/0.99  
% 2.80/0.99  ------ Abstraction refinement Options
% 2.80/0.99  
% 2.80/0.99  --abstr_ref                             []
% 2.80/0.99  --abstr_ref_prep                        false
% 2.80/0.99  --abstr_ref_until_sat                   false
% 2.80/0.99  --abstr_ref_sig_restrict                funpre
% 2.80/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.80/0.99  --abstr_ref_under                       []
% 2.80/0.99  
% 2.80/0.99  ------ SAT Options
% 2.80/0.99  
% 2.80/0.99  --sat_mode                              false
% 2.80/0.99  --sat_fm_restart_options                ""
% 2.80/0.99  --sat_gr_def                            false
% 2.80/0.99  --sat_epr_types                         true
% 2.80/0.99  --sat_non_cyclic_types                  false
% 2.80/0.99  --sat_finite_models                     false
% 2.80/0.99  --sat_fm_lemmas                         false
% 2.80/0.99  --sat_fm_prep                           false
% 2.80/0.99  --sat_fm_uc_incr                        true
% 2.80/0.99  --sat_out_model                         small
% 2.80/0.99  --sat_out_clauses                       false
% 2.80/0.99  
% 2.80/0.99  ------ QBF Options
% 2.80/0.99  
% 2.80/0.99  --qbf_mode                              false
% 2.80/0.99  --qbf_elim_univ                         false
% 2.80/0.99  --qbf_dom_inst                          none
% 2.80/0.99  --qbf_dom_pre_inst                      false
% 2.80/0.99  --qbf_sk_in                             false
% 2.80/0.99  --qbf_pred_elim                         true
% 2.80/0.99  --qbf_split                             512
% 2.80/0.99  
% 2.80/0.99  ------ BMC1 Options
% 2.80/0.99  
% 2.80/0.99  --bmc1_incremental                      false
% 2.80/0.99  --bmc1_axioms                           reachable_all
% 2.80/0.99  --bmc1_min_bound                        0
% 2.80/0.99  --bmc1_max_bound                        -1
% 2.80/0.99  --bmc1_max_bound_default                -1
% 2.80/0.99  --bmc1_symbol_reachability              true
% 2.80/0.99  --bmc1_property_lemmas                  false
% 2.80/0.99  --bmc1_k_induction                      false
% 2.80/0.99  --bmc1_non_equiv_states                 false
% 2.80/0.99  --bmc1_deadlock                         false
% 2.80/0.99  --bmc1_ucm                              false
% 2.80/0.99  --bmc1_add_unsat_core                   none
% 2.80/0.99  --bmc1_unsat_core_children              false
% 2.80/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.80/0.99  --bmc1_out_stat                         full
% 2.80/0.99  --bmc1_ground_init                      false
% 2.80/0.99  --bmc1_pre_inst_next_state              false
% 2.80/0.99  --bmc1_pre_inst_state                   false
% 2.80/0.99  --bmc1_pre_inst_reach_state             false
% 2.80/0.99  --bmc1_out_unsat_core                   false
% 2.80/0.99  --bmc1_aig_witness_out                  false
% 2.80/0.99  --bmc1_verbose                          false
% 2.80/0.99  --bmc1_dump_clauses_tptp                false
% 2.80/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.80/0.99  --bmc1_dump_file                        -
% 2.80/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.80/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.80/0.99  --bmc1_ucm_extend_mode                  1
% 2.80/0.99  --bmc1_ucm_init_mode                    2
% 2.80/0.99  --bmc1_ucm_cone_mode                    none
% 2.80/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.80/0.99  --bmc1_ucm_relax_model                  4
% 2.80/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.80/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.80/0.99  --bmc1_ucm_layered_model                none
% 2.80/0.99  --bmc1_ucm_max_lemma_size               10
% 2.80/0.99  
% 2.80/0.99  ------ AIG Options
% 2.80/0.99  
% 2.80/0.99  --aig_mode                              false
% 2.80/0.99  
% 2.80/0.99  ------ Instantiation Options
% 2.80/0.99  
% 2.80/0.99  --instantiation_flag                    true
% 2.80/0.99  --inst_sos_flag                         false
% 2.80/0.99  --inst_sos_phase                        true
% 2.80/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.80/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.80/0.99  --inst_lit_sel_side                     none
% 2.80/0.99  --inst_solver_per_active                1400
% 2.80/0.99  --inst_solver_calls_frac                1.
% 2.80/0.99  --inst_passive_queue_type               priority_queues
% 2.80/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.80/0.99  --inst_passive_queues_freq              [25;2]
% 2.80/0.99  --inst_dismatching                      true
% 2.80/0.99  --inst_eager_unprocessed_to_passive     true
% 2.80/0.99  --inst_prop_sim_given                   true
% 2.80/0.99  --inst_prop_sim_new                     false
% 2.80/0.99  --inst_subs_new                         false
% 2.80/0.99  --inst_eq_res_simp                      false
% 2.80/0.99  --inst_subs_given                       false
% 2.80/0.99  --inst_orphan_elimination               true
% 2.80/0.99  --inst_learning_loop_flag               true
% 2.80/0.99  --inst_learning_start                   3000
% 2.80/0.99  --inst_learning_factor                  2
% 2.80/0.99  --inst_start_prop_sim_after_learn       3
% 2.80/0.99  --inst_sel_renew                        solver
% 2.80/0.99  --inst_lit_activity_flag                true
% 2.80/0.99  --inst_restr_to_given                   false
% 2.80/0.99  --inst_activity_threshold               500
% 2.80/0.99  --inst_out_proof                        true
% 2.80/0.99  
% 2.80/0.99  ------ Resolution Options
% 2.80/0.99  
% 2.80/0.99  --resolution_flag                       false
% 2.80/0.99  --res_lit_sel                           adaptive
% 2.80/0.99  --res_lit_sel_side                      none
% 2.80/0.99  --res_ordering                          kbo
% 2.80/0.99  --res_to_prop_solver                    active
% 2.80/0.99  --res_prop_simpl_new                    false
% 2.80/0.99  --res_prop_simpl_given                  true
% 2.80/0.99  --res_passive_queue_type                priority_queues
% 2.80/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.80/0.99  --res_passive_queues_freq               [15;5]
% 2.80/0.99  --res_forward_subs                      full
% 2.80/0.99  --res_backward_subs                     full
% 2.80/0.99  --res_forward_subs_resolution           true
% 2.80/0.99  --res_backward_subs_resolution          true
% 2.80/0.99  --res_orphan_elimination                true
% 2.80/0.99  --res_time_limit                        2.
% 2.80/0.99  --res_out_proof                         true
% 2.80/0.99  
% 2.80/0.99  ------ Superposition Options
% 2.80/0.99  
% 2.80/0.99  --superposition_flag                    true
% 2.80/0.99  --sup_passive_queue_type                priority_queues
% 2.80/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.80/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.80/0.99  --demod_completeness_check              fast
% 2.80/0.99  --demod_use_ground                      true
% 2.80/0.99  --sup_to_prop_solver                    passive
% 2.80/0.99  --sup_prop_simpl_new                    true
% 2.80/0.99  --sup_prop_simpl_given                  true
% 2.80/0.99  --sup_fun_splitting                     false
% 2.80/0.99  --sup_smt_interval                      50000
% 2.80/0.99  
% 2.80/0.99  ------ Superposition Simplification Setup
% 2.80/0.99  
% 2.80/0.99  --sup_indices_passive                   []
% 2.80/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.80/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.99  --sup_full_bw                           [BwDemod]
% 2.80/0.99  --sup_immed_triv                        [TrivRules]
% 2.80/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.80/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.99  --sup_immed_bw_main                     []
% 2.80/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.80/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/0.99  
% 2.80/0.99  ------ Combination Options
% 2.80/0.99  
% 2.80/0.99  --comb_res_mult                         3
% 2.80/0.99  --comb_sup_mult                         2
% 2.80/0.99  --comb_inst_mult                        10
% 2.80/0.99  
% 2.80/0.99  ------ Debug Options
% 2.80/0.99  
% 2.80/0.99  --dbg_backtrace                         false
% 2.80/0.99  --dbg_dump_prop_clauses                 false
% 2.80/0.99  --dbg_dump_prop_clauses_file            -
% 2.80/0.99  --dbg_out_stat                          false
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  ------ Proving...
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  % SZS status Theorem for theBenchmark.p
% 2.80/0.99  
% 2.80/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.80/0.99  
% 2.80/0.99  fof(f19,conjecture,(
% 2.80/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f20,negated_conjecture,(
% 2.80/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.80/0.99    inference(negated_conjecture,[],[f19])).
% 2.80/0.99  
% 2.80/0.99  fof(f49,plain,(
% 2.80/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.80/0.99    inference(ennf_transformation,[],[f20])).
% 2.80/0.99  
% 2.80/0.99  fof(f50,plain,(
% 2.80/0.99    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.80/0.99    inference(flattening,[],[f49])).
% 2.80/0.99  
% 2.80/0.99  fof(f54,plain,(
% 2.80/0.99    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.80/0.99    introduced(choice_axiom,[])).
% 2.80/0.99  
% 2.80/0.99  fof(f53,plain,(
% 2.80/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.80/0.99    introduced(choice_axiom,[])).
% 2.80/0.99  
% 2.80/0.99  fof(f52,plain,(
% 2.80/0.99    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.80/0.99    introduced(choice_axiom,[])).
% 2.80/0.99  
% 2.80/0.99  fof(f55,plain,(
% 2.80/0.99    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.80/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f50,f54,f53,f52])).
% 2.80/0.99  
% 2.80/0.99  fof(f88,plain,(
% 2.80/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.80/0.99    inference(cnf_transformation,[],[f55])).
% 2.80/0.99  
% 2.80/0.99  fof(f16,axiom,(
% 2.80/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f44,plain,(
% 2.80/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.80/0.99    inference(ennf_transformation,[],[f16])).
% 2.80/0.99  
% 2.80/0.99  fof(f80,plain,(
% 2.80/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f44])).
% 2.80/0.99  
% 2.80/0.99  fof(f83,plain,(
% 2.80/0.99    l1_struct_0(sK0)),
% 2.80/0.99    inference(cnf_transformation,[],[f55])).
% 2.80/0.99  
% 2.80/0.99  fof(f85,plain,(
% 2.80/0.99    l1_struct_0(sK1)),
% 2.80/0.99    inference(cnf_transformation,[],[f55])).
% 2.80/0.99  
% 2.80/0.99  fof(f1,axiom,(
% 2.80/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f22,plain,(
% 2.80/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.80/0.99    inference(ennf_transformation,[],[f1])).
% 2.80/0.99  
% 2.80/0.99  fof(f56,plain,(
% 2.80/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f22])).
% 2.80/0.99  
% 2.80/0.99  fof(f2,axiom,(
% 2.80/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f57,plain,(
% 2.80/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.80/0.99    inference(cnf_transformation,[],[f2])).
% 2.80/0.99  
% 2.80/0.99  fof(f3,axiom,(
% 2.80/0.99    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f23,plain,(
% 2.80/0.99    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.80/0.99    inference(ennf_transformation,[],[f3])).
% 2.80/0.99  
% 2.80/0.99  fof(f58,plain,(
% 2.80/0.99    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f23])).
% 2.80/0.99  
% 2.80/0.99  fof(f7,axiom,(
% 2.80/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f28,plain,(
% 2.80/0.99    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.80/0.99    inference(ennf_transformation,[],[f7])).
% 2.80/0.99  
% 2.80/0.99  fof(f29,plain,(
% 2.80/0.99    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.80/0.99    inference(flattening,[],[f28])).
% 2.80/0.99  
% 2.80/0.99  fof(f66,plain,(
% 2.80/0.99    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f29])).
% 2.80/0.99  
% 2.80/0.99  fof(f86,plain,(
% 2.80/0.99    v1_funct_1(sK2)),
% 2.80/0.99    inference(cnf_transformation,[],[f55])).
% 2.80/0.99  
% 2.80/0.99  fof(f4,axiom,(
% 2.80/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f24,plain,(
% 2.80/0.99    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.80/0.99    inference(ennf_transformation,[],[f4])).
% 2.80/0.99  
% 2.80/0.99  fof(f25,plain,(
% 2.80/0.99    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.80/0.99    inference(flattening,[],[f24])).
% 2.80/0.99  
% 2.80/0.99  fof(f60,plain,(
% 2.80/0.99    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f25])).
% 2.80/0.99  
% 2.80/0.99  fof(f90,plain,(
% 2.80/0.99    v2_funct_1(sK2)),
% 2.80/0.99    inference(cnf_transformation,[],[f55])).
% 2.80/0.99  
% 2.80/0.99  fof(f5,axiom,(
% 2.80/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f26,plain,(
% 2.80/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.80/0.99    inference(ennf_transformation,[],[f5])).
% 2.80/0.99  
% 2.80/0.99  fof(f27,plain,(
% 2.80/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.80/0.99    inference(flattening,[],[f26])).
% 2.80/0.99  
% 2.80/0.99  fof(f61,plain,(
% 2.80/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f27])).
% 2.80/0.99  
% 2.80/0.99  fof(f62,plain,(
% 2.80/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f27])).
% 2.80/0.99  
% 2.80/0.99  fof(f8,axiom,(
% 2.80/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f30,plain,(
% 2.80/0.99    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.80/0.99    inference(ennf_transformation,[],[f8])).
% 2.80/0.99  
% 2.80/0.99  fof(f31,plain,(
% 2.80/0.99    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.80/0.99    inference(flattening,[],[f30])).
% 2.80/0.99  
% 2.80/0.99  fof(f67,plain,(
% 2.80/0.99    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f31])).
% 2.80/0.99  
% 2.80/0.99  fof(f6,axiom,(
% 2.80/0.99    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f64,plain,(
% 2.80/0.99    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.80/0.99    inference(cnf_transformation,[],[f6])).
% 2.80/0.99  
% 2.80/0.99  fof(f12,axiom,(
% 2.80/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f36,plain,(
% 2.80/0.99    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.80/0.99    inference(ennf_transformation,[],[f12])).
% 2.80/0.99  
% 2.80/0.99  fof(f37,plain,(
% 2.80/0.99    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.80/0.99    inference(flattening,[],[f36])).
% 2.80/0.99  
% 2.80/0.99  fof(f73,plain,(
% 2.80/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f37])).
% 2.80/0.99  
% 2.80/0.99  fof(f17,axiom,(
% 2.80/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f45,plain,(
% 2.80/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.80/0.99    inference(ennf_transformation,[],[f17])).
% 2.80/0.99  
% 2.80/0.99  fof(f46,plain,(
% 2.80/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.80/0.99    inference(flattening,[],[f45])).
% 2.80/0.99  
% 2.80/0.99  fof(f81,plain,(
% 2.80/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f46])).
% 2.80/0.99  
% 2.80/0.99  fof(f84,plain,(
% 2.80/0.99    ~v2_struct_0(sK1)),
% 2.80/0.99    inference(cnf_transformation,[],[f55])).
% 2.80/0.99  
% 2.80/0.99  fof(f13,axiom,(
% 2.80/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f38,plain,(
% 2.80/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.80/0.99    inference(ennf_transformation,[],[f13])).
% 2.80/0.99  
% 2.80/0.99  fof(f39,plain,(
% 2.80/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.80/0.99    inference(flattening,[],[f38])).
% 2.80/0.99  
% 2.80/0.99  fof(f51,plain,(
% 2.80/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.80/0.99    inference(nnf_transformation,[],[f39])).
% 2.80/0.99  
% 2.80/0.99  fof(f74,plain,(
% 2.80/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f51])).
% 2.80/0.99  
% 2.80/0.99  fof(f10,axiom,(
% 2.80/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f21,plain,(
% 2.80/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.80/0.99    inference(pure_predicate_removal,[],[f10])).
% 2.80/0.99  
% 2.80/0.99  fof(f34,plain,(
% 2.80/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/0.99    inference(ennf_transformation,[],[f21])).
% 2.80/0.99  
% 2.80/0.99  fof(f70,plain,(
% 2.80/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.80/0.99    inference(cnf_transformation,[],[f34])).
% 2.80/0.99  
% 2.80/0.99  fof(f87,plain,(
% 2.80/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.80/0.99    inference(cnf_transformation,[],[f55])).
% 2.80/0.99  
% 2.80/0.99  fof(f11,axiom,(
% 2.80/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f35,plain,(
% 2.80/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/0.99    inference(ennf_transformation,[],[f11])).
% 2.80/0.99  
% 2.80/0.99  fof(f71,plain,(
% 2.80/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.80/0.99    inference(cnf_transformation,[],[f35])).
% 2.80/0.99  
% 2.80/0.99  fof(f89,plain,(
% 2.80/0.99    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.80/0.99    inference(cnf_transformation,[],[f55])).
% 2.80/0.99  
% 2.80/0.99  fof(f15,axiom,(
% 2.80/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f42,plain,(
% 2.80/0.99    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.80/0.99    inference(ennf_transformation,[],[f15])).
% 2.80/0.99  
% 2.80/0.99  fof(f43,plain,(
% 2.80/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.80/0.99    inference(flattening,[],[f42])).
% 2.80/0.99  
% 2.80/0.99  fof(f79,plain,(
% 2.80/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f43])).
% 2.80/0.99  
% 2.80/0.99  fof(f59,plain,(
% 2.80/0.99    ( ! [X0] : (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f23])).
% 2.80/0.99  
% 2.80/0.99  fof(f18,axiom,(
% 2.80/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f47,plain,(
% 2.80/0.99    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.80/0.99    inference(ennf_transformation,[],[f18])).
% 2.80/0.99  
% 2.80/0.99  fof(f48,plain,(
% 2.80/0.99    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.80/0.99    inference(flattening,[],[f47])).
% 2.80/0.99  
% 2.80/0.99  fof(f82,plain,(
% 2.80/0.99    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f48])).
% 2.80/0.99  
% 2.80/0.99  fof(f9,axiom,(
% 2.80/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f32,plain,(
% 2.80/0.99    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.80/0.99    inference(ennf_transformation,[],[f9])).
% 2.80/0.99  
% 2.80/0.99  fof(f33,plain,(
% 2.80/0.99    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.80/0.99    inference(flattening,[],[f32])).
% 2.80/0.99  
% 2.80/0.99  fof(f69,plain,(
% 2.80/0.99    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f33])).
% 2.80/0.99  
% 2.80/0.99  fof(f78,plain,(
% 2.80/0.99    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f43])).
% 2.80/0.99  
% 2.80/0.99  fof(f14,axiom,(
% 2.80/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 2.80/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f40,plain,(
% 2.80/0.99    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.80/0.99    inference(ennf_transformation,[],[f14])).
% 2.80/0.99  
% 2.80/0.99  fof(f41,plain,(
% 2.80/0.99    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.80/0.99    inference(flattening,[],[f40])).
% 2.80/0.99  
% 2.80/0.99  fof(f76,plain,(
% 2.80/0.99    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f41])).
% 2.80/0.99  
% 2.80/0.99  fof(f91,plain,(
% 2.80/0.99    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 2.80/0.99    inference(cnf_transformation,[],[f55])).
% 2.80/0.99  
% 2.80/0.99  cnf(c_30,negated_conjecture,
% 2.80/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.80/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_722,negated_conjecture,
% 2.80/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.80/0.99      inference(subtyping,[status(esa)],[c_30]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1275,plain,
% 2.80/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_722]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_24,plain,
% 2.80/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.80/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_35,negated_conjecture,
% 2.80/0.99      ( l1_struct_0(sK0) ),
% 2.80/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_407,plain,
% 2.80/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.80/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_35]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_408,plain,
% 2.80/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.80/0.99      inference(unflattening,[status(thm)],[c_407]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_718,plain,
% 2.80/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.80/0.99      inference(subtyping,[status(esa)],[c_408]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_33,negated_conjecture,
% 2.80/0.99      ( l1_struct_0(sK1) ),
% 2.80/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_402,plain,
% 2.80/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.80/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_33]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_403,plain,
% 2.80/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.80/0.99      inference(unflattening,[status(thm)],[c_402]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_719,plain,
% 2.80/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.80/0.99      inference(subtyping,[status(esa)],[c_403]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1301,plain,
% 2.80/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.80/0.99      inference(light_normalisation,[status(thm)],[c_1275,c_718,c_719]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_0,plain,
% 2.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.80/0.99      | ~ v1_relat_1(X1)
% 2.80/0.99      | v1_relat_1(X0) ),
% 2.80/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_743,plain,
% 2.80/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 2.80/0.99      | ~ v1_relat_1(X1_54)
% 2.80/0.99      | v1_relat_1(X0_54) ),
% 2.80/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1255,plain,
% 2.80/0.99      ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top
% 2.80/0.99      | v1_relat_1(X1_54) != iProver_top
% 2.80/0.99      | v1_relat_1(X0_54) = iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_743]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1694,plain,
% 2.80/0.99      ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != iProver_top
% 2.80/0.99      | v1_relat_1(sK2) = iProver_top ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_1301,c_1255]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_41,plain,
% 2.80/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1560,plain,
% 2.80/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.80/0.99      | v1_relat_1(X0_54)
% 2.80/0.99      | ~ v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_743]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1774,plain,
% 2.80/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.80/0.99      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.80/0.99      | v1_relat_1(sK2) ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_1560]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1775,plain,
% 2.80/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.80/0.99      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.80/0.99      | v1_relat_1(sK2) = iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_1774]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1,plain,
% 2.80/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.80/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_742,plain,
% 2.80/0.99      ( v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) ),
% 2.80/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1789,plain,
% 2.80/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_742]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1790,plain,
% 2.80/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_1789]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1793,plain,
% 2.80/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 2.80/0.99      inference(global_propositional_subsumption,
% 2.80/0.99                [status(thm)],
% 2.80/0.99                [c_1694,c_41,c_1775,c_1790]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3,plain,
% 2.80/0.99      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 2.80/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_740,plain,
% 2.80/0.99      ( ~ v1_relat_1(X0_54)
% 2.80/0.99      | k1_relat_1(k4_relat_1(X0_54)) = k2_relat_1(X0_54) ),
% 2.80/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1258,plain,
% 2.80/0.99      ( k1_relat_1(k4_relat_1(X0_54)) = k2_relat_1(X0_54)
% 2.80/0.99      | v1_relat_1(X0_54) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_740]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1982,plain,
% 2.80/0.99      ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_1793,c_1258]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_9,plain,
% 2.80/0.99      ( ~ v1_funct_1(X0)
% 2.80/0.99      | ~ v1_funct_1(X1)
% 2.80/0.99      | v2_funct_1(X0)
% 2.80/0.99      | ~ v2_funct_1(k5_relat_1(X1,X0))
% 2.80/0.99      | ~ v1_relat_1(X0)
% 2.80/0.99      | ~ v1_relat_1(X1)
% 2.80/0.99      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 2.80/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_734,plain,
% 2.80/0.99      ( ~ v1_funct_1(X0_54)
% 2.80/0.99      | ~ v1_funct_1(X1_54)
% 2.80/0.99      | v2_funct_1(X0_54)
% 2.80/0.99      | ~ v2_funct_1(k5_relat_1(X1_54,X0_54))
% 2.80/0.99      | ~ v1_relat_1(X0_54)
% 2.80/0.99      | ~ v1_relat_1(X1_54)
% 2.80/0.99      | k1_relat_1(X0_54) != k2_relat_1(X1_54) ),
% 2.80/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1264,plain,
% 2.80/0.99      ( k1_relat_1(X0_54) != k2_relat_1(X1_54)
% 2.80/0.99      | v1_funct_1(X0_54) != iProver_top
% 2.80/0.99      | v1_funct_1(X1_54) != iProver_top
% 2.80/0.99      | v2_funct_1(X0_54) = iProver_top
% 2.80/0.99      | v2_funct_1(k5_relat_1(X1_54,X0_54)) != iProver_top
% 2.80/0.99      | v1_relat_1(X0_54) != iProver_top
% 2.80/0.99      | v1_relat_1(X1_54) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_734]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2477,plain,
% 2.80/0.99      ( k2_relat_1(X0_54) != k2_relat_1(sK2)
% 2.80/0.99      | v1_funct_1(X0_54) != iProver_top
% 2.80/0.99      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 2.80/0.99      | v2_funct_1(k5_relat_1(X0_54,k4_relat_1(sK2))) != iProver_top
% 2.80/0.99      | v2_funct_1(k4_relat_1(sK2)) = iProver_top
% 2.80/0.99      | v1_relat_1(X0_54) != iProver_top
% 2.80/0.99      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_1982,c_1264]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_32,negated_conjecture,
% 2.80/0.99      ( v1_funct_1(sK2) ),
% 2.80/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_39,plain,
% 2.80/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_720,negated_conjecture,
% 2.80/0.99      ( v1_funct_1(sK2) ),
% 2.80/0.99      inference(subtyping,[status(esa)],[c_32]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1277,plain,
% 2.80/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_720]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4,plain,
% 2.80/0.99      ( ~ v1_funct_1(X0)
% 2.80/0.99      | ~ v2_funct_1(X0)
% 2.80/0.99      | ~ v1_relat_1(X0)
% 2.80/0.99      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 2.80/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_739,plain,
% 2.80/0.99      ( ~ v1_funct_1(X0_54)
% 2.80/0.99      | ~ v2_funct_1(X0_54)
% 2.80/0.99      | ~ v1_relat_1(X0_54)
% 2.80/0.99      | k2_funct_1(X0_54) = k4_relat_1(X0_54) ),
% 2.80/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1259,plain,
% 2.80/0.99      ( k2_funct_1(X0_54) = k4_relat_1(X0_54)
% 2.80/0.99      | v1_funct_1(X0_54) != iProver_top
% 2.80/0.99      | v2_funct_1(X0_54) != iProver_top
% 2.80/0.99      | v1_relat_1(X0_54) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_739]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1923,plain,
% 2.80/0.99      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 2.80/0.99      | v2_funct_1(sK2) != iProver_top
% 2.80/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_1277,c_1259]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_28,negated_conjecture,
% 2.80/0.99      ( v2_funct_1(sK2) ),
% 2.80/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_795,plain,
% 2.80/0.99      ( ~ v1_funct_1(sK2)
% 2.80/0.99      | ~ v2_funct_1(sK2)
% 2.80/0.99      | ~ v1_relat_1(sK2)
% 2.80/0.99      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_739]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2177,plain,
% 2.80/0.99      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.80/0.99      inference(global_propositional_subsumption,
% 2.80/0.99                [status(thm)],
% 2.80/0.99                [c_1923,c_32,c_30,c_28,c_795,c_1774,c_1789]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_6,plain,
% 2.80/0.99      ( ~ v1_funct_1(X0)
% 2.80/0.99      | ~ v1_relat_1(X0)
% 2.80/0.99      | v1_relat_1(k2_funct_1(X0)) ),
% 2.80/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_737,plain,
% 2.80/0.99      ( ~ v1_funct_1(X0_54)
% 2.80/0.99      | ~ v1_relat_1(X0_54)
% 2.80/0.99      | v1_relat_1(k2_funct_1(X0_54)) ),
% 2.80/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1261,plain,
% 2.80/0.99      ( v1_funct_1(X0_54) != iProver_top
% 2.80/0.99      | v1_relat_1(X0_54) != iProver_top
% 2.80/0.99      | v1_relat_1(k2_funct_1(X0_54)) = iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_737]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2180,plain,
% 2.80/0.99      ( v1_funct_1(sK2) != iProver_top
% 2.80/0.99      | v1_relat_1(k4_relat_1(sK2)) = iProver_top
% 2.80/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_2177,c_1261]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_5,plain,
% 2.80/0.99      ( ~ v1_funct_1(X0)
% 2.80/0.99      | v1_funct_1(k2_funct_1(X0))
% 2.80/0.99      | ~ v1_relat_1(X0) ),
% 2.80/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_738,plain,
% 2.80/0.99      ( ~ v1_funct_1(X0_54)
% 2.80/0.99      | v1_funct_1(k2_funct_1(X0_54))
% 2.80/0.99      | ~ v1_relat_1(X0_54) ),
% 2.80/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1260,plain,
% 2.80/0.99      ( v1_funct_1(X0_54) != iProver_top
% 2.80/0.99      | v1_funct_1(k2_funct_1(X0_54)) = iProver_top
% 2.80/0.99      | v1_relat_1(X0_54) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_738]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2181,plain,
% 2.80/0.99      ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
% 2.80/0.99      | v1_funct_1(sK2) != iProver_top
% 2.80/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_2177,c_1260]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4863,plain,
% 2.80/0.99      ( v1_relat_1(X0_54) != iProver_top
% 2.80/0.99      | v2_funct_1(k4_relat_1(sK2)) = iProver_top
% 2.80/0.99      | v2_funct_1(k5_relat_1(X0_54,k4_relat_1(sK2))) != iProver_top
% 2.80/0.99      | k2_relat_1(X0_54) != k2_relat_1(sK2)
% 2.80/0.99      | v1_funct_1(X0_54) != iProver_top ),
% 2.80/0.99      inference(global_propositional_subsumption,
% 2.80/0.99                [status(thm)],
% 2.80/0.99                [c_2477,c_39,c_41,c_1775,c_1790,c_2180,c_2181]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4864,plain,
% 2.80/0.99      ( k2_relat_1(X0_54) != k2_relat_1(sK2)
% 2.80/0.99      | v1_funct_1(X0_54) != iProver_top
% 2.80/0.99      | v2_funct_1(k5_relat_1(X0_54,k4_relat_1(sK2))) != iProver_top
% 2.80/0.99      | v2_funct_1(k4_relat_1(sK2)) = iProver_top
% 2.80/0.99      | v1_relat_1(X0_54) != iProver_top ),
% 2.80/0.99      inference(renaming,[status(thm)],[c_4863]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4878,plain,
% 2.80/0.99      ( v1_funct_1(sK2) != iProver_top
% 2.80/0.99      | v2_funct_1(k5_relat_1(sK2,k4_relat_1(sK2))) != iProver_top
% 2.80/0.99      | v2_funct_1(k4_relat_1(sK2)) = iProver_top
% 2.80/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.80/0.99      inference(equality_resolution,[status(thm)],[c_4864]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_12,plain,
% 2.80/0.99      ( ~ v1_funct_1(X0)
% 2.80/0.99      | ~ v2_funct_1(X0)
% 2.80/0.99      | ~ v1_relat_1(X0)
% 2.80/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
% 2.80/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_731,plain,
% 2.80/0.99      ( ~ v1_funct_1(X0_54)
% 2.80/0.99      | ~ v2_funct_1(X0_54)
% 2.80/0.99      | ~ v1_relat_1(X0_54)
% 2.80/0.99      | k5_relat_1(X0_54,k2_funct_1(X0_54)) = k6_relat_1(k1_relat_1(X0_54)) ),
% 2.80/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1267,plain,
% 2.80/0.99      ( k5_relat_1(X0_54,k2_funct_1(X0_54)) = k6_relat_1(k1_relat_1(X0_54))
% 2.80/0.99      | v1_funct_1(X0_54) != iProver_top
% 2.80/0.99      | v2_funct_1(X0_54) != iProver_top
% 2.80/0.99      | v1_relat_1(X0_54) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_731]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2663,plain,
% 2.80/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
% 2.80/0.99      | v2_funct_1(sK2) != iProver_top
% 2.80/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_1277,c_1267]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2686,plain,
% 2.80/0.99      ( k5_relat_1(sK2,k4_relat_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
% 2.80/0.99      | v2_funct_1(sK2) != iProver_top
% 2.80/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.80/0.99      inference(light_normalisation,[status(thm)],[c_2663,c_2177]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_42,plain,
% 2.80/0.99      ( v2_funct_1(sK2) = iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2999,plain,
% 2.80/0.99      ( k5_relat_1(sK2,k4_relat_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
% 2.80/0.99      inference(global_propositional_subsumption,
% 2.80/0.99                [status(thm)],
% 2.80/0.99                [c_2686,c_41,c_42,c_1775,c_1790]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4883,plain,
% 2.80/0.99      ( v1_funct_1(sK2) != iProver_top
% 2.80/0.99      | v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top
% 2.80/0.99      | v2_funct_1(k4_relat_1(sK2)) = iProver_top
% 2.80/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.80/0.99      inference(light_normalisation,[status(thm)],[c_4878,c_2999]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4925,plain,
% 2.80/0.99      ( v2_funct_1(k4_relat_1(sK2)) = iProver_top
% 2.80/0.99      | v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top ),
% 2.80/0.99      inference(global_propositional_subsumption,
% 2.80/0.99                [status(thm)],
% 2.80/0.99                [c_4883,c_39,c_41,c_1775,c_1790]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4926,plain,
% 2.80/0.99      ( v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top
% 2.80/0.99      | v2_funct_1(k4_relat_1(sK2)) = iProver_top ),
% 2.80/0.99      inference(renaming,[status(thm)],[c_4925]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_7,plain,
% 2.80/0.99      ( v2_funct_1(k6_relat_1(X0)) ),
% 2.80/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_736,plain,
% 2.80/0.99      ( v2_funct_1(k6_relat_1(X0_55)) ),
% 2.80/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1262,plain,
% 2.80/0.99      ( v2_funct_1(k6_relat_1(X0_55)) = iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_736]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4931,plain,
% 2.80/0.99      ( v2_funct_1(k4_relat_1(sK2)) = iProver_top ),
% 2.80/0.99      inference(forward_subsumption_resolution,
% 2.80/0.99                [status(thm)],
% 2.80/0.99                [c_4926,c_1262]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_16,plain,
% 2.80/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.80/0.99      | v1_partfun1(X0,X1)
% 2.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/0.99      | v1_xboole_0(X2)
% 2.80/0.99      | ~ v1_funct_1(X0) ),
% 2.80/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_25,plain,
% 2.80/0.99      ( v2_struct_0(X0)
% 2.80/0.99      | ~ l1_struct_0(X0)
% 2.80/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.80/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_34,negated_conjecture,
% 2.80/0.99      ( ~ v2_struct_0(sK1) ),
% 2.80/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_389,plain,
% 2.80/0.99      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 2.80/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_34]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_390,plain,
% 2.80/0.99      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.80/0.99      inference(unflattening,[status(thm)],[c_389]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_48,plain,
% 2.80/0.99      ( v2_struct_0(sK1)
% 2.80/0.99      | ~ l1_struct_0(sK1)
% 2.80/0.99      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_25]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_392,plain,
% 2.80/0.99      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.80/0.99      inference(global_propositional_subsumption,
% 2.80/0.99                [status(thm)],
% 2.80/0.99                [c_390,c_34,c_33,c_48]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_414,plain,
% 2.80/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.80/0.99      | v1_partfun1(X0,X1)
% 2.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/0.99      | ~ v1_funct_1(X0)
% 2.80/0.99      | u1_struct_0(sK1) != X2 ),
% 2.80/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_392]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_415,plain,
% 2.80/0.99      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.80/0.99      | v1_partfun1(X0,X1)
% 2.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.80/0.99      | ~ v1_funct_1(X0) ),
% 2.80/0.99      inference(unflattening,[status(thm)],[c_414]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_19,plain,
% 2.80/0.99      ( ~ v1_partfun1(X0,X1)
% 2.80/0.99      | ~ v4_relat_1(X0,X1)
% 2.80/0.99      | ~ v1_relat_1(X0)
% 2.80/0.99      | k1_relat_1(X0) = X1 ),
% 2.80/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_511,plain,
% 2.80/0.99      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.80/0.99      | ~ v4_relat_1(X0,X1)
% 2.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.80/0.99      | ~ v1_funct_1(X0)
% 2.80/0.99      | ~ v1_relat_1(X0)
% 2.80/0.99      | k1_relat_1(X0) = X1 ),
% 2.80/0.99      inference(resolution,[status(thm)],[c_415,c_19]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_14,plain,
% 2.80/0.99      ( v4_relat_1(X0,X1)
% 2.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.80/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_527,plain,
% 2.80/0.99      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.80/0.99      | ~ v1_funct_1(X0)
% 2.80/0.99      | ~ v1_relat_1(X0)
% 2.80/0.99      | k1_relat_1(X0) = X1 ),
% 2.80/0.99      inference(forward_subsumption_resolution,
% 2.80/0.99                [status(thm)],
% 2.80/0.99                [c_511,c_14]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_716,plain,
% 2.80/0.99      ( ~ v1_funct_2(X0_54,X0_55,u1_struct_0(sK1))
% 2.80/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,u1_struct_0(sK1))))
% 2.80/0.99      | ~ v1_funct_1(X0_54)
% 2.80/0.99      | ~ v1_relat_1(X0_54)
% 2.80/0.99      | k1_relat_1(X0_54) = X0_55 ),
% 2.80/0.99      inference(subtyping,[status(esa)],[c_527]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1280,plain,
% 2.80/0.99      ( k1_relat_1(X0_54) = X0_55
% 2.80/0.99      | v1_funct_2(X0_54,X0_55,u1_struct_0(sK1)) != iProver_top
% 2.80/0.99      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,u1_struct_0(sK1)))) != iProver_top
% 2.80/0.99      | v1_funct_1(X0_54) != iProver_top
% 2.80/0.99      | v1_relat_1(X0_54) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_716]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1375,plain,
% 2.80/0.99      ( k1_relat_1(X0_54) = X0_55
% 2.80/0.99      | v1_funct_2(X0_54,X0_55,k2_struct_0(sK1)) != iProver_top
% 2.80/0.99      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,k2_struct_0(sK1)))) != iProver_top
% 2.80/0.99      | v1_funct_1(X0_54) != iProver_top
% 2.80/0.99      | v1_relat_1(X0_54) != iProver_top ),
% 2.80/0.99      inference(light_normalisation,[status(thm)],[c_1280,c_719]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1772,plain,
% 2.80/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.80/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.80/0.99      | v1_funct_1(sK2) != iProver_top
% 2.80/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_1301,c_1375]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_31,negated_conjecture,
% 2.80/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.80/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_721,negated_conjecture,
% 2.80/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.80/0.99      inference(subtyping,[status(esa)],[c_31]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1276,plain,
% 2.80/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_721]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1295,plain,
% 2.80/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.80/0.99      inference(light_normalisation,[status(thm)],[c_1276,c_718,c_719]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1483,plain,
% 2.80/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
% 2.80/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1295]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1773,plain,
% 2.80/0.99      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
% 2.80/0.99      | ~ v1_funct_1(sK2)
% 2.80/0.99      | ~ v1_relat_1(sK2)
% 2.80/0.99      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.80/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1772]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1800,plain,
% 2.80/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.80/0.99      inference(global_propositional_subsumption,
% 2.80/0.99                [status(thm)],
% 2.80/0.99                [c_1772,c_32,c_30,c_1483,c_1773,c_1774,c_1789]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1803,plain,
% 2.80/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) = iProver_top ),
% 2.80/0.99      inference(demodulation,[status(thm)],[c_1800,c_1301]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_15,plain,
% 2.80/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.80/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_729,plain,
% 2.80/0.99      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.80/0.99      | k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54) ),
% 2.80/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1269,plain,
% 2.80/0.99      ( k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54)
% 2.80/0.99      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_729]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2082,plain,
% 2.80/0.99      ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_1803,c_1269]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_29,negated_conjecture,
% 2.80/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.80/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_723,negated_conjecture,
% 2.80/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.80/0.99      inference(subtyping,[status(esa)],[c_29]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1298,plain,
% 2.80/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.80/0.99      inference(light_normalisation,[status(thm)],[c_723,c_718,c_719]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1805,plain,
% 2.80/0.99      ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.80/0.99      inference(demodulation,[status(thm)],[c_1800,c_1298]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2422,plain,
% 2.80/0.99      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.80/0.99      inference(demodulation,[status(thm)],[c_2082,c_1805]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2827,plain,
% 2.80/0.99      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.80/0.99      inference(demodulation,[status(thm)],[c_2422,c_2082]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_21,plain,
% 2.80/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.80/0.99      | ~ v1_funct_1(X0)
% 2.80/0.99      | ~ v2_funct_1(X0)
% 2.80/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.80/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_728,plain,
% 2.80/0.99      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 2.80/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.80/0.99      | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55)))
% 2.80/0.99      | ~ v1_funct_1(X0_54)
% 2.80/0.99      | ~ v2_funct_1(X0_54)
% 2.80/0.99      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
% 2.80/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1270,plain,
% 2.80/0.99      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 2.80/0.99      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 2.80/0.99      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.80/0.99      | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) = iProver_top
% 2.80/0.99      | v1_funct_1(X0_54) != iProver_top
% 2.80/0.99      | v2_funct_1(X0_54) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3176,plain,
% 2.80/0.99      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.80/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 2.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.80/0.99      | v1_funct_1(sK2) != iProver_top
% 2.80/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_2827,c_1270]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3177,plain,
% 2.80/0.99      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.80/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 2.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.80/0.99      | v1_funct_1(sK2) != iProver_top
% 2.80/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.80/0.99      inference(light_normalisation,[status(thm)],[c_3176,c_2177]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2829,plain,
% 2.80/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 2.80/0.99      inference(demodulation,[status(thm)],[c_2422,c_1803]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1804,plain,
% 2.80/0.99      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) = iProver_top ),
% 2.80/0.99      inference(demodulation,[status(thm)],[c_1800,c_1295]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2830,plain,
% 2.80/0.99      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 2.80/0.99      inference(demodulation,[status(thm)],[c_2422,c_1804]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3836,plain,
% 2.80/0.99      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 2.80/0.99      inference(global_propositional_subsumption,
% 2.80/0.99                [status(thm)],
% 2.80/0.99                [c_3177,c_39,c_42,c_2829,c_2830]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3842,plain,
% 2.80/0.99      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2)) ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_3836,c_1269]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2,plain,
% 2.80/0.99      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 2.80/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_741,plain,
% 2.80/0.99      ( ~ v1_relat_1(X0_54)
% 2.80/0.99      | k2_relat_1(k4_relat_1(X0_54)) = k1_relat_1(X0_54) ),
% 2.80/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1257,plain,
% 2.80/0.99      ( k2_relat_1(k4_relat_1(X0_54)) = k1_relat_1(X0_54)
% 2.80/0.99      | v1_relat_1(X0_54) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_741]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1798,plain,
% 2.80/0.99      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_1793,c_1257]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3845,plain,
% 2.80/0.99      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.80/0.99      inference(light_normalisation,[status(thm)],[c_3842,c_1798]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_26,plain,
% 2.80/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/0.99      | ~ v1_funct_1(X0)
% 2.80/0.99      | ~ v2_funct_1(X0)
% 2.80/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.80/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.80/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_725,plain,
% 2.80/0.99      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 2.80/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.80/0.99      | ~ v1_funct_1(X0_54)
% 2.80/0.99      | ~ v2_funct_1(X0_54)
% 2.80/0.99      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 2.80/0.99      | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54) ),
% 2.80/0.99      inference(subtyping,[status(esa)],[c_26]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1273,plain,
% 2.80/0.99      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 2.80/0.99      | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54)
% 2.80/0.99      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 2.80/0.99      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.80/0.99      | v1_funct_1(X0_54) != iProver_top
% 2.80/0.99      | v2_funct_1(X0_54) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_725]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4124,plain,
% 2.80/0.99      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_funct_1(k4_relat_1(sK2))
% 2.80/0.99      | v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.80/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.80/0.99      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 2.80/0.99      | v2_funct_1(k4_relat_1(sK2)) != iProver_top ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_3845,c_1273]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_13,plain,
% 2.80/0.99      ( ~ v1_funct_1(X0)
% 2.80/0.99      | ~ v2_funct_1(X0)
% 2.80/0.99      | ~ v1_relat_1(X0)
% 2.80/0.99      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.80/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_730,plain,
% 2.80/0.99      ( ~ v1_funct_1(X0_54)
% 2.80/0.99      | ~ v2_funct_1(X0_54)
% 2.80/0.99      | ~ v1_relat_1(X0_54)
% 2.80/0.99      | k2_funct_1(k2_funct_1(X0_54)) = X0_54 ),
% 2.80/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1268,plain,
% 2.80/0.99      ( k2_funct_1(k2_funct_1(X0_54)) = X0_54
% 2.80/0.99      | v1_funct_1(X0_54) != iProver_top
% 2.80/0.99      | v2_funct_1(X0_54) != iProver_top
% 2.80/0.99      | v1_relat_1(X0_54) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_730]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2550,plain,
% 2.80/0.99      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.80/0.99      | v2_funct_1(sK2) != iProver_top
% 2.80/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_1277,c_1268]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2572,plain,
% 2.80/0.99      ( k2_funct_1(k4_relat_1(sK2)) = sK2
% 2.80/0.99      | v2_funct_1(sK2) != iProver_top
% 2.80/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.80/0.99      inference(light_normalisation,[status(thm)],[c_2550,c_2177]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2937,plain,
% 2.80/0.99      ( k2_funct_1(k4_relat_1(sK2)) = sK2 ),
% 2.80/0.99      inference(global_propositional_subsumption,
% 2.80/0.99                [status(thm)],
% 2.80/0.99                [c_2572,c_41,c_42,c_1775,c_1790]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4144,plain,
% 2.80/0.99      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = sK2
% 2.80/0.99      | v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.80/0.99      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.80/0.99      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 2.80/0.99      | v2_funct_1(k4_relat_1(sK2)) != iProver_top ),
% 2.80/0.99      inference(light_normalisation,[status(thm)],[c_4124,c_2937]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_22,plain,
% 2.80/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.80/0.99      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/0.99      | ~ v1_funct_1(X0)
% 2.80/0.99      | ~ v2_funct_1(X0)
% 2.80/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.80/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_727,plain,
% 2.80/0.99      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 2.80/0.99      | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55)
% 2.80/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.80/0.99      | ~ v1_funct_1(X0_54)
% 2.80/0.99      | ~ v2_funct_1(X0_54)
% 2.80/0.99      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
% 2.80/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1271,plain,
% 2.80/0.99      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 2.80/0.99      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 2.80/0.99      | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55) = iProver_top
% 2.80/0.99      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.80/0.99      | v1_funct_1(X0_54) != iProver_top
% 2.80/0.99      | v2_funct_1(X0_54) != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_727]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3327,plain,
% 2.80/0.99      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 2.80/0.99      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.80/0.99      | v1_funct_1(sK2) != iProver_top
% 2.80/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_2827,c_1271]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3328,plain,
% 2.80/0.99      ( v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 2.80/0.99      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.80/0.99      | v1_funct_1(sK2) != iProver_top
% 2.80/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.80/0.99      inference(light_normalisation,[status(thm)],[c_3327,c_2177]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4481,plain,
% 2.80/0.99      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = sK2
% 2.80/0.99      | v2_funct_1(k4_relat_1(sK2)) != iProver_top ),
% 2.80/0.99      inference(global_propositional_subsumption,
% 2.80/0.99                [status(thm)],
% 2.80/0.99                [c_4144,c_39,c_41,c_42,c_1775,c_1790,c_2181,c_2829,
% 2.80/0.99                 c_2830,c_3177,c_3328]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4933,plain,
% 2.80/0.99      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = sK2 ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_4931,c_4481]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_20,plain,
% 2.80/0.99      ( r2_funct_2(X0,X1,X2,X2)
% 2.80/0.99      | ~ v1_funct_2(X2,X0,X1)
% 2.80/0.99      | ~ v1_funct_2(X3,X0,X1)
% 2.80/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.80/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.80/0.99      | ~ v1_funct_1(X2)
% 2.80/0.99      | ~ v1_funct_1(X3) ),
% 2.80/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_27,negated_conjecture,
% 2.80/0.99      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 2.80/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_437,plain,
% 2.80/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.80/0.99      | ~ v1_funct_2(X3,X1,X2)
% 2.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/0.99      | ~ v1_funct_1(X0)
% 2.80/0.99      | ~ v1_funct_1(X3)
% 2.80/0.99      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 2.80/0.99      | u1_struct_0(sK1) != X2
% 2.80/0.99      | u1_struct_0(sK0) != X1
% 2.80/0.99      | sK2 != X0 ),
% 2.80/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_438,plain,
% 2.80/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.80/0.99      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.80/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.80/0.99      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.80/0.99      | ~ v1_funct_1(X0)
% 2.80/0.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.80/0.99      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.80/0.99      inference(unflattening,[status(thm)],[c_437]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_717,plain,
% 2.80/0.99      ( ~ v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.80/0.99      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.80/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.80/0.99      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.80/0.99      | ~ v1_funct_1(X0_54)
% 2.80/0.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.80/0.99      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.80/0.99      inference(subtyping,[status(esa)],[c_438]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_745,plain,
% 2.80/0.99      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.80/0.99      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.80/0.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.80/0.99      | sP0_iProver_split
% 2.80/0.99      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.80/0.99      inference(splitting,
% 2.80/0.99                [splitting(split),new_symbols(definition,[])],
% 2.80/0.99                [c_717]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1278,plain,
% 2.80/0.99      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.80/0.99      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.80/0.99      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.80/0.99      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
% 2.80/0.99      | sP0_iProver_split = iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_745]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1462,plain,
% 2.80/0.99      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.80/0.99      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.80/0.99      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.80/0.99      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
% 2.80/0.99      | sP0_iProver_split = iProver_top ),
% 2.80/0.99      inference(light_normalisation,[status(thm)],[c_1278,c_718,c_719]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_744,plain,
% 2.80/0.99      ( ~ v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.80/0.99      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.80/0.99      | ~ v1_funct_1(X0_54)
% 2.80/0.99      | ~ sP0_iProver_split ),
% 2.80/0.99      inference(splitting,
% 2.80/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.80/0.99                [c_717]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1279,plain,
% 2.80/0.99      ( v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.80/0.99      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.80/0.99      | v1_funct_1(X0_54) != iProver_top
% 2.80/0.99      | sP0_iProver_split != iProver_top ),
% 2.80/0.99      inference(predicate_to_equality,[status(thm)],[c_744]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1366,plain,
% 2.80/0.99      ( v1_funct_2(X0_54,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.80/0.99      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.80/0.99      | v1_funct_1(X0_54) != iProver_top
% 2.80/0.99      | sP0_iProver_split != iProver_top ),
% 2.80/0.99      inference(light_normalisation,[status(thm)],[c_1279,c_718,c_719]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1468,plain,
% 2.80/0.99      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.80/0.99      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.80/0.99      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.80/0.99      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.80/0.99      inference(forward_subsumption_resolution,
% 2.80/0.99                [status(thm)],
% 2.80/0.99                [c_1462,c_1366]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1912,plain,
% 2.80/0.99      ( k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) != sK2
% 2.80/0.99      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_relat_1(sK2),k2_struct_0(sK1)) != iProver_top
% 2.80/0.99      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) != iProver_top
% 2.80/0.99      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.80/0.99      inference(light_normalisation,[status(thm)],[c_1468,c_1800]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2828,plain,
% 2.80/0.99      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
% 2.80/0.99      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.80/0.99      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.80/0.99      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
% 2.80/0.99      inference(demodulation,[status(thm)],[c_2422,c_1912]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3481,plain,
% 2.80/0.99      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 2.80/0.99      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.80/0.99      | v1_funct_1(sK2) != iProver_top
% 2.80/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.80/0.99      inference(superposition,[status(thm)],[c_2827,c_1273]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3482,plain,
% 2.80/0.99      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k4_relat_1(sK2)
% 2.80/0.99      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.80/0.99      | v1_funct_1(sK2) != iProver_top
% 2.80/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.80/0.99      inference(light_normalisation,[status(thm)],[c_3481,c_2177]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3741,plain,
% 2.80/0.99      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k4_relat_1(sK2) ),
% 2.80/0.99      inference(global_propositional_subsumption,
% 2.80/0.99                [status(thm)],
% 2.80/0.99                [c_3482,c_39,c_42,c_2829,c_2830]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_4007,plain,
% 2.80/0.99      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) != sK2
% 2.80/0.99      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.80/0.99      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.80/0.99      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))) != iProver_top ),
% 2.80/0.99      inference(light_normalisation,[status(thm)],[c_2828,c_3741]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_5378,plain,
% 2.80/0.99      ( sK2 != sK2
% 2.80/0.99      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.80/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.80/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.80/0.99      inference(demodulation,[status(thm)],[c_4933,c_4007]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_747,plain,( X0_54 = X0_54 ),theory(equality) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_781,plain,
% 2.80/0.99      ( sK2 = sK2 ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_747]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(contradiction,plain,
% 2.80/0.99      ( $false ),
% 2.80/0.99      inference(minisat,[status(thm)],[c_5378,c_2830,c_2829,c_781,c_39]) ).
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.80/0.99  
% 2.80/0.99  ------                               Statistics
% 2.80/0.99  
% 2.80/0.99  ------ General
% 2.80/0.99  
% 2.80/0.99  abstr_ref_over_cycles:                  0
% 2.80/0.99  abstr_ref_under_cycles:                 0
% 2.80/0.99  gc_basic_clause_elim:                   0
% 2.80/0.99  forced_gc_time:                         0
% 2.80/0.99  parsing_time:                           0.01
% 2.80/0.99  unif_index_cands_time:                  0.
% 2.80/0.99  unif_index_add_time:                    0.
% 2.80/0.99  orderings_time:                         0.
% 2.80/0.99  out_proof_time:                         0.014
% 2.80/0.99  total_time:                             0.21
% 2.80/0.99  num_of_symbols:                         62
% 2.80/0.99  num_of_terms:                           5019
% 2.80/0.99  
% 2.80/0.99  ------ Preprocessing
% 2.80/0.99  
% 2.80/0.99  num_of_splits:                          1
% 2.80/0.99  num_of_split_atoms:                     1
% 2.80/0.99  num_of_reused_defs:                     0
% 2.80/0.99  num_eq_ax_congr_red:                    7
% 2.80/0.99  num_of_sem_filtered_clauses:            2
% 2.80/0.99  num_of_subtypes:                        4
% 2.80/0.99  monotx_restored_types:                  1
% 2.80/0.99  sat_num_of_epr_types:                   0
% 2.80/0.99  sat_num_of_non_cyclic_types:            0
% 2.80/0.99  sat_guarded_non_collapsed_types:        1
% 2.80/0.99  num_pure_diseq_elim:                    0
% 2.80/0.99  simp_replaced_by:                       0
% 2.80/0.99  res_preprocessed:                       159
% 2.80/0.99  prep_upred:                             0
% 2.80/0.99  prep_unflattend:                        11
% 2.80/0.99  smt_new_axioms:                         0
% 2.80/0.99  pred_elim_cands:                        5
% 2.80/0.99  pred_elim:                              6
% 2.80/0.99  pred_elim_cl:                           7
% 2.80/0.99  pred_elim_cycles:                       9
% 2.80/0.99  merged_defs:                            0
% 2.80/0.99  merged_defs_ncl:                        0
% 2.80/0.99  bin_hyper_res:                          0
% 2.80/0.99  prep_cycles:                            4
% 2.80/0.99  pred_elim_time:                         0.005
% 2.80/0.99  splitting_time:                         0.
% 2.80/0.99  sem_filter_time:                        0.
% 2.80/0.99  monotx_time:                            0.001
% 2.80/0.99  subtype_inf_time:                       0.002
% 2.80/0.99  
% 2.80/0.99  ------ Problem properties
% 2.80/0.99  
% 2.80/0.99  clauses:                                29
% 2.80/0.99  conjectures:                            5
% 2.80/0.99  epr:                                    2
% 2.80/0.99  horn:                                   29
% 2.80/0.99  ground:                                 8
% 2.80/0.99  unary:                                  10
% 2.80/0.99  binary:                                 3
% 2.80/0.99  lits:                                   93
% 2.80/0.99  lits_eq:                                19
% 2.80/0.99  fd_pure:                                0
% 2.80/0.99  fd_pseudo:                              0
% 2.80/0.99  fd_cond:                                0
% 2.80/0.99  fd_pseudo_cond:                         1
% 2.80/0.99  ac_symbols:                             0
% 2.80/0.99  
% 2.80/0.99  ------ Propositional Solver
% 2.80/0.99  
% 2.80/0.99  prop_solver_calls:                      30
% 2.80/0.99  prop_fast_solver_calls:                 1303
% 2.80/0.99  smt_solver_calls:                       0
% 2.80/0.99  smt_fast_solver_calls:                  0
% 2.80/0.99  prop_num_of_clauses:                    1956
% 2.80/0.99  prop_preprocess_simplified:             6259
% 2.80/0.99  prop_fo_subsumed:                       61
% 2.80/0.99  prop_solver_time:                       0.
% 2.80/0.99  smt_solver_time:                        0.
% 2.80/0.99  smt_fast_solver_time:                   0.
% 2.80/0.99  prop_fast_solver_time:                  0.
% 2.80/0.99  prop_unsat_core_time:                   0.
% 2.80/0.99  
% 2.80/0.99  ------ QBF
% 2.80/0.99  
% 2.80/0.99  qbf_q_res:                              0
% 2.80/0.99  qbf_num_tautologies:                    0
% 2.80/0.99  qbf_prep_cycles:                        0
% 2.80/0.99  
% 2.80/0.99  ------ BMC1
% 2.80/0.99  
% 2.80/0.99  bmc1_current_bound:                     -1
% 2.80/0.99  bmc1_last_solved_bound:                 -1
% 2.80/0.99  bmc1_unsat_core_size:                   -1
% 2.80/0.99  bmc1_unsat_core_parents_size:           -1
% 2.80/0.99  bmc1_merge_next_fun:                    0
% 2.80/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.80/0.99  
% 2.80/0.99  ------ Instantiation
% 2.80/0.99  
% 2.80/0.99  inst_num_of_clauses:                    657
% 2.80/0.99  inst_num_in_passive:                    33
% 2.80/0.99  inst_num_in_active:                     362
% 2.80/0.99  inst_num_in_unprocessed:                262
% 2.80/0.99  inst_num_of_loops:                      390
% 2.80/0.99  inst_num_of_learning_restarts:          0
% 2.80/0.99  inst_num_moves_active_passive:          23
% 2.80/0.99  inst_lit_activity:                      0
% 2.80/0.99  inst_lit_activity_moves:                0
% 2.80/0.99  inst_num_tautologies:                   0
% 2.80/0.99  inst_num_prop_implied:                  0
% 2.80/0.99  inst_num_existing_simplified:           0
% 2.80/0.99  inst_num_eq_res_simplified:             0
% 2.80/0.99  inst_num_child_elim:                    0
% 2.80/0.99  inst_num_of_dismatching_blockings:      152
% 2.80/0.99  inst_num_of_non_proper_insts:           651
% 2.80/0.99  inst_num_of_duplicates:                 0
% 2.80/0.99  inst_inst_num_from_inst_to_res:         0
% 2.80/0.99  inst_dismatching_checking_time:         0.
% 2.80/0.99  
% 2.80/0.99  ------ Resolution
% 2.80/0.99  
% 2.80/0.99  res_num_of_clauses:                     0
% 2.80/0.99  res_num_in_passive:                     0
% 2.80/0.99  res_num_in_active:                      0
% 2.80/0.99  res_num_of_loops:                       163
% 2.80/0.99  res_forward_subset_subsumed:            71
% 2.80/0.99  res_backward_subset_subsumed:           0
% 2.80/0.99  res_forward_subsumed:                   0
% 2.80/0.99  res_backward_subsumed:                  0
% 2.80/0.99  res_forward_subsumption_resolution:     1
% 2.80/0.99  res_backward_subsumption_resolution:    0
% 2.80/0.99  res_clause_to_clause_subsumption:       250
% 2.80/0.99  res_orphan_elimination:                 0
% 2.80/0.99  res_tautology_del:                      74
% 2.80/0.99  res_num_eq_res_simplified:              0
% 2.80/0.99  res_num_sel_changes:                    0
% 2.80/0.99  res_moves_from_active_to_pass:          0
% 2.80/0.99  
% 2.80/0.99  ------ Superposition
% 2.80/0.99  
% 2.80/0.99  sup_time_total:                         0.
% 2.80/0.99  sup_time_generating:                    0.
% 2.80/0.99  sup_time_sim_full:                      0.
% 2.80/0.99  sup_time_sim_immed:                     0.
% 2.80/0.99  
% 2.80/0.99  sup_num_of_clauses:                     89
% 2.80/0.99  sup_num_in_active:                      60
% 2.80/0.99  sup_num_in_passive:                     29
% 2.80/0.99  sup_num_of_loops:                       76
% 2.80/0.99  sup_fw_superposition:                   61
% 2.80/0.99  sup_bw_superposition:                   33
% 2.80/0.99  sup_immediate_simplified:               37
% 2.80/0.99  sup_given_eliminated:                   0
% 2.80/0.99  comparisons_done:                       0
% 2.80/0.99  comparisons_avoided:                    0
% 2.80/0.99  
% 2.80/0.99  ------ Simplifications
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  sim_fw_subset_subsumed:                 8
% 2.80/0.99  sim_bw_subset_subsumed:                 2
% 2.80/0.99  sim_fw_subsumed:                        4
% 2.80/0.99  sim_bw_subsumed:                        0
% 2.80/0.99  sim_fw_subsumption_res:                 2
% 2.80/0.99  sim_bw_subsumption_res:                 0
% 2.80/0.99  sim_tautology_del:                      0
% 2.80/0.99  sim_eq_tautology_del:                   20
% 2.80/0.99  sim_eq_res_simp:                        0
% 2.80/0.99  sim_fw_demodulated:                     0
% 2.80/0.99  sim_bw_demodulated:                     14
% 2.80/0.99  sim_light_normalised:                   43
% 2.80/0.99  sim_joinable_taut:                      0
% 2.80/0.99  sim_joinable_simp:                      0
% 2.80/0.99  sim_ac_normalised:                      0
% 2.80/0.99  sim_smt_subsumption:                    0
% 2.80/0.99  
%------------------------------------------------------------------------------
