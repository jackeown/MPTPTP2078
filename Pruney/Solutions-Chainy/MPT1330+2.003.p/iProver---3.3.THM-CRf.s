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
% DateTime   : Thu Dec  3 12:16:53 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :  159 (1831 expanded)
%              Number of clauses        :   98 ( 547 expanded)
%              Number of leaves         :   16 ( 507 expanded)
%              Depth                    :   23
%              Number of atoms          :  484 (10395 expanded)
%              Number of equality atoms :  248 (4191 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f24,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( k1_xboole_0 = k2_struct_0(X1)
                   => k1_xboole_0 = k2_struct_0(X0) )
                 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0)
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0)
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0)
          & ( k1_xboole_0 = k2_struct_0(X0)
            | k1_xboole_0 != k2_struct_0(X1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,k2_struct_0(X1)) != k2_struct_0(X0)
        & ( k1_xboole_0 = k2_struct_0(X0)
          | k1_xboole_0 != k2_struct_0(X1) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0)
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
     => ( ? [X2] :
            ( k8_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2,k2_struct_0(sK2)) != k2_struct_0(X0)
            & ( k1_xboole_0 = k2_struct_0(X0)
              | k1_xboole_0 != k2_struct_0(sK2) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2))
            & v1_funct_1(X2) )
        & l1_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0)
                & ( k1_xboole_0 = k2_struct_0(X0)
                  | k1_xboole_0 != k2_struct_0(X1) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(sK1)
              & ( k1_xboole_0 = k2_struct_0(sK1)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1)
    & ( k1_xboole_0 = k2_struct_0(sK1)
      | k1_xboole_0 != k2_struct_0(sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_struct_0(sK2)
    & l1_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f48,f57,f56,f55])).

fof(f94,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f58])).

fof(f93,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f95,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f58])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f90,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f92,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f91,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f96,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k1_xboole_0 != k2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f97,plain,(
    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f101,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f89])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f49])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f99,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f98,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f63])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_475,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK2) != X2
    | u1_struct_0(sK1) != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_35])).

cnf(c_476,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_478,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1))
    | k1_xboole_0 = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_476,c_36,c_34])).

cnf(c_24,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_28,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_418,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_24,c_28])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_418,c_28,c_24,c_22])).

cnf(c_421,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_420])).

cnf(c_570,plain,
    ( ~ v1_partfun1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | k1_relat_1(X0) = X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_421,c_34])).

cnf(c_571,plain,
    ( ~ v1_partfun1(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_relat_1(sK3) = X0 ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_741,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK1) != X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_relat_1(sK3) = X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_478,c_571])).

cnf(c_742,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0))
    | k1_relat_1(sK3) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_741])).

cnf(c_921,plain,
    ( sP0_iProver_split
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(sK3) = u1_struct_0(sK1) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_742])).

cnf(c_1256,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(sK3) = u1_struct_0(sK1)
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_921])).

cnf(c_31,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_37,negated_conjecture,
    ( l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_384,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_37])).

cnf(c_385,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_38,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_389,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_38])).

cnf(c_390,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_1320,plain,
    ( k2_struct_0(sK2) = k1_xboole_0
    | k2_struct_0(sK1) = k1_relat_1(sK3)
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_1256,c_385,c_390])).

cnf(c_920,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_742])).

cnf(c_1257,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_920])).

cnf(c_1358,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),X0))
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1257,c_385,c_390])).

cnf(c_1504,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1358])).

cnf(c_1803,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | k2_struct_0(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1320,c_1504])).

cnf(c_1804,plain,
    ( k2_struct_0(sK2) = k1_xboole_0
    | k2_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_1803])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != k2_struct_0(sK2)
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1815,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1804,c_33])).

cnf(c_7,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_397,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_23])).

cnf(c_398,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_402,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_398,c_22])).

cnf(c_403,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_402])).

cnf(c_585,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_403,c_34])).

cnf(c_586,plain,
    ( r1_tarski(k2_relat_1(sK3),X0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_585])).

cnf(c_1261,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r1_tarski(k2_relat_1(sK3),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_1363,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r1_tarski(k2_relat_1(sK3),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1261,c_385,c_390])).

cnf(c_1720,plain,
    ( r1_tarski(k2_relat_1(sK3),k2_struct_0(sK2)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1363])).

cnf(c_18,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1265,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4064,plain,
    ( k5_relat_1(sK3,k6_relat_1(k2_struct_0(sK2))) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1720,c_1265])).

cnf(c_606,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_34])).

cnf(c_607,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_606])).

cnf(c_1260,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_607])).

cnf(c_1348,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1260,c_385,c_390])).

cnf(c_1476,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1348])).

cnf(c_4462,plain,
    ( k5_relat_1(sK3,k6_relat_1(k2_struct_0(sK2))) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4064,c_1476])).

cnf(c_8,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1269,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1267,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5128,plain,
    ( k10_relat_1(sK3,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK3,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1476,c_1267])).

cnf(c_5645,plain,
    ( k10_relat_1(sK3,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_1269,c_5128])).

cnf(c_17,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_5654,plain,
    ( k1_relat_1(k5_relat_1(sK3,k6_relat_1(X0))) = k10_relat_1(sK3,X0) ),
    inference(light_normalisation,[status(thm)],[c_5645,c_17])).

cnf(c_6230,plain,
    ( k10_relat_1(sK3,k2_struct_0(sK2)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_4462,c_5654])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_597,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_34])).

cnf(c_598,plain,
    ( k8_relset_1(X0,X1,sK3,X2) = k10_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_597])).

cnf(c_1380,plain,
    ( k8_relset_1(X0,X1,sK3,X2) = k10_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_598,c_385,c_390])).

cnf(c_1793,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(equality_resolution,[status(thm)],[c_1380])).

cnf(c_32,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1317,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_32,c_385,c_390])).

cnf(c_2488,plain,
    ( k10_relat_1(sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1793,c_1317])).

cnf(c_6235,plain,
    ( k2_struct_0(sK1) != k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_6230,c_2488])).

cnf(c_6318,plain,
    ( k2_struct_0(sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1815,c_6235])).

cnf(c_6320,plain,
    ( k1_relat_1(sK3) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6318,c_6235])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_458,plain,
    ( v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK2) != X1
    | u1_struct_0(sK1) != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_35])).

cnf(c_459,plain,
    ( v1_partfun1(sK3,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))))
    | ~ v1_funct_1(sK3)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_461,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))))
    | v1_partfun1(sK3,k1_xboole_0)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_459,c_36])).

cnf(c_462,plain,
    ( v1_partfun1(sK3,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))))
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_461])).

cnf(c_630,plain,
    ( v1_partfun1(sK3,k1_xboole_0)
    | u1_struct_0(sK1) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2)))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_462])).

cnf(c_726,plain,
    ( u1_struct_0(sK1) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2)))
    | k1_relat_1(sK3) = X0
    | sK3 != sK3
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_630,c_571])).

cnf(c_727,plain,
    ( u1_struct_0(sK1) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2)))
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_726])).

cnf(c_923,plain,
    ( sP1_iProver_split
    | u1_struct_0(sK1) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2)))
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_727])).

cnf(c_1258,plain,
    ( u1_struct_0(sK1) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2)))
    | k1_relat_1(sK3) = k1_xboole_0
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_923])).

cnf(c_1385,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK2)))
    | k1_relat_1(sK3) = k1_xboole_0
    | sP1_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1258,c_385,c_390])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1386,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k1_xboole_0)
    | k1_relat_1(sK3) = k1_xboole_0
    | sP1_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_1385,c_3])).

cnf(c_922,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_727])).

cnf(c_1259,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_922])).

cnf(c_1343,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k1_xboole_0)
    | sP1_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1259,c_3,c_385,c_390])).

cnf(c_1391,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k1_xboole_0)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1386,c_1343])).

cnf(c_3263,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | k2_struct_0(sK1) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1804,c_1391])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_3268,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | k2_struct_0(sK1) != k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3263,c_2])).

cnf(c_3269,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | k2_struct_0(sK1) != k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3268])).

cnf(c_4636,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3269,c_1815])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6320,c_6235,c_4636])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:32:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.87/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.02  
% 1.87/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.87/1.02  
% 1.87/1.02  ------  iProver source info
% 1.87/1.02  
% 1.87/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.87/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.87/1.02  git: non_committed_changes: false
% 1.87/1.02  git: last_make_outside_of_git: false
% 1.87/1.02  
% 1.87/1.02  ------ 
% 1.87/1.02  
% 1.87/1.02  ------ Input Options
% 1.87/1.02  
% 1.87/1.02  --out_options                           all
% 1.87/1.02  --tptp_safe_out                         true
% 1.87/1.02  --problem_path                          ""
% 1.87/1.02  --include_path                          ""
% 1.87/1.02  --clausifier                            res/vclausify_rel
% 1.87/1.02  --clausifier_options                    --mode clausify
% 1.87/1.02  --stdin                                 false
% 1.87/1.02  --stats_out                             all
% 1.87/1.02  
% 1.87/1.02  ------ General Options
% 1.87/1.02  
% 1.87/1.02  --fof                                   false
% 1.87/1.02  --time_out_real                         305.
% 1.87/1.02  --time_out_virtual                      -1.
% 1.87/1.02  --symbol_type_check                     false
% 1.87/1.02  --clausify_out                          false
% 1.87/1.02  --sig_cnt_out                           false
% 1.87/1.02  --trig_cnt_out                          false
% 1.87/1.02  --trig_cnt_out_tolerance                1.
% 1.87/1.02  --trig_cnt_out_sk_spl                   false
% 1.87/1.02  --abstr_cl_out                          false
% 1.87/1.02  
% 1.87/1.02  ------ Global Options
% 1.87/1.02  
% 1.87/1.02  --schedule                              default
% 1.87/1.02  --add_important_lit                     false
% 1.87/1.02  --prop_solver_per_cl                    1000
% 1.87/1.02  --min_unsat_core                        false
% 1.87/1.02  --soft_assumptions                      false
% 1.87/1.02  --soft_lemma_size                       3
% 1.87/1.02  --prop_impl_unit_size                   0
% 1.87/1.02  --prop_impl_unit                        []
% 1.87/1.02  --share_sel_clauses                     true
% 1.87/1.02  --reset_solvers                         false
% 1.87/1.02  --bc_imp_inh                            [conj_cone]
% 1.87/1.02  --conj_cone_tolerance                   3.
% 1.87/1.02  --extra_neg_conj                        none
% 1.87/1.02  --large_theory_mode                     true
% 1.87/1.02  --prolific_symb_bound                   200
% 1.87/1.02  --lt_threshold                          2000
% 1.87/1.02  --clause_weak_htbl                      true
% 1.87/1.02  --gc_record_bc_elim                     false
% 1.87/1.02  
% 1.87/1.02  ------ Preprocessing Options
% 1.87/1.02  
% 1.87/1.02  --preprocessing_flag                    true
% 1.87/1.02  --time_out_prep_mult                    0.1
% 1.87/1.02  --splitting_mode                        input
% 1.87/1.02  --splitting_grd                         true
% 1.87/1.02  --splitting_cvd                         false
% 1.87/1.02  --splitting_cvd_svl                     false
% 1.87/1.02  --splitting_nvd                         32
% 1.87/1.02  --sub_typing                            true
% 1.87/1.02  --prep_gs_sim                           true
% 1.87/1.02  --prep_unflatten                        true
% 1.87/1.02  --prep_res_sim                          true
% 1.87/1.02  --prep_upred                            true
% 1.87/1.02  --prep_sem_filter                       exhaustive
% 1.87/1.02  --prep_sem_filter_out                   false
% 1.87/1.02  --pred_elim                             true
% 1.87/1.02  --res_sim_input                         true
% 1.87/1.02  --eq_ax_congr_red                       true
% 1.87/1.02  --pure_diseq_elim                       true
% 1.87/1.02  --brand_transform                       false
% 1.87/1.02  --non_eq_to_eq                          false
% 1.87/1.02  --prep_def_merge                        true
% 1.87/1.02  --prep_def_merge_prop_impl              false
% 1.87/1.02  --prep_def_merge_mbd                    true
% 1.87/1.02  --prep_def_merge_tr_red                 false
% 1.87/1.02  --prep_def_merge_tr_cl                  false
% 1.87/1.02  --smt_preprocessing                     true
% 1.87/1.02  --smt_ac_axioms                         fast
% 1.87/1.02  --preprocessed_out                      false
% 1.87/1.02  --preprocessed_stats                    false
% 1.87/1.02  
% 1.87/1.02  ------ Abstraction refinement Options
% 1.87/1.02  
% 1.87/1.02  --abstr_ref                             []
% 1.87/1.02  --abstr_ref_prep                        false
% 1.87/1.02  --abstr_ref_until_sat                   false
% 1.87/1.02  --abstr_ref_sig_restrict                funpre
% 1.87/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.87/1.02  --abstr_ref_under                       []
% 1.87/1.02  
% 1.87/1.02  ------ SAT Options
% 1.87/1.02  
% 1.87/1.02  --sat_mode                              false
% 1.87/1.02  --sat_fm_restart_options                ""
% 1.87/1.02  --sat_gr_def                            false
% 1.87/1.02  --sat_epr_types                         true
% 1.87/1.02  --sat_non_cyclic_types                  false
% 1.87/1.02  --sat_finite_models                     false
% 1.87/1.02  --sat_fm_lemmas                         false
% 1.87/1.02  --sat_fm_prep                           false
% 1.87/1.02  --sat_fm_uc_incr                        true
% 1.87/1.02  --sat_out_model                         small
% 1.87/1.02  --sat_out_clauses                       false
% 1.87/1.02  
% 1.87/1.02  ------ QBF Options
% 1.87/1.02  
% 1.87/1.02  --qbf_mode                              false
% 1.87/1.02  --qbf_elim_univ                         false
% 1.87/1.02  --qbf_dom_inst                          none
% 1.87/1.02  --qbf_dom_pre_inst                      false
% 1.87/1.02  --qbf_sk_in                             false
% 1.87/1.02  --qbf_pred_elim                         true
% 1.87/1.02  --qbf_split                             512
% 1.87/1.02  
% 1.87/1.02  ------ BMC1 Options
% 1.87/1.02  
% 1.87/1.02  --bmc1_incremental                      false
% 1.87/1.02  --bmc1_axioms                           reachable_all
% 1.87/1.02  --bmc1_min_bound                        0
% 1.87/1.02  --bmc1_max_bound                        -1
% 1.87/1.02  --bmc1_max_bound_default                -1
% 1.87/1.02  --bmc1_symbol_reachability              true
% 1.87/1.02  --bmc1_property_lemmas                  false
% 1.87/1.02  --bmc1_k_induction                      false
% 1.87/1.02  --bmc1_non_equiv_states                 false
% 1.87/1.02  --bmc1_deadlock                         false
% 1.87/1.02  --bmc1_ucm                              false
% 1.87/1.02  --bmc1_add_unsat_core                   none
% 1.87/1.02  --bmc1_unsat_core_children              false
% 1.87/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.87/1.02  --bmc1_out_stat                         full
% 1.87/1.02  --bmc1_ground_init                      false
% 1.87/1.02  --bmc1_pre_inst_next_state              false
% 1.87/1.02  --bmc1_pre_inst_state                   false
% 1.87/1.02  --bmc1_pre_inst_reach_state             false
% 1.87/1.02  --bmc1_out_unsat_core                   false
% 1.87/1.02  --bmc1_aig_witness_out                  false
% 1.87/1.02  --bmc1_verbose                          false
% 1.87/1.02  --bmc1_dump_clauses_tptp                false
% 1.87/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.87/1.02  --bmc1_dump_file                        -
% 1.87/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.87/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.87/1.02  --bmc1_ucm_extend_mode                  1
% 1.87/1.02  --bmc1_ucm_init_mode                    2
% 1.87/1.02  --bmc1_ucm_cone_mode                    none
% 1.87/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.87/1.02  --bmc1_ucm_relax_model                  4
% 1.87/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.87/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.87/1.02  --bmc1_ucm_layered_model                none
% 1.87/1.02  --bmc1_ucm_max_lemma_size               10
% 1.87/1.02  
% 1.87/1.02  ------ AIG Options
% 1.87/1.02  
% 1.87/1.02  --aig_mode                              false
% 1.87/1.02  
% 1.87/1.02  ------ Instantiation Options
% 1.87/1.02  
% 1.87/1.02  --instantiation_flag                    true
% 1.87/1.02  --inst_sos_flag                         false
% 1.87/1.02  --inst_sos_phase                        true
% 1.87/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.87/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.87/1.02  --inst_lit_sel_side                     num_symb
% 1.87/1.02  --inst_solver_per_active                1400
% 1.87/1.02  --inst_solver_calls_frac                1.
% 1.87/1.02  --inst_passive_queue_type               priority_queues
% 1.87/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.87/1.02  --inst_passive_queues_freq              [25;2]
% 1.87/1.02  --inst_dismatching                      true
% 1.87/1.02  --inst_eager_unprocessed_to_passive     true
% 1.87/1.02  --inst_prop_sim_given                   true
% 1.87/1.02  --inst_prop_sim_new                     false
% 1.87/1.02  --inst_subs_new                         false
% 1.87/1.02  --inst_eq_res_simp                      false
% 1.87/1.02  --inst_subs_given                       false
% 1.87/1.02  --inst_orphan_elimination               true
% 1.87/1.02  --inst_learning_loop_flag               true
% 1.87/1.02  --inst_learning_start                   3000
% 1.87/1.02  --inst_learning_factor                  2
% 1.87/1.02  --inst_start_prop_sim_after_learn       3
% 1.87/1.02  --inst_sel_renew                        solver
% 1.87/1.02  --inst_lit_activity_flag                true
% 1.87/1.02  --inst_restr_to_given                   false
% 1.87/1.02  --inst_activity_threshold               500
% 1.87/1.02  --inst_out_proof                        true
% 1.87/1.02  
% 1.87/1.02  ------ Resolution Options
% 1.87/1.02  
% 1.87/1.02  --resolution_flag                       true
% 1.87/1.02  --res_lit_sel                           adaptive
% 1.87/1.02  --res_lit_sel_side                      none
% 1.87/1.02  --res_ordering                          kbo
% 1.87/1.02  --res_to_prop_solver                    active
% 1.87/1.02  --res_prop_simpl_new                    false
% 1.87/1.02  --res_prop_simpl_given                  true
% 1.87/1.02  --res_passive_queue_type                priority_queues
% 1.87/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.87/1.02  --res_passive_queues_freq               [15;5]
% 1.87/1.02  --res_forward_subs                      full
% 1.87/1.02  --res_backward_subs                     full
% 1.87/1.02  --res_forward_subs_resolution           true
% 1.87/1.02  --res_backward_subs_resolution          true
% 1.87/1.02  --res_orphan_elimination                true
% 1.87/1.02  --res_time_limit                        2.
% 1.87/1.02  --res_out_proof                         true
% 1.87/1.02  
% 1.87/1.02  ------ Superposition Options
% 1.87/1.02  
% 1.87/1.02  --superposition_flag                    true
% 1.87/1.02  --sup_passive_queue_type                priority_queues
% 1.87/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.87/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.87/1.02  --demod_completeness_check              fast
% 1.87/1.02  --demod_use_ground                      true
% 1.87/1.02  --sup_to_prop_solver                    passive
% 1.87/1.02  --sup_prop_simpl_new                    true
% 1.87/1.02  --sup_prop_simpl_given                  true
% 1.87/1.02  --sup_fun_splitting                     false
% 1.87/1.02  --sup_smt_interval                      50000
% 1.87/1.02  
% 1.87/1.02  ------ Superposition Simplification Setup
% 1.87/1.02  
% 1.87/1.02  --sup_indices_passive                   []
% 1.87/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.87/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/1.02  --sup_full_bw                           [BwDemod]
% 1.87/1.02  --sup_immed_triv                        [TrivRules]
% 1.87/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.87/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/1.02  --sup_immed_bw_main                     []
% 1.87/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.87/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/1.02  
% 1.87/1.02  ------ Combination Options
% 1.87/1.02  
% 1.87/1.02  --comb_res_mult                         3
% 1.87/1.02  --comb_sup_mult                         2
% 1.87/1.02  --comb_inst_mult                        10
% 1.87/1.02  
% 1.87/1.02  ------ Debug Options
% 1.87/1.02  
% 1.87/1.02  --dbg_backtrace                         false
% 1.87/1.02  --dbg_dump_prop_clauses                 false
% 1.87/1.02  --dbg_dump_prop_clauses_file            -
% 1.87/1.02  --dbg_out_stat                          false
% 1.87/1.02  ------ Parsing...
% 1.87/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.87/1.02  
% 1.87/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.87/1.02  
% 1.87/1.02  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.87/1.02  
% 1.87/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.87/1.02  ------ Proving...
% 1.87/1.02  ------ Problem Properties 
% 1.87/1.02  
% 1.87/1.02  
% 1.87/1.02  clauses                                 31
% 1.87/1.02  conjectures                             2
% 1.87/1.02  EPR                                     3
% 1.87/1.02  Horn                                    28
% 1.87/1.02  unary                                   13
% 1.87/1.02  binary                                  12
% 1.87/1.02  lits                                    56
% 1.87/1.02  lits eq                                 33
% 1.87/1.02  fd_pure                                 0
% 1.87/1.02  fd_pseudo                               0
% 1.87/1.02  fd_cond                                 2
% 1.87/1.02  fd_pseudo_cond                          1
% 1.87/1.02  AC symbols                              0
% 1.87/1.02  
% 1.87/1.02  ------ Schedule dynamic 5 is on 
% 1.87/1.02  
% 1.87/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.87/1.02  
% 1.87/1.02  
% 1.87/1.02  ------ 
% 1.87/1.02  Current options:
% 1.87/1.02  ------ 
% 1.87/1.02  
% 1.87/1.02  ------ Input Options
% 1.87/1.02  
% 1.87/1.02  --out_options                           all
% 1.87/1.02  --tptp_safe_out                         true
% 1.87/1.02  --problem_path                          ""
% 1.87/1.02  --include_path                          ""
% 1.87/1.02  --clausifier                            res/vclausify_rel
% 1.87/1.02  --clausifier_options                    --mode clausify
% 1.87/1.02  --stdin                                 false
% 1.87/1.02  --stats_out                             all
% 1.87/1.02  
% 1.87/1.02  ------ General Options
% 1.87/1.02  
% 1.87/1.02  --fof                                   false
% 1.87/1.02  --time_out_real                         305.
% 1.87/1.02  --time_out_virtual                      -1.
% 1.87/1.02  --symbol_type_check                     false
% 1.87/1.02  --clausify_out                          false
% 1.87/1.02  --sig_cnt_out                           false
% 1.87/1.02  --trig_cnt_out                          false
% 1.87/1.02  --trig_cnt_out_tolerance                1.
% 1.87/1.02  --trig_cnt_out_sk_spl                   false
% 1.87/1.02  --abstr_cl_out                          false
% 1.87/1.02  
% 1.87/1.02  ------ Global Options
% 1.87/1.02  
% 1.87/1.02  --schedule                              default
% 1.87/1.02  --add_important_lit                     false
% 1.87/1.02  --prop_solver_per_cl                    1000
% 1.87/1.02  --min_unsat_core                        false
% 1.87/1.02  --soft_assumptions                      false
% 1.87/1.02  --soft_lemma_size                       3
% 1.87/1.02  --prop_impl_unit_size                   0
% 1.87/1.02  --prop_impl_unit                        []
% 1.87/1.02  --share_sel_clauses                     true
% 1.87/1.02  --reset_solvers                         false
% 1.87/1.02  --bc_imp_inh                            [conj_cone]
% 1.87/1.02  --conj_cone_tolerance                   3.
% 1.87/1.02  --extra_neg_conj                        none
% 1.87/1.02  --large_theory_mode                     true
% 1.87/1.02  --prolific_symb_bound                   200
% 1.87/1.02  --lt_threshold                          2000
% 1.87/1.02  --clause_weak_htbl                      true
% 1.87/1.02  --gc_record_bc_elim                     false
% 1.87/1.02  
% 1.87/1.02  ------ Preprocessing Options
% 1.87/1.02  
% 1.87/1.02  --preprocessing_flag                    true
% 1.87/1.02  --time_out_prep_mult                    0.1
% 1.87/1.02  --splitting_mode                        input
% 1.87/1.02  --splitting_grd                         true
% 1.87/1.02  --splitting_cvd                         false
% 1.87/1.02  --splitting_cvd_svl                     false
% 1.87/1.02  --splitting_nvd                         32
% 1.87/1.02  --sub_typing                            true
% 1.87/1.02  --prep_gs_sim                           true
% 1.87/1.02  --prep_unflatten                        true
% 1.87/1.02  --prep_res_sim                          true
% 1.87/1.02  --prep_upred                            true
% 1.87/1.02  --prep_sem_filter                       exhaustive
% 1.87/1.02  --prep_sem_filter_out                   false
% 1.87/1.02  --pred_elim                             true
% 1.87/1.02  --res_sim_input                         true
% 1.87/1.02  --eq_ax_congr_red                       true
% 1.87/1.02  --pure_diseq_elim                       true
% 1.87/1.02  --brand_transform                       false
% 1.87/1.02  --non_eq_to_eq                          false
% 1.87/1.02  --prep_def_merge                        true
% 1.87/1.02  --prep_def_merge_prop_impl              false
% 1.87/1.02  --prep_def_merge_mbd                    true
% 1.87/1.02  --prep_def_merge_tr_red                 false
% 1.87/1.02  --prep_def_merge_tr_cl                  false
% 1.87/1.02  --smt_preprocessing                     true
% 1.87/1.02  --smt_ac_axioms                         fast
% 1.87/1.02  --preprocessed_out                      false
% 1.87/1.02  --preprocessed_stats                    false
% 1.87/1.02  
% 1.87/1.02  ------ Abstraction refinement Options
% 1.87/1.02  
% 1.87/1.02  --abstr_ref                             []
% 1.87/1.02  --abstr_ref_prep                        false
% 1.87/1.02  --abstr_ref_until_sat                   false
% 1.87/1.02  --abstr_ref_sig_restrict                funpre
% 1.87/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.87/1.02  --abstr_ref_under                       []
% 1.87/1.02  
% 1.87/1.02  ------ SAT Options
% 1.87/1.02  
% 1.87/1.02  --sat_mode                              false
% 1.87/1.02  --sat_fm_restart_options                ""
% 1.87/1.02  --sat_gr_def                            false
% 1.87/1.02  --sat_epr_types                         true
% 1.87/1.02  --sat_non_cyclic_types                  false
% 1.87/1.02  --sat_finite_models                     false
% 1.87/1.02  --sat_fm_lemmas                         false
% 1.87/1.02  --sat_fm_prep                           false
% 1.87/1.02  --sat_fm_uc_incr                        true
% 1.87/1.02  --sat_out_model                         small
% 1.87/1.02  --sat_out_clauses                       false
% 1.87/1.02  
% 1.87/1.02  ------ QBF Options
% 1.87/1.02  
% 1.87/1.02  --qbf_mode                              false
% 1.87/1.02  --qbf_elim_univ                         false
% 1.87/1.02  --qbf_dom_inst                          none
% 1.87/1.02  --qbf_dom_pre_inst                      false
% 1.87/1.02  --qbf_sk_in                             false
% 1.87/1.02  --qbf_pred_elim                         true
% 1.87/1.02  --qbf_split                             512
% 1.87/1.02  
% 1.87/1.02  ------ BMC1 Options
% 1.87/1.02  
% 1.87/1.02  --bmc1_incremental                      false
% 1.87/1.02  --bmc1_axioms                           reachable_all
% 1.87/1.02  --bmc1_min_bound                        0
% 1.87/1.02  --bmc1_max_bound                        -1
% 1.87/1.02  --bmc1_max_bound_default                -1
% 1.87/1.02  --bmc1_symbol_reachability              true
% 1.87/1.02  --bmc1_property_lemmas                  false
% 1.87/1.02  --bmc1_k_induction                      false
% 1.87/1.02  --bmc1_non_equiv_states                 false
% 1.87/1.02  --bmc1_deadlock                         false
% 1.87/1.02  --bmc1_ucm                              false
% 1.87/1.02  --bmc1_add_unsat_core                   none
% 1.87/1.02  --bmc1_unsat_core_children              false
% 1.87/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.87/1.02  --bmc1_out_stat                         full
% 1.87/1.02  --bmc1_ground_init                      false
% 1.87/1.02  --bmc1_pre_inst_next_state              false
% 1.87/1.02  --bmc1_pre_inst_state                   false
% 1.87/1.02  --bmc1_pre_inst_reach_state             false
% 1.87/1.02  --bmc1_out_unsat_core                   false
% 1.87/1.02  --bmc1_aig_witness_out                  false
% 1.87/1.02  --bmc1_verbose                          false
% 1.87/1.02  --bmc1_dump_clauses_tptp                false
% 1.87/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.87/1.02  --bmc1_dump_file                        -
% 1.87/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.87/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.87/1.02  --bmc1_ucm_extend_mode                  1
% 1.87/1.02  --bmc1_ucm_init_mode                    2
% 1.87/1.02  --bmc1_ucm_cone_mode                    none
% 1.87/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.87/1.02  --bmc1_ucm_relax_model                  4
% 1.87/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.87/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.87/1.02  --bmc1_ucm_layered_model                none
% 1.87/1.02  --bmc1_ucm_max_lemma_size               10
% 1.87/1.02  
% 1.87/1.02  ------ AIG Options
% 1.87/1.02  
% 1.87/1.02  --aig_mode                              false
% 1.87/1.02  
% 1.87/1.02  ------ Instantiation Options
% 1.87/1.02  
% 1.87/1.02  --instantiation_flag                    true
% 1.87/1.02  --inst_sos_flag                         false
% 1.87/1.02  --inst_sos_phase                        true
% 1.87/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.87/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.87/1.02  --inst_lit_sel_side                     none
% 1.87/1.02  --inst_solver_per_active                1400
% 1.87/1.02  --inst_solver_calls_frac                1.
% 1.87/1.02  --inst_passive_queue_type               priority_queues
% 1.87/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.87/1.02  --inst_passive_queues_freq              [25;2]
% 1.87/1.02  --inst_dismatching                      true
% 1.87/1.02  --inst_eager_unprocessed_to_passive     true
% 1.87/1.02  --inst_prop_sim_given                   true
% 1.87/1.02  --inst_prop_sim_new                     false
% 1.87/1.02  --inst_subs_new                         false
% 1.87/1.02  --inst_eq_res_simp                      false
% 1.87/1.02  --inst_subs_given                       false
% 1.87/1.02  --inst_orphan_elimination               true
% 1.87/1.02  --inst_learning_loop_flag               true
% 1.87/1.02  --inst_learning_start                   3000
% 1.87/1.02  --inst_learning_factor                  2
% 1.87/1.02  --inst_start_prop_sim_after_learn       3
% 1.87/1.02  --inst_sel_renew                        solver
% 1.87/1.02  --inst_lit_activity_flag                true
% 1.87/1.02  --inst_restr_to_given                   false
% 1.87/1.02  --inst_activity_threshold               500
% 1.87/1.02  --inst_out_proof                        true
% 1.87/1.02  
% 1.87/1.02  ------ Resolution Options
% 1.87/1.02  
% 1.87/1.02  --resolution_flag                       false
% 1.87/1.02  --res_lit_sel                           adaptive
% 1.87/1.02  --res_lit_sel_side                      none
% 1.87/1.02  --res_ordering                          kbo
% 1.87/1.02  --res_to_prop_solver                    active
% 1.87/1.02  --res_prop_simpl_new                    false
% 1.87/1.02  --res_prop_simpl_given                  true
% 1.87/1.02  --res_passive_queue_type                priority_queues
% 1.87/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.87/1.02  --res_passive_queues_freq               [15;5]
% 1.87/1.02  --res_forward_subs                      full
% 1.87/1.02  --res_backward_subs                     full
% 1.87/1.02  --res_forward_subs_resolution           true
% 1.87/1.02  --res_backward_subs_resolution          true
% 1.87/1.02  --res_orphan_elimination                true
% 1.87/1.02  --res_time_limit                        2.
% 1.87/1.02  --res_out_proof                         true
% 1.87/1.02  
% 1.87/1.02  ------ Superposition Options
% 1.87/1.02  
% 1.87/1.02  --superposition_flag                    true
% 1.87/1.02  --sup_passive_queue_type                priority_queues
% 1.87/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.87/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.87/1.02  --demod_completeness_check              fast
% 1.87/1.02  --demod_use_ground                      true
% 1.87/1.02  --sup_to_prop_solver                    passive
% 1.87/1.02  --sup_prop_simpl_new                    true
% 1.87/1.02  --sup_prop_simpl_given                  true
% 1.87/1.02  --sup_fun_splitting                     false
% 1.87/1.02  --sup_smt_interval                      50000
% 1.87/1.02  
% 1.87/1.02  ------ Superposition Simplification Setup
% 1.87/1.02  
% 1.87/1.02  --sup_indices_passive                   []
% 1.87/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.87/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/1.02  --sup_full_bw                           [BwDemod]
% 1.87/1.02  --sup_immed_triv                        [TrivRules]
% 1.87/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.87/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/1.02  --sup_immed_bw_main                     []
% 1.87/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.87/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/1.02  
% 1.87/1.02  ------ Combination Options
% 1.87/1.02  
% 1.87/1.02  --comb_res_mult                         3
% 1.87/1.02  --comb_sup_mult                         2
% 1.87/1.02  --comb_inst_mult                        10
% 1.87/1.02  
% 1.87/1.02  ------ Debug Options
% 1.87/1.02  
% 1.87/1.02  --dbg_backtrace                         false
% 1.87/1.02  --dbg_dump_prop_clauses                 false
% 1.87/1.02  --dbg_dump_prop_clauses_file            -
% 1.87/1.02  --dbg_out_stat                          false
% 1.87/1.02  
% 1.87/1.02  
% 1.87/1.02  
% 1.87/1.02  
% 1.87/1.02  ------ Proving...
% 1.87/1.02  
% 1.87/1.02  
% 1.87/1.02  % SZS status Theorem for theBenchmark.p
% 1.87/1.02  
% 1.87/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.87/1.02  
% 1.87/1.02  fof(f22,axiom,(
% 1.87/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.02  
% 1.87/1.02  fof(f44,plain,(
% 1.87/1.02    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.87/1.02    inference(ennf_transformation,[],[f22])).
% 1.87/1.02  
% 1.87/1.02  fof(f45,plain,(
% 1.87/1.02    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.87/1.02    inference(flattening,[],[f44])).
% 1.87/1.02  
% 1.87/1.02  fof(f88,plain,(
% 1.87/1.02    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.87/1.02    inference(cnf_transformation,[],[f45])).
% 1.87/1.02  
% 1.87/1.02  fof(f24,conjecture,(
% 1.87/1.02    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 1.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.02  
% 1.87/1.02  fof(f25,negated_conjecture,(
% 1.87/1.02    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 1.87/1.02    inference(negated_conjecture,[],[f24])).
% 1.87/1.02  
% 1.87/1.02  fof(f47,plain,(
% 1.87/1.02    ? [X0] : (? [X1] : (? [X2] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 1.87/1.02    inference(ennf_transformation,[],[f25])).
% 1.87/1.02  
% 1.87/1.02  fof(f48,plain,(
% 1.87/1.02    ? [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 1.87/1.02    inference(flattening,[],[f47])).
% 1.87/1.02  
% 1.87/1.02  fof(f57,plain,(
% 1.87/1.02    ( ! [X0,X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 1.87/1.02    introduced(choice_axiom,[])).
% 1.87/1.02  
% 1.87/1.02  fof(f56,plain,(
% 1.87/1.02    ( ! [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2,k2_struct_0(sK2)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(sK2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_struct_0(sK2))) )),
% 1.87/1.02    introduced(choice_axiom,[])).
% 1.87/1.02  
% 1.87/1.02  fof(f55,plain,(
% 1.87/1.02    ? [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(sK1) & (k1_xboole_0 = k2_struct_0(sK1) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK1))),
% 1.87/1.02    introduced(choice_axiom,[])).
% 1.87/1.02  
% 1.87/1.02  fof(f58,plain,(
% 1.87/1.02    ((k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) & (k1_xboole_0 = k2_struct_0(sK1) | k1_xboole_0 != k2_struct_0(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_struct_0(sK2)) & l1_struct_0(sK1)),
% 1.87/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f48,f57,f56,f55])).
% 1.87/1.02  
% 1.87/1.02  fof(f94,plain,(
% 1.87/1.02    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 1.87/1.02    inference(cnf_transformation,[],[f58])).
% 1.87/1.02  
% 1.87/1.02  fof(f93,plain,(
% 1.87/1.02    v1_funct_1(sK3)),
% 1.87/1.02    inference(cnf_transformation,[],[f58])).
% 1.87/1.02  
% 1.87/1.02  fof(f95,plain,(
% 1.87/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 1.87/1.02    inference(cnf_transformation,[],[f58])).
% 1.87/1.02  
% 1.87/1.02  fof(f18,axiom,(
% 1.87/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.02  
% 1.87/1.02  fof(f39,plain,(
% 1.87/1.02    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/1.02    inference(ennf_transformation,[],[f18])).
% 1.87/1.02  
% 1.87/1.02  fof(f82,plain,(
% 1.87/1.02    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.87/1.02    inference(cnf_transformation,[],[f39])).
% 1.87/1.02  
% 1.87/1.02  fof(f21,axiom,(
% 1.87/1.02    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.02  
% 1.87/1.02  fof(f42,plain,(
% 1.87/1.02    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.87/1.02    inference(ennf_transformation,[],[f21])).
% 1.87/1.02  
% 1.87/1.02  fof(f43,plain,(
% 1.87/1.02    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.87/1.02    inference(flattening,[],[f42])).
% 1.87/1.02  
% 1.87/1.02  fof(f54,plain,(
% 1.87/1.02    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.87/1.02    inference(nnf_transformation,[],[f43])).
% 1.87/1.02  
% 1.87/1.02  fof(f86,plain,(
% 1.87/1.02    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.87/1.02    inference(cnf_transformation,[],[f54])).
% 1.87/1.02  
% 1.87/1.02  fof(f17,axiom,(
% 1.87/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.02  
% 1.87/1.02  fof(f38,plain,(
% 1.87/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/1.02    inference(ennf_transformation,[],[f17])).
% 1.87/1.02  
% 1.87/1.02  fof(f81,plain,(
% 1.87/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.87/1.02    inference(cnf_transformation,[],[f38])).
% 1.87/1.02  
% 1.87/1.02  fof(f23,axiom,(
% 1.87/1.02    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.02  
% 1.87/1.02  fof(f46,plain,(
% 1.87/1.02    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.87/1.02    inference(ennf_transformation,[],[f23])).
% 1.87/1.02  
% 1.87/1.02  fof(f90,plain,(
% 1.87/1.02    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.87/1.02    inference(cnf_transformation,[],[f46])).
% 1.87/1.02  
% 1.87/1.02  fof(f92,plain,(
% 1.87/1.02    l1_struct_0(sK2)),
% 1.87/1.02    inference(cnf_transformation,[],[f58])).
% 1.87/1.02  
% 1.87/1.02  fof(f91,plain,(
% 1.87/1.02    l1_struct_0(sK1)),
% 1.87/1.02    inference(cnf_transformation,[],[f58])).
% 1.87/1.02  
% 1.87/1.02  fof(f96,plain,(
% 1.87/1.02    k1_xboole_0 = k2_struct_0(sK1) | k1_xboole_0 != k2_struct_0(sK2)),
% 1.87/1.02    inference(cnf_transformation,[],[f58])).
% 1.87/1.02  
% 1.87/1.02  fof(f5,axiom,(
% 1.87/1.02    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.02  
% 1.87/1.02  fof(f29,plain,(
% 1.87/1.02    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.87/1.02    inference(ennf_transformation,[],[f5])).
% 1.87/1.02  
% 1.87/1.02  fof(f51,plain,(
% 1.87/1.02    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.87/1.02    inference(nnf_transformation,[],[f29])).
% 1.87/1.02  
% 1.87/1.02  fof(f65,plain,(
% 1.87/1.02    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.87/1.02    inference(cnf_transformation,[],[f51])).
% 1.87/1.02  
% 1.87/1.02  fof(f83,plain,(
% 1.87/1.02    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.87/1.02    inference(cnf_transformation,[],[f39])).
% 1.87/1.02  
% 1.87/1.02  fof(f13,axiom,(
% 1.87/1.02    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.02  
% 1.87/1.02  fof(f34,plain,(
% 1.87/1.02    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.87/1.02    inference(ennf_transformation,[],[f13])).
% 1.87/1.02  
% 1.87/1.02  fof(f35,plain,(
% 1.87/1.02    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.87/1.02    inference(flattening,[],[f34])).
% 1.87/1.02  
% 1.87/1.02  fof(f77,plain,(
% 1.87/1.02    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.87/1.02    inference(cnf_transformation,[],[f35])).
% 1.87/1.02  
% 1.87/1.02  fof(f6,axiom,(
% 1.87/1.02    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.02  
% 1.87/1.02  fof(f67,plain,(
% 1.87/1.02    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.87/1.02    inference(cnf_transformation,[],[f6])).
% 1.87/1.02  
% 1.87/1.02  fof(f9,axiom,(
% 1.87/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.02  
% 1.87/1.02  fof(f33,plain,(
% 1.87/1.02    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.87/1.02    inference(ennf_transformation,[],[f9])).
% 1.87/1.02  
% 1.87/1.02  fof(f71,plain,(
% 1.87/1.02    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.87/1.02    inference(cnf_transformation,[],[f33])).
% 1.87/1.02  
% 1.87/1.02  fof(f12,axiom,(
% 1.87/1.02    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.02  
% 1.87/1.02  fof(f75,plain,(
% 1.87/1.02    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.87/1.02    inference(cnf_transformation,[],[f12])).
% 1.87/1.02  
% 1.87/1.02  fof(f19,axiom,(
% 1.87/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 1.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.02  
% 1.87/1.02  fof(f40,plain,(
% 1.87/1.02    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/1.02    inference(ennf_transformation,[],[f19])).
% 1.87/1.02  
% 1.87/1.02  fof(f84,plain,(
% 1.87/1.02    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.87/1.02    inference(cnf_transformation,[],[f40])).
% 1.87/1.02  
% 1.87/1.02  fof(f97,plain,(
% 1.87/1.02    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1)),
% 1.87/1.02    inference(cnf_transformation,[],[f58])).
% 1.87/1.02  
% 1.87/1.02  fof(f89,plain,(
% 1.87/1.02    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.87/1.02    inference(cnf_transformation,[],[f45])).
% 1.87/1.02  
% 1.87/1.02  fof(f101,plain,(
% 1.87/1.02    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 1.87/1.02    inference(equality_resolution,[],[f89])).
% 1.87/1.02  
% 1.87/1.02  fof(f3,axiom,(
% 1.87/1.02    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.87/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.02  
% 1.87/1.02  fof(f49,plain,(
% 1.87/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.87/1.02    inference(nnf_transformation,[],[f3])).
% 1.87/1.02  
% 1.87/1.02  fof(f50,plain,(
% 1.87/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.87/1.02    inference(flattening,[],[f49])).
% 1.87/1.02  
% 1.87/1.02  fof(f62,plain,(
% 1.87/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.87/1.02    inference(cnf_transformation,[],[f50])).
% 1.87/1.02  
% 1.87/1.02  fof(f99,plain,(
% 1.87/1.02    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.87/1.02    inference(equality_resolution,[],[f62])).
% 1.87/1.02  
% 1.87/1.02  fof(f63,plain,(
% 1.87/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.87/1.02    inference(cnf_transformation,[],[f50])).
% 1.87/1.02  
% 1.87/1.02  fof(f98,plain,(
% 1.87/1.02    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.87/1.02    inference(equality_resolution,[],[f63])).
% 1.87/1.02  
% 1.87/1.02  cnf(c_30,plain,
% 1.87/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 1.87/1.02      | v1_partfun1(X0,X1)
% 1.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.87/1.02      | ~ v1_funct_1(X0)
% 1.87/1.02      | k1_xboole_0 = X2 ),
% 1.87/1.02      inference(cnf_transformation,[],[f88]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_35,negated_conjecture,
% 1.87/1.02      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 1.87/1.02      inference(cnf_transformation,[],[f94]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_475,plain,
% 1.87/1.02      ( v1_partfun1(X0,X1)
% 1.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.87/1.02      | ~ v1_funct_1(X0)
% 1.87/1.02      | u1_struct_0(sK2) != X2
% 1.87/1.02      | u1_struct_0(sK1) != X1
% 1.87/1.02      | sK3 != X0
% 1.87/1.02      | k1_xboole_0 = X2 ),
% 1.87/1.02      inference(resolution_lifted,[status(thm)],[c_30,c_35]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_476,plain,
% 1.87/1.02      ( v1_partfun1(sK3,u1_struct_0(sK1))
% 1.87/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 1.87/1.02      | ~ v1_funct_1(sK3)
% 1.87/1.02      | k1_xboole_0 = u1_struct_0(sK2) ),
% 1.87/1.02      inference(unflattening,[status(thm)],[c_475]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_36,negated_conjecture,
% 1.87/1.02      ( v1_funct_1(sK3) ),
% 1.87/1.02      inference(cnf_transformation,[],[f93]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_34,negated_conjecture,
% 1.87/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 1.87/1.02      inference(cnf_transformation,[],[f95]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_478,plain,
% 1.87/1.02      ( v1_partfun1(sK3,u1_struct_0(sK1))
% 1.87/1.02      | k1_xboole_0 = u1_struct_0(sK2) ),
% 1.87/1.02      inference(global_propositional_subsumption,
% 1.87/1.02                [status(thm)],
% 1.87/1.02                [c_476,c_36,c_34]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_24,plain,
% 1.87/1.02      ( v4_relat_1(X0,X1)
% 1.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.87/1.02      inference(cnf_transformation,[],[f82]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_28,plain,
% 1.87/1.02      ( ~ v1_partfun1(X0,X1)
% 1.87/1.02      | ~ v4_relat_1(X0,X1)
% 1.87/1.02      | ~ v1_relat_1(X0)
% 1.87/1.02      | k1_relat_1(X0) = X1 ),
% 1.87/1.02      inference(cnf_transformation,[],[f86]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_418,plain,
% 1.87/1.02      ( ~ v1_partfun1(X0,X1)
% 1.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.87/1.02      | ~ v1_relat_1(X0)
% 1.87/1.02      | k1_relat_1(X0) = X1 ),
% 1.87/1.02      inference(resolution,[status(thm)],[c_24,c_28]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_22,plain,
% 1.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.87/1.02      | v1_relat_1(X0) ),
% 1.87/1.02      inference(cnf_transformation,[],[f81]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_420,plain,
% 1.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.87/1.02      | ~ v1_partfun1(X0,X1)
% 1.87/1.02      | k1_relat_1(X0) = X1 ),
% 1.87/1.02      inference(global_propositional_subsumption,
% 1.87/1.02                [status(thm)],
% 1.87/1.02                [c_418,c_28,c_24,c_22]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_421,plain,
% 1.87/1.02      ( ~ v1_partfun1(X0,X1)
% 1.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.87/1.02      | k1_relat_1(X0) = X1 ),
% 1.87/1.02      inference(renaming,[status(thm)],[c_420]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_570,plain,
% 1.87/1.02      ( ~ v1_partfun1(X0,X1)
% 1.87/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.87/1.02      | k1_relat_1(X0) = X1
% 1.87/1.02      | sK3 != X0 ),
% 1.87/1.02      inference(resolution_lifted,[status(thm)],[c_421,c_34]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_571,plain,
% 1.87/1.02      ( ~ v1_partfun1(sK3,X0)
% 1.87/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.87/1.02      | k1_relat_1(sK3) = X0 ),
% 1.87/1.02      inference(unflattening,[status(thm)],[c_570]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_741,plain,
% 1.87/1.02      ( u1_struct_0(sK2) = k1_xboole_0
% 1.87/1.02      | u1_struct_0(sK1) != X0
% 1.87/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.87/1.02      | k1_relat_1(sK3) = X0
% 1.87/1.02      | sK3 != sK3 ),
% 1.87/1.02      inference(resolution_lifted,[status(thm)],[c_478,c_571]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_742,plain,
% 1.87/1.02      ( u1_struct_0(sK2) = k1_xboole_0
% 1.87/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0))
% 1.87/1.02      | k1_relat_1(sK3) = u1_struct_0(sK1) ),
% 1.87/1.02      inference(unflattening,[status(thm)],[c_741]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_921,plain,
% 1.87/1.02      ( sP0_iProver_split
% 1.87/1.02      | u1_struct_0(sK2) = k1_xboole_0
% 1.87/1.02      | k1_relat_1(sK3) = u1_struct_0(sK1) ),
% 1.87/1.02      inference(splitting,
% 1.87/1.02                [splitting(split),new_symbols(definition,[])],
% 1.87/1.02                [c_742]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1256,plain,
% 1.87/1.02      ( u1_struct_0(sK2) = k1_xboole_0
% 1.87/1.02      | k1_relat_1(sK3) = u1_struct_0(sK1)
% 1.87/1.02      | sP0_iProver_split = iProver_top ),
% 1.87/1.02      inference(predicate_to_equality,[status(thm)],[c_921]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_31,plain,
% 1.87/1.02      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.87/1.02      inference(cnf_transformation,[],[f90]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_37,negated_conjecture,
% 1.87/1.02      ( l1_struct_0(sK2) ),
% 1.87/1.02      inference(cnf_transformation,[],[f92]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_384,plain,
% 1.87/1.02      ( u1_struct_0(X0) = k2_struct_0(X0) | sK2 != X0 ),
% 1.87/1.02      inference(resolution_lifted,[status(thm)],[c_31,c_37]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_385,plain,
% 1.87/1.02      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 1.87/1.02      inference(unflattening,[status(thm)],[c_384]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_38,negated_conjecture,
% 1.87/1.02      ( l1_struct_0(sK1) ),
% 1.87/1.02      inference(cnf_transformation,[],[f91]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_389,plain,
% 1.87/1.02      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 1.87/1.02      inference(resolution_lifted,[status(thm)],[c_31,c_38]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_390,plain,
% 1.87/1.02      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.87/1.02      inference(unflattening,[status(thm)],[c_389]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1320,plain,
% 1.87/1.02      ( k2_struct_0(sK2) = k1_xboole_0
% 1.87/1.02      | k2_struct_0(sK1) = k1_relat_1(sK3)
% 1.87/1.02      | sP0_iProver_split = iProver_top ),
% 1.87/1.02      inference(demodulation,[status(thm)],[c_1256,c_385,c_390]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_920,plain,
% 1.87/1.02      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0))
% 1.87/1.02      | ~ sP0_iProver_split ),
% 1.87/1.02      inference(splitting,
% 1.87/1.02                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.87/1.02                [c_742]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1257,plain,
% 1.87/1.02      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0))
% 1.87/1.02      | sP0_iProver_split != iProver_top ),
% 1.87/1.02      inference(predicate_to_equality,[status(thm)],[c_920]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1358,plain,
% 1.87/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),X0))
% 1.87/1.02      | sP0_iProver_split != iProver_top ),
% 1.87/1.02      inference(light_normalisation,[status(thm)],[c_1257,c_385,c_390]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1504,plain,
% 1.87/1.02      ( sP0_iProver_split != iProver_top ),
% 1.87/1.02      inference(equality_resolution,[status(thm)],[c_1358]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1803,plain,
% 1.87/1.02      ( k2_struct_0(sK1) = k1_relat_1(sK3)
% 1.87/1.02      | k2_struct_0(sK2) = k1_xboole_0 ),
% 1.87/1.02      inference(global_propositional_subsumption,
% 1.87/1.02                [status(thm)],
% 1.87/1.02                [c_1320,c_1504]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1804,plain,
% 1.87/1.02      ( k2_struct_0(sK2) = k1_xboole_0
% 1.87/1.02      | k2_struct_0(sK1) = k1_relat_1(sK3) ),
% 1.87/1.02      inference(renaming,[status(thm)],[c_1803]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_33,negated_conjecture,
% 1.87/1.02      ( k1_xboole_0 != k2_struct_0(sK2)
% 1.87/1.02      | k1_xboole_0 = k2_struct_0(sK1) ),
% 1.87/1.02      inference(cnf_transformation,[],[f96]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1815,plain,
% 1.87/1.02      ( k2_struct_0(sK1) = k1_relat_1(sK3)
% 1.87/1.02      | k2_struct_0(sK1) = k1_xboole_0 ),
% 1.87/1.02      inference(superposition,[status(thm)],[c_1804,c_33]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_7,plain,
% 1.87/1.02      ( r1_tarski(k2_relat_1(X0),X1)
% 1.87/1.02      | ~ v5_relat_1(X0,X1)
% 1.87/1.02      | ~ v1_relat_1(X0) ),
% 1.87/1.02      inference(cnf_transformation,[],[f65]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_23,plain,
% 1.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.87/1.02      | v5_relat_1(X0,X2) ),
% 1.87/1.02      inference(cnf_transformation,[],[f83]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_397,plain,
% 1.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.87/1.02      | r1_tarski(k2_relat_1(X3),X4)
% 1.87/1.02      | ~ v1_relat_1(X3)
% 1.87/1.02      | X0 != X3
% 1.87/1.02      | X2 != X4 ),
% 1.87/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_23]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_398,plain,
% 1.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.87/1.02      | r1_tarski(k2_relat_1(X0),X2)
% 1.87/1.02      | ~ v1_relat_1(X0) ),
% 1.87/1.02      inference(unflattening,[status(thm)],[c_397]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_402,plain,
% 1.87/1.02      ( r1_tarski(k2_relat_1(X0),X2)
% 1.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.87/1.02      inference(global_propositional_subsumption,
% 1.87/1.02                [status(thm)],
% 1.87/1.02                [c_398,c_22]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_403,plain,
% 1.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.87/1.02      | r1_tarski(k2_relat_1(X0),X2) ),
% 1.87/1.02      inference(renaming,[status(thm)],[c_402]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_585,plain,
% 1.87/1.02      ( r1_tarski(k2_relat_1(X0),X1)
% 1.87/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
% 1.87/1.02      | sK3 != X0 ),
% 1.87/1.02      inference(resolution_lifted,[status(thm)],[c_403,c_34]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_586,plain,
% 1.87/1.02      ( r1_tarski(k2_relat_1(sK3),X0)
% 1.87/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
% 1.87/1.02      inference(unflattening,[status(thm)],[c_585]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1261,plain,
% 1.87/1.02      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.87/1.02      | r1_tarski(k2_relat_1(sK3),X1) = iProver_top ),
% 1.87/1.02      inference(predicate_to_equality,[status(thm)],[c_586]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1363,plain,
% 1.87/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.87/1.02      | r1_tarski(k2_relat_1(sK3),X1) = iProver_top ),
% 1.87/1.02      inference(light_normalisation,[status(thm)],[c_1261,c_385,c_390]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1720,plain,
% 1.87/1.02      ( r1_tarski(k2_relat_1(sK3),k2_struct_0(sK2)) = iProver_top ),
% 1.87/1.02      inference(equality_resolution,[status(thm)],[c_1363]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_18,plain,
% 1.87/1.02      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 1.87/1.02      | ~ v1_relat_1(X0)
% 1.87/1.02      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 1.87/1.02      inference(cnf_transformation,[],[f77]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1265,plain,
% 1.87/1.02      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 1.87/1.02      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 1.87/1.02      | v1_relat_1(X0) != iProver_top ),
% 1.87/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_4064,plain,
% 1.87/1.02      ( k5_relat_1(sK3,k6_relat_1(k2_struct_0(sK2))) = sK3
% 1.87/1.02      | v1_relat_1(sK3) != iProver_top ),
% 1.87/1.02      inference(superposition,[status(thm)],[c_1720,c_1265]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_606,plain,
% 1.87/1.02      ( v1_relat_1(X0)
% 1.87/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.87/1.02      | sK3 != X0 ),
% 1.87/1.02      inference(resolution_lifted,[status(thm)],[c_22,c_34]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_607,plain,
% 1.87/1.02      ( v1_relat_1(sK3)
% 1.87/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.87/1.02      inference(unflattening,[status(thm)],[c_606]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1260,plain,
% 1.87/1.02      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.87/1.02      | v1_relat_1(sK3) = iProver_top ),
% 1.87/1.02      inference(predicate_to_equality,[status(thm)],[c_607]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1348,plain,
% 1.87/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.87/1.02      | v1_relat_1(sK3) = iProver_top ),
% 1.87/1.02      inference(light_normalisation,[status(thm)],[c_1260,c_385,c_390]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1476,plain,
% 1.87/1.02      ( v1_relat_1(sK3) = iProver_top ),
% 1.87/1.02      inference(equality_resolution,[status(thm)],[c_1348]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_4462,plain,
% 1.87/1.02      ( k5_relat_1(sK3,k6_relat_1(k2_struct_0(sK2))) = sK3 ),
% 1.87/1.02      inference(global_propositional_subsumption,
% 1.87/1.02                [status(thm)],
% 1.87/1.02                [c_4064,c_1476]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_8,plain,
% 1.87/1.02      ( v1_relat_1(k6_relat_1(X0)) ),
% 1.87/1.02      inference(cnf_transformation,[],[f67]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1269,plain,
% 1.87/1.02      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 1.87/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_12,plain,
% 1.87/1.02      ( ~ v1_relat_1(X0)
% 1.87/1.02      | ~ v1_relat_1(X1)
% 1.87/1.02      | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
% 1.87/1.02      inference(cnf_transformation,[],[f71]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1267,plain,
% 1.87/1.02      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 1.87/1.02      | v1_relat_1(X1) != iProver_top
% 1.87/1.02      | v1_relat_1(X0) != iProver_top ),
% 1.87/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_5128,plain,
% 1.87/1.02      ( k10_relat_1(sK3,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK3,X0))
% 1.87/1.02      | v1_relat_1(X0) != iProver_top ),
% 1.87/1.02      inference(superposition,[status(thm)],[c_1476,c_1267]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_5645,plain,
% 1.87/1.02      ( k10_relat_1(sK3,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(X0))) ),
% 1.87/1.02      inference(superposition,[status(thm)],[c_1269,c_5128]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_17,plain,
% 1.87/1.02      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 1.87/1.02      inference(cnf_transformation,[],[f75]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_5654,plain,
% 1.87/1.02      ( k1_relat_1(k5_relat_1(sK3,k6_relat_1(X0))) = k10_relat_1(sK3,X0) ),
% 1.87/1.02      inference(light_normalisation,[status(thm)],[c_5645,c_17]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_6230,plain,
% 1.87/1.02      ( k10_relat_1(sK3,k2_struct_0(sK2)) = k1_relat_1(sK3) ),
% 1.87/1.02      inference(superposition,[status(thm)],[c_4462,c_5654]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_25,plain,
% 1.87/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.87/1.02      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 1.87/1.02      inference(cnf_transformation,[],[f84]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_597,plain,
% 1.87/1.02      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 1.87/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.87/1.02      | sK3 != X2 ),
% 1.87/1.02      inference(resolution_lifted,[status(thm)],[c_25,c_34]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_598,plain,
% 1.87/1.02      ( k8_relset_1(X0,X1,sK3,X2) = k10_relat_1(sK3,X2)
% 1.87/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.87/1.02      inference(unflattening,[status(thm)],[c_597]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1380,plain,
% 1.87/1.02      ( k8_relset_1(X0,X1,sK3,X2) = k10_relat_1(sK3,X2)
% 1.87/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.87/1.02      inference(light_normalisation,[status(thm)],[c_598,c_385,c_390]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1793,plain,
% 1.87/1.02      ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,X0) = k10_relat_1(sK3,X0) ),
% 1.87/1.02      inference(equality_resolution,[status(thm)],[c_1380]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_32,negated_conjecture,
% 1.87/1.02      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
% 1.87/1.02      inference(cnf_transformation,[],[f97]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1317,plain,
% 1.87/1.02      ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
% 1.87/1.02      inference(light_normalisation,[status(thm)],[c_32,c_385,c_390]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_2488,plain,
% 1.87/1.02      ( k10_relat_1(sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
% 1.87/1.02      inference(demodulation,[status(thm)],[c_1793,c_1317]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_6235,plain,
% 1.87/1.02      ( k2_struct_0(sK1) != k1_relat_1(sK3) ),
% 1.87/1.02      inference(demodulation,[status(thm)],[c_6230,c_2488]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_6318,plain,
% 1.87/1.02      ( k2_struct_0(sK1) = k1_xboole_0 ),
% 1.87/1.02      inference(superposition,[status(thm)],[c_1815,c_6235]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_6320,plain,
% 1.87/1.02      ( k1_relat_1(sK3) != k1_xboole_0 ),
% 1.87/1.02      inference(demodulation,[status(thm)],[c_6318,c_6235]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_29,plain,
% 1.87/1.02      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.87/1.02      | v1_partfun1(X0,k1_xboole_0)
% 1.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.87/1.02      | ~ v1_funct_1(X0) ),
% 1.87/1.02      inference(cnf_transformation,[],[f101]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_458,plain,
% 1.87/1.02      ( v1_partfun1(X0,k1_xboole_0)
% 1.87/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.87/1.02      | ~ v1_funct_1(X0)
% 1.87/1.02      | u1_struct_0(sK2) != X1
% 1.87/1.02      | u1_struct_0(sK1) != k1_xboole_0
% 1.87/1.02      | sK3 != X0 ),
% 1.87/1.02      inference(resolution_lifted,[status(thm)],[c_29,c_35]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_459,plain,
% 1.87/1.02      ( v1_partfun1(sK3,k1_xboole_0)
% 1.87/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))))
% 1.87/1.02      | ~ v1_funct_1(sK3)
% 1.87/1.02      | u1_struct_0(sK1) != k1_xboole_0 ),
% 1.87/1.02      inference(unflattening,[status(thm)],[c_458]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_461,plain,
% 1.87/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))))
% 1.87/1.02      | v1_partfun1(sK3,k1_xboole_0)
% 1.87/1.02      | u1_struct_0(sK1) != k1_xboole_0 ),
% 1.87/1.02      inference(global_propositional_subsumption,
% 1.87/1.02                [status(thm)],
% 1.87/1.02                [c_459,c_36]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_462,plain,
% 1.87/1.02      ( v1_partfun1(sK3,k1_xboole_0)
% 1.87/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))))
% 1.87/1.02      | u1_struct_0(sK1) != k1_xboole_0 ),
% 1.87/1.02      inference(renaming,[status(thm)],[c_461]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_630,plain,
% 1.87/1.02      ( v1_partfun1(sK3,k1_xboole_0)
% 1.87/1.02      | u1_struct_0(sK1) != k1_xboole_0
% 1.87/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2)))
% 1.87/1.02      | sK3 != sK3 ),
% 1.87/1.02      inference(resolution_lifted,[status(thm)],[c_34,c_462]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_726,plain,
% 1.87/1.02      ( u1_struct_0(sK1) != k1_xboole_0
% 1.87/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.87/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2)))
% 1.87/1.02      | k1_relat_1(sK3) = X0
% 1.87/1.02      | sK3 != sK3
% 1.87/1.02      | k1_xboole_0 != X0 ),
% 1.87/1.02      inference(resolution_lifted,[status(thm)],[c_630,c_571]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_727,plain,
% 1.87/1.02      ( u1_struct_0(sK1) != k1_xboole_0
% 1.87/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
% 1.87/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2)))
% 1.87/1.02      | k1_relat_1(sK3) = k1_xboole_0 ),
% 1.87/1.02      inference(unflattening,[status(thm)],[c_726]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_923,plain,
% 1.87/1.02      ( sP1_iProver_split
% 1.87/1.02      | u1_struct_0(sK1) != k1_xboole_0
% 1.87/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2)))
% 1.87/1.02      | k1_relat_1(sK3) = k1_xboole_0 ),
% 1.87/1.02      inference(splitting,
% 1.87/1.02                [splitting(split),new_symbols(definition,[])],
% 1.87/1.02                [c_727]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1258,plain,
% 1.87/1.02      ( u1_struct_0(sK1) != k1_xboole_0
% 1.87/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2)))
% 1.87/1.02      | k1_relat_1(sK3) = k1_xboole_0
% 1.87/1.02      | sP1_iProver_split = iProver_top ),
% 1.87/1.02      inference(predicate_to_equality,[status(thm)],[c_923]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1385,plain,
% 1.87/1.02      ( k2_struct_0(sK1) != k1_xboole_0
% 1.87/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK2)))
% 1.87/1.02      | k1_relat_1(sK3) = k1_xboole_0
% 1.87/1.02      | sP1_iProver_split = iProver_top ),
% 1.87/1.02      inference(light_normalisation,[status(thm)],[c_1258,c_385,c_390]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_3,plain,
% 1.87/1.02      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.87/1.02      inference(cnf_transformation,[],[f99]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1386,plain,
% 1.87/1.02      ( k2_struct_0(sK1) != k1_xboole_0
% 1.87/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k1_xboole_0)
% 1.87/1.02      | k1_relat_1(sK3) = k1_xboole_0
% 1.87/1.02      | sP1_iProver_split = iProver_top ),
% 1.87/1.02      inference(demodulation,[status(thm)],[c_1385,c_3]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_922,plain,
% 1.87/1.02      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
% 1.87/1.02      | ~ sP1_iProver_split ),
% 1.87/1.02      inference(splitting,
% 1.87/1.02                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.87/1.02                [c_727]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1259,plain,
% 1.87/1.02      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
% 1.87/1.02      | sP1_iProver_split != iProver_top ),
% 1.87/1.02      inference(predicate_to_equality,[status(thm)],[c_922]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1343,plain,
% 1.87/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k1_xboole_0)
% 1.87/1.02      | sP1_iProver_split != iProver_top ),
% 1.87/1.02      inference(light_normalisation,
% 1.87/1.02                [status(thm)],
% 1.87/1.02                [c_1259,c_3,c_385,c_390]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_1391,plain,
% 1.87/1.02      ( k2_struct_0(sK1) != k1_xboole_0
% 1.87/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k1_xboole_0)
% 1.87/1.02      | k1_relat_1(sK3) = k1_xboole_0 ),
% 1.87/1.02      inference(forward_subsumption_resolution,
% 1.87/1.02                [status(thm)],
% 1.87/1.02                [c_1386,c_1343]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_3263,plain,
% 1.87/1.02      ( k2_struct_0(sK1) = k1_relat_1(sK3)
% 1.87/1.02      | k2_struct_0(sK1) != k1_xboole_0
% 1.87/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0)
% 1.87/1.02      | k1_relat_1(sK3) = k1_xboole_0 ),
% 1.87/1.02      inference(superposition,[status(thm)],[c_1804,c_1391]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_2,plain,
% 1.87/1.02      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 1.87/1.02      inference(cnf_transformation,[],[f98]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_3268,plain,
% 1.87/1.02      ( k2_struct_0(sK1) = k1_relat_1(sK3)
% 1.87/1.02      | k2_struct_0(sK1) != k1_xboole_0
% 1.87/1.02      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
% 1.87/1.02      | k1_relat_1(sK3) = k1_xboole_0 ),
% 1.87/1.02      inference(demodulation,[status(thm)],[c_3263,c_2]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_3269,plain,
% 1.87/1.02      ( k2_struct_0(sK1) = k1_relat_1(sK3)
% 1.87/1.02      | k2_struct_0(sK1) != k1_xboole_0
% 1.87/1.02      | k1_relat_1(sK3) = k1_xboole_0 ),
% 1.87/1.02      inference(equality_resolution_simp,[status(thm)],[c_3268]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(c_4636,plain,
% 1.87/1.02      ( k2_struct_0(sK1) = k1_relat_1(sK3)
% 1.87/1.02      | k1_relat_1(sK3) = k1_xboole_0 ),
% 1.87/1.02      inference(global_propositional_subsumption,
% 1.87/1.02                [status(thm)],
% 1.87/1.02                [c_3269,c_1815]) ).
% 1.87/1.02  
% 1.87/1.02  cnf(contradiction,plain,
% 1.87/1.02      ( $false ),
% 1.87/1.02      inference(minisat,[status(thm)],[c_6320,c_6235,c_4636]) ).
% 1.87/1.02  
% 1.87/1.02  
% 1.87/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.87/1.02  
% 1.87/1.02  ------                               Statistics
% 1.87/1.02  
% 1.87/1.02  ------ General
% 1.87/1.02  
% 1.87/1.02  abstr_ref_over_cycles:                  0
% 1.87/1.02  abstr_ref_under_cycles:                 0
% 1.87/1.02  gc_basic_clause_elim:                   0
% 1.87/1.02  forced_gc_time:                         0
% 1.87/1.02  parsing_time:                           0.013
% 1.87/1.02  unif_index_cands_time:                  0.
% 1.87/1.02  unif_index_add_time:                    0.
% 1.87/1.02  orderings_time:                         0.
% 1.87/1.02  out_proof_time:                         0.011
% 1.87/1.02  total_time:                             0.222
% 1.87/1.02  num_of_symbols:                         61
% 1.87/1.02  num_of_terms:                           5104
% 1.87/1.02  
% 1.87/1.02  ------ Preprocessing
% 1.87/1.02  
% 1.87/1.02  num_of_splits:                          2
% 1.87/1.02  num_of_split_atoms:                     2
% 1.87/1.02  num_of_reused_defs:                     0
% 1.87/1.02  num_eq_ax_congr_red:                    20
% 1.87/1.02  num_of_sem_filtered_clauses:            1
% 1.87/1.02  num_of_subtypes:                        0
% 1.87/1.02  monotx_restored_types:                  0
% 1.87/1.02  sat_num_of_epr_types:                   0
% 1.87/1.02  sat_num_of_non_cyclic_types:            0
% 1.87/1.02  sat_guarded_non_collapsed_types:        0
% 1.87/1.02  num_pure_diseq_elim:                    0
% 1.87/1.02  simp_replaced_by:                       0
% 1.87/1.02  res_preprocessed:                       163
% 1.87/1.02  prep_upred:                             0
% 1.87/1.02  prep_unflattend:                        37
% 1.87/1.02  smt_new_axioms:                         0
% 1.87/1.02  pred_elim_cands:                        3
% 1.87/1.02  pred_elim:                              8
% 1.87/1.02  pred_elim_cl:                           10
% 1.87/1.02  pred_elim_cycles:                       12
% 1.87/1.02  merged_defs:                            0
% 1.87/1.02  merged_defs_ncl:                        0
% 1.87/1.02  bin_hyper_res:                          0
% 1.87/1.02  prep_cycles:                            4
% 1.87/1.02  pred_elim_time:                         0.016
% 1.87/1.02  splitting_time:                         0.
% 1.87/1.02  sem_filter_time:                        0.
% 1.87/1.02  monotx_time:                            0.
% 1.87/1.02  subtype_inf_time:                       0.
% 1.87/1.02  
% 1.87/1.02  ------ Problem properties
% 1.87/1.02  
% 1.87/1.02  clauses:                                31
% 1.87/1.02  conjectures:                            2
% 1.87/1.02  epr:                                    3
% 1.87/1.02  horn:                                   28
% 1.87/1.02  ground:                                 10
% 1.87/1.02  unary:                                  13
% 1.87/1.02  binary:                                 12
% 1.87/1.02  lits:                                   56
% 1.87/1.02  lits_eq:                                33
% 1.87/1.02  fd_pure:                                0
% 1.87/1.02  fd_pseudo:                              0
% 1.87/1.02  fd_cond:                                2
% 1.87/1.02  fd_pseudo_cond:                         1
% 1.87/1.02  ac_symbols:                             0
% 1.87/1.02  
% 1.87/1.02  ------ Propositional Solver
% 1.87/1.02  
% 1.87/1.02  prop_solver_calls:                      28
% 1.87/1.02  prop_fast_solver_calls:                 930
% 1.87/1.02  smt_solver_calls:                       0
% 1.87/1.02  smt_fast_solver_calls:                  0
% 1.87/1.02  prop_num_of_clauses:                    2365
% 1.87/1.02  prop_preprocess_simplified:             7740
% 1.87/1.02  prop_fo_subsumed:                       14
% 1.87/1.02  prop_solver_time:                       0.
% 1.87/1.02  smt_solver_time:                        0.
% 1.87/1.02  smt_fast_solver_time:                   0.
% 1.87/1.02  prop_fast_solver_time:                  0.
% 1.87/1.02  prop_unsat_core_time:                   0.
% 1.87/1.02  
% 1.87/1.02  ------ QBF
% 1.87/1.02  
% 1.87/1.02  qbf_q_res:                              0
% 1.87/1.02  qbf_num_tautologies:                    0
% 1.87/1.02  qbf_prep_cycles:                        0
% 1.87/1.02  
% 1.87/1.02  ------ BMC1
% 1.87/1.02  
% 1.87/1.02  bmc1_current_bound:                     -1
% 1.87/1.02  bmc1_last_solved_bound:                 -1
% 1.87/1.02  bmc1_unsat_core_size:                   -1
% 1.87/1.02  bmc1_unsat_core_parents_size:           -1
% 1.87/1.02  bmc1_merge_next_fun:                    0
% 1.87/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.87/1.02  
% 1.87/1.02  ------ Instantiation
% 1.87/1.02  
% 1.87/1.02  inst_num_of_clauses:                    945
% 1.87/1.02  inst_num_in_passive:                    526
% 1.87/1.02  inst_num_in_active:                     394
% 1.87/1.02  inst_num_in_unprocessed:                25
% 1.87/1.02  inst_num_of_loops:                      450
% 1.87/1.02  inst_num_of_learning_restarts:          0
% 1.87/1.02  inst_num_moves_active_passive:          54
% 1.87/1.02  inst_lit_activity:                      0
% 1.87/1.02  inst_lit_activity_moves:                0
% 1.87/1.02  inst_num_tautologies:                   0
% 1.87/1.02  inst_num_prop_implied:                  0
% 1.87/1.02  inst_num_existing_simplified:           0
% 1.87/1.02  inst_num_eq_res_simplified:             0
% 1.87/1.02  inst_num_child_elim:                    0
% 1.87/1.02  inst_num_of_dismatching_blockings:      254
% 1.87/1.02  inst_num_of_non_proper_insts:           874
% 1.87/1.02  inst_num_of_duplicates:                 0
% 1.87/1.02  inst_inst_num_from_inst_to_res:         0
% 1.87/1.02  inst_dismatching_checking_time:         0.
% 1.87/1.02  
% 1.87/1.02  ------ Resolution
% 1.87/1.02  
% 1.87/1.02  res_num_of_clauses:                     0
% 1.87/1.02  res_num_in_passive:                     0
% 1.87/1.02  res_num_in_active:                      0
% 1.87/1.02  res_num_of_loops:                       167
% 1.87/1.02  res_forward_subset_subsumed:            62
% 1.87/1.02  res_backward_subset_subsumed:           4
% 1.87/1.02  res_forward_subsumed:                   0
% 1.87/1.02  res_backward_subsumed:                  0
% 1.87/1.02  res_forward_subsumption_resolution:     1
% 1.87/1.02  res_backward_subsumption_resolution:    0
% 1.87/1.02  res_clause_to_clause_subsumption:       164
% 1.87/1.02  res_orphan_elimination:                 0
% 1.87/1.02  res_tautology_del:                      64
% 1.87/1.02  res_num_eq_res_simplified:              0
% 1.87/1.02  res_num_sel_changes:                    0
% 1.87/1.02  res_moves_from_active_to_pass:          0
% 1.87/1.02  
% 1.87/1.02  ------ Superposition
% 1.87/1.02  
% 1.87/1.02  sup_time_total:                         0.
% 1.87/1.02  sup_time_generating:                    0.
% 1.87/1.02  sup_time_sim_full:                      0.
% 1.87/1.02  sup_time_sim_immed:                     0.
% 1.87/1.02  
% 1.87/1.02  sup_num_of_clauses:                     104
% 1.87/1.02  sup_num_in_active:                      85
% 1.87/1.02  sup_num_in_passive:                     19
% 1.87/1.02  sup_num_of_loops:                       89
% 1.87/1.02  sup_fw_superposition:                   89
% 1.87/1.02  sup_bw_superposition:                   46
% 1.87/1.02  sup_immediate_simplified:               53
% 1.87/1.02  sup_given_eliminated:                   1
% 1.87/1.02  comparisons_done:                       0
% 1.87/1.02  comparisons_avoided:                    33
% 1.87/1.02  
% 1.87/1.02  ------ Simplifications
% 1.87/1.02  
% 1.87/1.02  
% 1.87/1.02  sim_fw_subset_subsumed:                 26
% 1.87/1.02  sim_bw_subset_subsumed:                 3
% 1.87/1.02  sim_fw_subsumed:                        5
% 1.87/1.02  sim_bw_subsumed:                        1
% 1.87/1.02  sim_fw_subsumption_res:                 1
% 1.87/1.02  sim_bw_subsumption_res:                 0
% 1.87/1.02  sim_tautology_del:                      1
% 1.87/1.02  sim_eq_tautology_del:                   4
% 1.87/1.02  sim_eq_res_simp:                        8
% 1.87/1.02  sim_fw_demodulated:                     17
% 1.87/1.02  sim_bw_demodulated:                     3
% 1.87/1.02  sim_light_normalised:                   18
% 1.87/1.02  sim_joinable_taut:                      0
% 1.87/1.02  sim_joinable_simp:                      0
% 1.87/1.02  sim_ac_normalised:                      0
% 1.87/1.02  sim_smt_subsumption:                    0
% 1.87/1.02  
%------------------------------------------------------------------------------
