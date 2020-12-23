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

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  166 (2355 expanded)
%              Number of clauses        :  105 ( 751 expanded)
%              Number of leaves         :   18 ( 668 expanded)
%              Depth                    :   32
%              Number of atoms          :  514 (13777 expanded)
%              Number of equality atoms :  268 (5615 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   3 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f87,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f93,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f58])).

fof(f92,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f94,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f58])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f89,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f91,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f90,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f95,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k1_xboole_0 != k2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f96,plain,(
    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f100,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f88])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f98,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f62])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_477,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK2) != X2
    | u1_struct_0(sK1) != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_34])).

cnf(c_478,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_480,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1))
    | k1_xboole_0 = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_478,c_35,c_33])).

cnf(c_27,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_23,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_546,plain,
    ( v4_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_33])).

cnf(c_547,plain,
    ( v4_relat_1(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_593,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_relat_1(X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_547])).

cnf(c_594,plain,
    ( ~ v1_partfun1(sK3,X0)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_593])).

cnf(c_729,plain,
    ( ~ v1_relat_1(sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK1) != X0
    | k1_relat_1(sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_480,c_594])).

cnf(c_730,plain,
    ( ~ v1_relat_1(sK3)
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(sK3) = u1_struct_0(sK1)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0)) ),
    inference(unflattening,[status(thm)],[c_729])).

cnf(c_945,plain,
    ( ~ v1_relat_1(sK3)
    | sP0_iProver_split
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(sK3) = u1_struct_0(sK1) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_730])).

cnf(c_1290,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(sK3) = u1_struct_0(sK1)
    | v1_relat_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_945])).

cnf(c_30,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_36,negated_conjecture,
    ( l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_390,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_36])).

cnf(c_391,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_37,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_395,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_37])).

cnf(c_396,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_1384,plain,
    ( k2_struct_0(sK2) = k1_xboole_0
    | k2_struct_0(sK1) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_1290,c_391,c_396])).

cnf(c_949,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1486,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_949])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_507,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_33])).

cnf(c_508,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_1487,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_508])).

cnf(c_1489,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1487])).

cnf(c_944,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_730])).

cnf(c_1291,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_944])).

cnf(c_1379,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),X0))
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1291,c_391,c_396])).

cnf(c_1542,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1379])).

cnf(c_12,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1648,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1649,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1648])).

cnf(c_1829,plain,
    ( k2_struct_0(sK2) = k1_xboole_0
    | k2_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1384,c_1486,c_1489,c_1542,c_1649])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != k2_struct_0(sK2)
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1841,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1829,c_32])).

cnf(c_22,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_8,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_402,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_22,c_8])).

cnf(c_522,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_402,c_33])).

cnf(c_523,plain,
    ( r1_tarski(k2_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_1294,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r1_tarski(k2_relat_1(sK3),X1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_523])).

cnf(c_1417,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r1_tarski(k2_relat_1(sK3),X1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1294,c_391,c_396])).

cnf(c_1807,plain,
    ( r1_tarski(k2_relat_1(sK3),X1) = iProver_top
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1417,c_1486,c_1489,c_1649])).

cnf(c_1808,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r1_tarski(k2_relat_1(sK3),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1807])).

cnf(c_1817,plain,
    ( r1_tarski(k2_relat_1(sK3),k2_struct_0(sK2)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1808])).

cnf(c_18,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1299,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4316,plain,
    ( k5_relat_1(sK3,k6_relat_1(k2_struct_0(sK2))) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1817,c_1299])).

cnf(c_4865,plain,
    ( k5_relat_1(sK3,k6_relat_1(k2_struct_0(sK2))) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4316,c_1486,c_1489,c_1649])).

cnf(c_9,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1304,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1295,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_1399,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1295,c_391,c_396])).

cnf(c_1929,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_struct_0(sK2))) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1841,c_1399])).

cnf(c_2394,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1929,c_1486,c_1489,c_1649])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1301,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4563,plain,
    ( k10_relat_1(sK3,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK3,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2394,c_1301])).

cnf(c_4648,plain,
    ( k10_relat_1(sK3,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_1304,c_4563])).

cnf(c_17,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_4660,plain,
    ( k1_relat_1(k5_relat_1(sK3,k6_relat_1(X0))) = k10_relat_1(sK3,X0) ),
    inference(light_normalisation,[status(thm)],[c_4648,c_17])).

cnf(c_5209,plain,
    ( k10_relat_1(sK3,k2_struct_0(sK2)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_4865,c_4660])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_537,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_33])).

cnf(c_538,plain,
    ( k8_relset_1(X0,X1,sK3,X2) = k10_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_1412,plain,
    ( k8_relset_1(X0,X1,sK3,X2) = k10_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_538,c_391,c_396])).

cnf(c_1747,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(equality_resolution,[status(thm)],[c_1412])).

cnf(c_31,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1350,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_31,c_391,c_396])).

cnf(c_2697,plain,
    ( k10_relat_1(sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1747,c_1350])).

cnf(c_5674,plain,
    ( k2_struct_0(sK1) != k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_5209,c_2697])).

cnf(c_5695,plain,
    ( k2_struct_0(sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1841,c_5674])).

cnf(c_5697,plain,
    ( k1_relat_1(sK3) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5695,c_5674])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_460,plain,
    ( v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK2) != X1
    | u1_struct_0(sK1) != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_34])).

cnf(c_461,plain,
    ( v1_partfun1(sK3,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))))
    | ~ v1_funct_1(sK3)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_463,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))))
    | v1_partfun1(sK3,k1_xboole_0)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_461,c_35])).

cnf(c_464,plain,
    ( v1_partfun1(sK3,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))))
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_463])).

cnf(c_558,plain,
    ( v1_partfun1(sK3,k1_xboole_0)
    | u1_struct_0(sK1) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2)))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_464])).

cnf(c_708,plain,
    ( ~ v1_relat_1(sK3)
    | u1_struct_0(sK1) != k1_xboole_0
    | k1_relat_1(sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2)))
    | sK3 != sK3
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_558,c_594])).

cnf(c_709,plain,
    ( ~ v1_relat_1(sK3)
    | u1_struct_0(sK1) != k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_708])).

cnf(c_947,plain,
    ( ~ v1_relat_1(sK3)
    | sP1_iProver_split
    | u1_struct_0(sK1) != k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_709])).

cnf(c_1292,plain,
    ( u1_struct_0(sK1) != k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2)))
    | v1_relat_1(sK3) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_947])).

cnf(c_1424,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK2)))
    | v1_relat_1(sK3) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1292,c_391,c_396])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1425,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k1_xboole_0)
    | v1_relat_1(sK3) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_1424,c_3])).

cnf(c_946,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_709])).

cnf(c_1293,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_946])).

cnf(c_1369,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k1_xboole_0)
    | sP1_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1293,c_3,c_391,c_396])).

cnf(c_1431,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k1_xboole_0)
    | v1_relat_1(sK3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1425,c_1369])).

cnf(c_3387,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k1_xboole_0)
    | k1_relat_1(sK3) = k1_xboole_0
    | k2_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1431,c_1486,c_1489,c_1649])).

cnf(c_3388,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k1_xboole_0) ),
    inference(renaming,[status(thm)],[c_3387])).

cnf(c_5709,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK2))) != k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5695,c_3388])).

cnf(c_5785,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK2))) != k1_zfmisc_1(k1_xboole_0) ),
    inference(equality_resolution_simp,[status(thm)],[c_5709])).

cnf(c_5788,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5785,c_3])).

cnf(c_5789,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5788])).

cnf(c_5792,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5697,c_5789])).

cnf(c_5793,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_5792])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:32:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.14/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.01  
% 3.14/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.14/1.01  
% 3.14/1.01  ------  iProver source info
% 3.14/1.01  
% 3.14/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.14/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.14/1.01  git: non_committed_changes: false
% 3.14/1.01  git: last_make_outside_of_git: false
% 3.14/1.01  
% 3.14/1.01  ------ 
% 3.14/1.01  
% 3.14/1.01  ------ Input Options
% 3.14/1.01  
% 3.14/1.01  --out_options                           all
% 3.14/1.01  --tptp_safe_out                         true
% 3.14/1.01  --problem_path                          ""
% 3.14/1.01  --include_path                          ""
% 3.14/1.01  --clausifier                            res/vclausify_rel
% 3.14/1.01  --clausifier_options                    --mode clausify
% 3.14/1.01  --stdin                                 false
% 3.14/1.01  --stats_out                             all
% 3.14/1.01  
% 3.14/1.01  ------ General Options
% 3.14/1.01  
% 3.14/1.01  --fof                                   false
% 3.14/1.01  --time_out_real                         305.
% 3.14/1.01  --time_out_virtual                      -1.
% 3.14/1.01  --symbol_type_check                     false
% 3.14/1.01  --clausify_out                          false
% 3.14/1.01  --sig_cnt_out                           false
% 3.14/1.01  --trig_cnt_out                          false
% 3.14/1.01  --trig_cnt_out_tolerance                1.
% 3.14/1.01  --trig_cnt_out_sk_spl                   false
% 3.14/1.01  --abstr_cl_out                          false
% 3.14/1.01  
% 3.14/1.01  ------ Global Options
% 3.14/1.01  
% 3.14/1.01  --schedule                              default
% 3.14/1.01  --add_important_lit                     false
% 3.14/1.01  --prop_solver_per_cl                    1000
% 3.14/1.01  --min_unsat_core                        false
% 3.14/1.01  --soft_assumptions                      false
% 3.14/1.01  --soft_lemma_size                       3
% 3.14/1.01  --prop_impl_unit_size                   0
% 3.14/1.01  --prop_impl_unit                        []
% 3.14/1.01  --share_sel_clauses                     true
% 3.14/1.01  --reset_solvers                         false
% 3.14/1.01  --bc_imp_inh                            [conj_cone]
% 3.14/1.01  --conj_cone_tolerance                   3.
% 3.14/1.01  --extra_neg_conj                        none
% 3.14/1.01  --large_theory_mode                     true
% 3.14/1.01  --prolific_symb_bound                   200
% 3.14/1.01  --lt_threshold                          2000
% 3.14/1.01  --clause_weak_htbl                      true
% 3.14/1.01  --gc_record_bc_elim                     false
% 3.14/1.01  
% 3.14/1.01  ------ Preprocessing Options
% 3.14/1.01  
% 3.14/1.01  --preprocessing_flag                    true
% 3.14/1.01  --time_out_prep_mult                    0.1
% 3.14/1.01  --splitting_mode                        input
% 3.14/1.01  --splitting_grd                         true
% 3.14/1.01  --splitting_cvd                         false
% 3.14/1.01  --splitting_cvd_svl                     false
% 3.14/1.01  --splitting_nvd                         32
% 3.14/1.01  --sub_typing                            true
% 3.14/1.01  --prep_gs_sim                           true
% 3.14/1.01  --prep_unflatten                        true
% 3.14/1.01  --prep_res_sim                          true
% 3.14/1.01  --prep_upred                            true
% 3.14/1.01  --prep_sem_filter                       exhaustive
% 3.14/1.01  --prep_sem_filter_out                   false
% 3.14/1.01  --pred_elim                             true
% 3.14/1.01  --res_sim_input                         true
% 3.14/1.01  --eq_ax_congr_red                       true
% 3.14/1.01  --pure_diseq_elim                       true
% 3.14/1.01  --brand_transform                       false
% 3.14/1.01  --non_eq_to_eq                          false
% 3.14/1.01  --prep_def_merge                        true
% 3.14/1.01  --prep_def_merge_prop_impl              false
% 3.14/1.01  --prep_def_merge_mbd                    true
% 3.14/1.01  --prep_def_merge_tr_red                 false
% 3.14/1.01  --prep_def_merge_tr_cl                  false
% 3.14/1.01  --smt_preprocessing                     true
% 3.14/1.01  --smt_ac_axioms                         fast
% 3.14/1.01  --preprocessed_out                      false
% 3.14/1.01  --preprocessed_stats                    false
% 3.14/1.01  
% 3.14/1.01  ------ Abstraction refinement Options
% 3.14/1.01  
% 3.14/1.01  --abstr_ref                             []
% 3.14/1.01  --abstr_ref_prep                        false
% 3.14/1.01  --abstr_ref_until_sat                   false
% 3.14/1.01  --abstr_ref_sig_restrict                funpre
% 3.14/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.14/1.01  --abstr_ref_under                       []
% 3.14/1.01  
% 3.14/1.01  ------ SAT Options
% 3.14/1.01  
% 3.14/1.01  --sat_mode                              false
% 3.14/1.01  --sat_fm_restart_options                ""
% 3.14/1.01  --sat_gr_def                            false
% 3.14/1.01  --sat_epr_types                         true
% 3.14/1.01  --sat_non_cyclic_types                  false
% 3.14/1.01  --sat_finite_models                     false
% 3.14/1.01  --sat_fm_lemmas                         false
% 3.14/1.01  --sat_fm_prep                           false
% 3.14/1.01  --sat_fm_uc_incr                        true
% 3.14/1.01  --sat_out_model                         small
% 3.14/1.01  --sat_out_clauses                       false
% 3.14/1.01  
% 3.14/1.01  ------ QBF Options
% 3.14/1.01  
% 3.14/1.01  --qbf_mode                              false
% 3.14/1.01  --qbf_elim_univ                         false
% 3.14/1.01  --qbf_dom_inst                          none
% 3.14/1.01  --qbf_dom_pre_inst                      false
% 3.14/1.01  --qbf_sk_in                             false
% 3.14/1.01  --qbf_pred_elim                         true
% 3.14/1.01  --qbf_split                             512
% 3.14/1.01  
% 3.14/1.01  ------ BMC1 Options
% 3.14/1.01  
% 3.14/1.01  --bmc1_incremental                      false
% 3.14/1.01  --bmc1_axioms                           reachable_all
% 3.14/1.01  --bmc1_min_bound                        0
% 3.14/1.01  --bmc1_max_bound                        -1
% 3.14/1.01  --bmc1_max_bound_default                -1
% 3.14/1.01  --bmc1_symbol_reachability              true
% 3.14/1.01  --bmc1_property_lemmas                  false
% 3.14/1.01  --bmc1_k_induction                      false
% 3.14/1.01  --bmc1_non_equiv_states                 false
% 3.14/1.01  --bmc1_deadlock                         false
% 3.14/1.01  --bmc1_ucm                              false
% 3.14/1.01  --bmc1_add_unsat_core                   none
% 3.14/1.01  --bmc1_unsat_core_children              false
% 3.14/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.14/1.01  --bmc1_out_stat                         full
% 3.14/1.01  --bmc1_ground_init                      false
% 3.14/1.01  --bmc1_pre_inst_next_state              false
% 3.14/1.01  --bmc1_pre_inst_state                   false
% 3.14/1.01  --bmc1_pre_inst_reach_state             false
% 3.14/1.01  --bmc1_out_unsat_core                   false
% 3.14/1.01  --bmc1_aig_witness_out                  false
% 3.14/1.01  --bmc1_verbose                          false
% 3.14/1.01  --bmc1_dump_clauses_tptp                false
% 3.14/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.14/1.01  --bmc1_dump_file                        -
% 3.14/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.14/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.14/1.01  --bmc1_ucm_extend_mode                  1
% 3.14/1.01  --bmc1_ucm_init_mode                    2
% 3.14/1.01  --bmc1_ucm_cone_mode                    none
% 3.14/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.14/1.01  --bmc1_ucm_relax_model                  4
% 3.14/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.14/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.14/1.01  --bmc1_ucm_layered_model                none
% 3.14/1.01  --bmc1_ucm_max_lemma_size               10
% 3.14/1.01  
% 3.14/1.01  ------ AIG Options
% 3.14/1.01  
% 3.14/1.01  --aig_mode                              false
% 3.14/1.01  
% 3.14/1.01  ------ Instantiation Options
% 3.14/1.01  
% 3.14/1.01  --instantiation_flag                    true
% 3.14/1.01  --inst_sos_flag                         false
% 3.14/1.01  --inst_sos_phase                        true
% 3.14/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.14/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.14/1.01  --inst_lit_sel_side                     num_symb
% 3.14/1.01  --inst_solver_per_active                1400
% 3.14/1.01  --inst_solver_calls_frac                1.
% 3.14/1.01  --inst_passive_queue_type               priority_queues
% 3.14/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.14/1.01  --inst_passive_queues_freq              [25;2]
% 3.14/1.01  --inst_dismatching                      true
% 3.14/1.01  --inst_eager_unprocessed_to_passive     true
% 3.14/1.01  --inst_prop_sim_given                   true
% 3.14/1.01  --inst_prop_sim_new                     false
% 3.14/1.01  --inst_subs_new                         false
% 3.14/1.01  --inst_eq_res_simp                      false
% 3.14/1.01  --inst_subs_given                       false
% 3.14/1.01  --inst_orphan_elimination               true
% 3.14/1.01  --inst_learning_loop_flag               true
% 3.14/1.01  --inst_learning_start                   3000
% 3.14/1.01  --inst_learning_factor                  2
% 3.14/1.01  --inst_start_prop_sim_after_learn       3
% 3.14/1.01  --inst_sel_renew                        solver
% 3.14/1.01  --inst_lit_activity_flag                true
% 3.14/1.01  --inst_restr_to_given                   false
% 3.14/1.01  --inst_activity_threshold               500
% 3.14/1.01  --inst_out_proof                        true
% 3.14/1.01  
% 3.14/1.01  ------ Resolution Options
% 3.14/1.01  
% 3.14/1.01  --resolution_flag                       true
% 3.14/1.01  --res_lit_sel                           adaptive
% 3.14/1.01  --res_lit_sel_side                      none
% 3.14/1.01  --res_ordering                          kbo
% 3.14/1.01  --res_to_prop_solver                    active
% 3.14/1.01  --res_prop_simpl_new                    false
% 3.14/1.01  --res_prop_simpl_given                  true
% 3.14/1.01  --res_passive_queue_type                priority_queues
% 3.14/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.14/1.01  --res_passive_queues_freq               [15;5]
% 3.14/1.01  --res_forward_subs                      full
% 3.14/1.01  --res_backward_subs                     full
% 3.14/1.01  --res_forward_subs_resolution           true
% 3.14/1.01  --res_backward_subs_resolution          true
% 3.14/1.01  --res_orphan_elimination                true
% 3.14/1.01  --res_time_limit                        2.
% 3.14/1.01  --res_out_proof                         true
% 3.14/1.01  
% 3.14/1.01  ------ Superposition Options
% 3.14/1.01  
% 3.14/1.01  --superposition_flag                    true
% 3.14/1.01  --sup_passive_queue_type                priority_queues
% 3.14/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.14/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.14/1.01  --demod_completeness_check              fast
% 3.14/1.01  --demod_use_ground                      true
% 3.14/1.01  --sup_to_prop_solver                    passive
% 3.14/1.01  --sup_prop_simpl_new                    true
% 3.14/1.01  --sup_prop_simpl_given                  true
% 3.14/1.01  --sup_fun_splitting                     false
% 3.14/1.01  --sup_smt_interval                      50000
% 3.14/1.01  
% 3.14/1.01  ------ Superposition Simplification Setup
% 3.14/1.01  
% 3.14/1.01  --sup_indices_passive                   []
% 3.14/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.14/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/1.01  --sup_full_bw                           [BwDemod]
% 3.14/1.01  --sup_immed_triv                        [TrivRules]
% 3.14/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.14/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/1.01  --sup_immed_bw_main                     []
% 3.14/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.14/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/1.01  
% 3.14/1.01  ------ Combination Options
% 3.14/1.01  
% 3.14/1.01  --comb_res_mult                         3
% 3.14/1.01  --comb_sup_mult                         2
% 3.14/1.01  --comb_inst_mult                        10
% 3.14/1.01  
% 3.14/1.01  ------ Debug Options
% 3.14/1.01  
% 3.14/1.01  --dbg_backtrace                         false
% 3.14/1.01  --dbg_dump_prop_clauses                 false
% 3.14/1.01  --dbg_dump_prop_clauses_file            -
% 3.14/1.01  --dbg_out_stat                          false
% 3.14/1.01  ------ Parsing...
% 3.14/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.14/1.01  
% 3.14/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 3.14/1.01  
% 3.14/1.01  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.14/1.01  
% 3.14/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.14/1.01  ------ Proving...
% 3.14/1.01  ------ Problem Properties 
% 3.14/1.01  
% 3.14/1.01  
% 3.14/1.01  clauses                                 30
% 3.14/1.01  conjectures                             2
% 3.14/1.01  EPR                                     3
% 3.14/1.01  Horn                                    27
% 3.14/1.01  unary                                   12
% 3.14/1.01  binary                                  10
% 3.14/1.01  lits                                    59
% 3.14/1.01  lits eq                                 31
% 3.14/1.01  fd_pure                                 0
% 3.14/1.01  fd_pseudo                               0
% 3.14/1.01  fd_cond                                 2
% 3.14/1.01  fd_pseudo_cond                          1
% 3.14/1.01  AC symbols                              0
% 3.14/1.01  
% 3.14/1.01  ------ Schedule dynamic 5 is on 
% 3.14/1.01  
% 3.14/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.14/1.01  
% 3.14/1.01  
% 3.14/1.01  ------ 
% 3.14/1.01  Current options:
% 3.14/1.01  ------ 
% 3.14/1.01  
% 3.14/1.01  ------ Input Options
% 3.14/1.01  
% 3.14/1.01  --out_options                           all
% 3.14/1.01  --tptp_safe_out                         true
% 3.14/1.01  --problem_path                          ""
% 3.14/1.01  --include_path                          ""
% 3.14/1.01  --clausifier                            res/vclausify_rel
% 3.14/1.01  --clausifier_options                    --mode clausify
% 3.14/1.01  --stdin                                 false
% 3.14/1.01  --stats_out                             all
% 3.14/1.01  
% 3.14/1.01  ------ General Options
% 3.14/1.01  
% 3.14/1.01  --fof                                   false
% 3.14/1.01  --time_out_real                         305.
% 3.14/1.01  --time_out_virtual                      -1.
% 3.14/1.01  --symbol_type_check                     false
% 3.14/1.01  --clausify_out                          false
% 3.14/1.01  --sig_cnt_out                           false
% 3.14/1.01  --trig_cnt_out                          false
% 3.14/1.01  --trig_cnt_out_tolerance                1.
% 3.14/1.01  --trig_cnt_out_sk_spl                   false
% 3.14/1.01  --abstr_cl_out                          false
% 3.14/1.01  
% 3.14/1.01  ------ Global Options
% 3.14/1.01  
% 3.14/1.01  --schedule                              default
% 3.14/1.01  --add_important_lit                     false
% 3.14/1.01  --prop_solver_per_cl                    1000
% 3.14/1.01  --min_unsat_core                        false
% 3.14/1.01  --soft_assumptions                      false
% 3.14/1.01  --soft_lemma_size                       3
% 3.14/1.01  --prop_impl_unit_size                   0
% 3.14/1.01  --prop_impl_unit                        []
% 3.14/1.01  --share_sel_clauses                     true
% 3.14/1.01  --reset_solvers                         false
% 3.14/1.01  --bc_imp_inh                            [conj_cone]
% 3.14/1.01  --conj_cone_tolerance                   3.
% 3.14/1.01  --extra_neg_conj                        none
% 3.14/1.01  --large_theory_mode                     true
% 3.14/1.01  --prolific_symb_bound                   200
% 3.14/1.01  --lt_threshold                          2000
% 3.14/1.01  --clause_weak_htbl                      true
% 3.14/1.01  --gc_record_bc_elim                     false
% 3.14/1.01  
% 3.14/1.01  ------ Preprocessing Options
% 3.14/1.01  
% 3.14/1.01  --preprocessing_flag                    true
% 3.14/1.01  --time_out_prep_mult                    0.1
% 3.14/1.01  --splitting_mode                        input
% 3.14/1.01  --splitting_grd                         true
% 3.14/1.01  --splitting_cvd                         false
% 3.14/1.01  --splitting_cvd_svl                     false
% 3.14/1.01  --splitting_nvd                         32
% 3.14/1.01  --sub_typing                            true
% 3.14/1.01  --prep_gs_sim                           true
% 3.14/1.01  --prep_unflatten                        true
% 3.14/1.01  --prep_res_sim                          true
% 3.14/1.01  --prep_upred                            true
% 3.14/1.01  --prep_sem_filter                       exhaustive
% 3.14/1.01  --prep_sem_filter_out                   false
% 3.14/1.01  --pred_elim                             true
% 3.14/1.01  --res_sim_input                         true
% 3.14/1.01  --eq_ax_congr_red                       true
% 3.14/1.01  --pure_diseq_elim                       true
% 3.14/1.01  --brand_transform                       false
% 3.14/1.01  --non_eq_to_eq                          false
% 3.14/1.01  --prep_def_merge                        true
% 3.14/1.01  --prep_def_merge_prop_impl              false
% 3.14/1.01  --prep_def_merge_mbd                    true
% 3.14/1.01  --prep_def_merge_tr_red                 false
% 3.14/1.01  --prep_def_merge_tr_cl                  false
% 3.14/1.01  --smt_preprocessing                     true
% 3.14/1.01  --smt_ac_axioms                         fast
% 3.14/1.01  --preprocessed_out                      false
% 3.14/1.01  --preprocessed_stats                    false
% 3.14/1.01  
% 3.14/1.01  ------ Abstraction refinement Options
% 3.14/1.01  
% 3.14/1.01  --abstr_ref                             []
% 3.14/1.01  --abstr_ref_prep                        false
% 3.14/1.01  --abstr_ref_until_sat                   false
% 3.14/1.01  --abstr_ref_sig_restrict                funpre
% 3.14/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.14/1.01  --abstr_ref_under                       []
% 3.14/1.01  
% 3.14/1.01  ------ SAT Options
% 3.14/1.01  
% 3.14/1.01  --sat_mode                              false
% 3.14/1.01  --sat_fm_restart_options                ""
% 3.14/1.01  --sat_gr_def                            false
% 3.14/1.01  --sat_epr_types                         true
% 3.14/1.01  --sat_non_cyclic_types                  false
% 3.14/1.01  --sat_finite_models                     false
% 3.14/1.01  --sat_fm_lemmas                         false
% 3.14/1.01  --sat_fm_prep                           false
% 3.14/1.01  --sat_fm_uc_incr                        true
% 3.14/1.01  --sat_out_model                         small
% 3.14/1.01  --sat_out_clauses                       false
% 3.14/1.01  
% 3.14/1.01  ------ QBF Options
% 3.14/1.01  
% 3.14/1.01  --qbf_mode                              false
% 3.14/1.01  --qbf_elim_univ                         false
% 3.14/1.01  --qbf_dom_inst                          none
% 3.14/1.01  --qbf_dom_pre_inst                      false
% 3.14/1.01  --qbf_sk_in                             false
% 3.14/1.01  --qbf_pred_elim                         true
% 3.14/1.01  --qbf_split                             512
% 3.14/1.01  
% 3.14/1.01  ------ BMC1 Options
% 3.14/1.01  
% 3.14/1.01  --bmc1_incremental                      false
% 3.14/1.01  --bmc1_axioms                           reachable_all
% 3.14/1.01  --bmc1_min_bound                        0
% 3.14/1.01  --bmc1_max_bound                        -1
% 3.14/1.01  --bmc1_max_bound_default                -1
% 3.14/1.01  --bmc1_symbol_reachability              true
% 3.14/1.01  --bmc1_property_lemmas                  false
% 3.14/1.01  --bmc1_k_induction                      false
% 3.14/1.01  --bmc1_non_equiv_states                 false
% 3.14/1.01  --bmc1_deadlock                         false
% 3.14/1.01  --bmc1_ucm                              false
% 3.14/1.01  --bmc1_add_unsat_core                   none
% 3.14/1.01  --bmc1_unsat_core_children              false
% 3.14/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.14/1.01  --bmc1_out_stat                         full
% 3.14/1.01  --bmc1_ground_init                      false
% 3.14/1.01  --bmc1_pre_inst_next_state              false
% 3.14/1.01  --bmc1_pre_inst_state                   false
% 3.14/1.01  --bmc1_pre_inst_reach_state             false
% 3.14/1.01  --bmc1_out_unsat_core                   false
% 3.14/1.01  --bmc1_aig_witness_out                  false
% 3.14/1.01  --bmc1_verbose                          false
% 3.14/1.01  --bmc1_dump_clauses_tptp                false
% 3.14/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.14/1.01  --bmc1_dump_file                        -
% 3.14/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.14/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.14/1.01  --bmc1_ucm_extend_mode                  1
% 3.14/1.01  --bmc1_ucm_init_mode                    2
% 3.14/1.01  --bmc1_ucm_cone_mode                    none
% 3.14/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.14/1.01  --bmc1_ucm_relax_model                  4
% 3.14/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.14/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.14/1.01  --bmc1_ucm_layered_model                none
% 3.14/1.01  --bmc1_ucm_max_lemma_size               10
% 3.14/1.01  
% 3.14/1.01  ------ AIG Options
% 3.14/1.01  
% 3.14/1.01  --aig_mode                              false
% 3.14/1.01  
% 3.14/1.01  ------ Instantiation Options
% 3.14/1.01  
% 3.14/1.01  --instantiation_flag                    true
% 3.14/1.01  --inst_sos_flag                         false
% 3.14/1.01  --inst_sos_phase                        true
% 3.14/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.14/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.14/1.01  --inst_lit_sel_side                     none
% 3.14/1.01  --inst_solver_per_active                1400
% 3.14/1.01  --inst_solver_calls_frac                1.
% 3.14/1.01  --inst_passive_queue_type               priority_queues
% 3.14/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.14/1.01  --inst_passive_queues_freq              [25;2]
% 3.14/1.01  --inst_dismatching                      true
% 3.14/1.01  --inst_eager_unprocessed_to_passive     true
% 3.14/1.01  --inst_prop_sim_given                   true
% 3.14/1.01  --inst_prop_sim_new                     false
% 3.14/1.01  --inst_subs_new                         false
% 3.14/1.01  --inst_eq_res_simp                      false
% 3.14/1.01  --inst_subs_given                       false
% 3.14/1.01  --inst_orphan_elimination               true
% 3.14/1.01  --inst_learning_loop_flag               true
% 3.14/1.01  --inst_learning_start                   3000
% 3.14/1.01  --inst_learning_factor                  2
% 3.14/1.01  --inst_start_prop_sim_after_learn       3
% 3.14/1.01  --inst_sel_renew                        solver
% 3.14/1.01  --inst_lit_activity_flag                true
% 3.14/1.01  --inst_restr_to_given                   false
% 3.14/1.01  --inst_activity_threshold               500
% 3.14/1.01  --inst_out_proof                        true
% 3.14/1.01  
% 3.14/1.01  ------ Resolution Options
% 3.14/1.01  
% 3.14/1.01  --resolution_flag                       false
% 3.14/1.01  --res_lit_sel                           adaptive
% 3.14/1.01  --res_lit_sel_side                      none
% 3.14/1.01  --res_ordering                          kbo
% 3.14/1.01  --res_to_prop_solver                    active
% 3.14/1.01  --res_prop_simpl_new                    false
% 3.14/1.01  --res_prop_simpl_given                  true
% 3.14/1.01  --res_passive_queue_type                priority_queues
% 3.14/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.14/1.01  --res_passive_queues_freq               [15;5]
% 3.14/1.01  --res_forward_subs                      full
% 3.14/1.01  --res_backward_subs                     full
% 3.14/1.01  --res_forward_subs_resolution           true
% 3.14/1.01  --res_backward_subs_resolution          true
% 3.14/1.01  --res_orphan_elimination                true
% 3.14/1.01  --res_time_limit                        2.
% 3.14/1.01  --res_out_proof                         true
% 3.14/1.01  
% 3.14/1.01  ------ Superposition Options
% 3.14/1.01  
% 3.14/1.01  --superposition_flag                    true
% 3.14/1.01  --sup_passive_queue_type                priority_queues
% 3.14/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.14/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.14/1.01  --demod_completeness_check              fast
% 3.14/1.01  --demod_use_ground                      true
% 3.14/1.01  --sup_to_prop_solver                    passive
% 3.14/1.01  --sup_prop_simpl_new                    true
% 3.14/1.01  --sup_prop_simpl_given                  true
% 3.14/1.01  --sup_fun_splitting                     false
% 3.14/1.01  --sup_smt_interval                      50000
% 3.14/1.01  
% 3.14/1.01  ------ Superposition Simplification Setup
% 3.14/1.01  
% 3.14/1.01  --sup_indices_passive                   []
% 3.14/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.14/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/1.01  --sup_full_bw                           [BwDemod]
% 3.14/1.01  --sup_immed_triv                        [TrivRules]
% 3.14/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.14/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/1.01  --sup_immed_bw_main                     []
% 3.14/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.14/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/1.01  
% 3.14/1.01  ------ Combination Options
% 3.14/1.01  
% 3.14/1.01  --comb_res_mult                         3
% 3.14/1.01  --comb_sup_mult                         2
% 3.14/1.01  --comb_inst_mult                        10
% 3.14/1.01  
% 3.14/1.01  ------ Debug Options
% 3.14/1.01  
% 3.14/1.01  --dbg_backtrace                         false
% 3.14/1.01  --dbg_dump_prop_clauses                 false
% 3.14/1.01  --dbg_dump_prop_clauses_file            -
% 3.14/1.01  --dbg_out_stat                          false
% 3.14/1.01  
% 3.14/1.01  
% 3.14/1.01  
% 3.14/1.01  
% 3.14/1.01  ------ Proving...
% 3.14/1.01  
% 3.14/1.01  
% 3.14/1.01  % SZS status Theorem for theBenchmark.p
% 3.14/1.01  
% 3.14/1.01   Resolution empty clause
% 3.14/1.01  
% 3.14/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.14/1.01  
% 3.14/1.01  fof(f22,axiom,(
% 3.14/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.14/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.01  
% 3.14/1.01  fof(f44,plain,(
% 3.14/1.01    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.14/1.01    inference(ennf_transformation,[],[f22])).
% 3.14/1.01  
% 3.14/1.01  fof(f45,plain,(
% 3.14/1.01    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.14/1.01    inference(flattening,[],[f44])).
% 3.14/1.01  
% 3.14/1.01  fof(f87,plain,(
% 3.14/1.01    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.14/1.01    inference(cnf_transformation,[],[f45])).
% 3.14/1.01  
% 3.14/1.01  fof(f24,conjecture,(
% 3.14/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 3.14/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.01  
% 3.14/1.01  fof(f25,negated_conjecture,(
% 3.14/1.01    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 3.14/1.01    inference(negated_conjecture,[],[f24])).
% 3.14/1.01  
% 3.14/1.01  fof(f47,plain,(
% 3.14/1.01    ? [X0] : (? [X1] : (? [X2] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 3.14/1.01    inference(ennf_transformation,[],[f25])).
% 3.14/1.01  
% 3.14/1.01  fof(f48,plain,(
% 3.14/1.01    ? [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 3.14/1.01    inference(flattening,[],[f47])).
% 3.14/1.01  
% 3.14/1.01  fof(f57,plain,(
% 3.14/1.01    ( ! [X0,X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 3.14/1.01    introduced(choice_axiom,[])).
% 3.14/1.01  
% 3.14/1.01  fof(f56,plain,(
% 3.14/1.01    ( ! [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2,k2_struct_0(sK2)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(sK2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_struct_0(sK2))) )),
% 3.14/1.01    introduced(choice_axiom,[])).
% 3.14/1.01  
% 3.14/1.01  fof(f55,plain,(
% 3.14/1.01    ? [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(sK1) & (k1_xboole_0 = k2_struct_0(sK1) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK1))),
% 3.14/1.01    introduced(choice_axiom,[])).
% 3.14/1.01  
% 3.14/1.01  fof(f58,plain,(
% 3.14/1.01    ((k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) & (k1_xboole_0 = k2_struct_0(sK1) | k1_xboole_0 != k2_struct_0(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_struct_0(sK2)) & l1_struct_0(sK1)),
% 3.14/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f48,f57,f56,f55])).
% 3.14/1.01  
% 3.14/1.01  fof(f93,plain,(
% 3.14/1.01    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 3.14/1.01    inference(cnf_transformation,[],[f58])).
% 3.14/1.01  
% 3.14/1.01  fof(f92,plain,(
% 3.14/1.01    v1_funct_1(sK3)),
% 3.14/1.01    inference(cnf_transformation,[],[f58])).
% 3.14/1.01  
% 3.14/1.01  fof(f94,plain,(
% 3.14/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 3.14/1.01    inference(cnf_transformation,[],[f58])).
% 3.14/1.01  
% 3.14/1.01  fof(f21,axiom,(
% 3.14/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.14/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.01  
% 3.14/1.01  fof(f42,plain,(
% 3.14/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.14/1.01    inference(ennf_transformation,[],[f21])).
% 3.14/1.01  
% 3.14/1.01  fof(f43,plain,(
% 3.14/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.14/1.01    inference(flattening,[],[f42])).
% 3.14/1.01  
% 3.14/1.01  fof(f54,plain,(
% 3.14/1.01    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.14/1.01    inference(nnf_transformation,[],[f43])).
% 3.14/1.01  
% 3.14/1.01  fof(f85,plain,(
% 3.14/1.01    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.14/1.01    inference(cnf_transformation,[],[f54])).
% 3.14/1.01  
% 3.14/1.01  fof(f18,axiom,(
% 3.14/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.14/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.01  
% 3.14/1.01  fof(f39,plain,(
% 3.14/1.01    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/1.01    inference(ennf_transformation,[],[f18])).
% 3.14/1.01  
% 3.14/1.01  fof(f81,plain,(
% 3.14/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/1.01    inference(cnf_transformation,[],[f39])).
% 3.14/1.01  
% 3.14/1.01  fof(f23,axiom,(
% 3.14/1.01    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.14/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.01  
% 3.14/1.01  fof(f46,plain,(
% 3.14/1.01    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.14/1.01    inference(ennf_transformation,[],[f23])).
% 3.14/1.01  
% 3.14/1.01  fof(f89,plain,(
% 3.14/1.01    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.14/1.01    inference(cnf_transformation,[],[f46])).
% 3.14/1.01  
% 3.14/1.01  fof(f91,plain,(
% 3.14/1.01    l1_struct_0(sK2)),
% 3.14/1.01    inference(cnf_transformation,[],[f58])).
% 3.14/1.01  
% 3.14/1.01  fof(f90,plain,(
% 3.14/1.01    l1_struct_0(sK1)),
% 3.14/1.01    inference(cnf_transformation,[],[f58])).
% 3.14/1.01  
% 3.14/1.01  fof(f5,axiom,(
% 3.14/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.14/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.01  
% 3.14/1.01  fof(f29,plain,(
% 3.14/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.14/1.01    inference(ennf_transformation,[],[f5])).
% 3.14/1.01  
% 3.14/1.01  fof(f65,plain,(
% 3.14/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.14/1.01    inference(cnf_transformation,[],[f29])).
% 3.14/1.01  
% 3.14/1.01  fof(f9,axiom,(
% 3.14/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.14/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.01  
% 3.14/1.01  fof(f71,plain,(
% 3.14/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.14/1.01    inference(cnf_transformation,[],[f9])).
% 3.14/1.01  
% 3.14/1.01  fof(f95,plain,(
% 3.14/1.01    k1_xboole_0 = k2_struct_0(sK1) | k1_xboole_0 != k2_struct_0(sK2)),
% 3.14/1.01    inference(cnf_transformation,[],[f58])).
% 3.14/1.01  
% 3.14/1.01  fof(f82,plain,(
% 3.14/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/1.01    inference(cnf_transformation,[],[f39])).
% 3.14/1.01  
% 3.14/1.01  fof(f6,axiom,(
% 3.14/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.14/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.01  
% 3.14/1.01  fof(f30,plain,(
% 3.14/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.14/1.01    inference(ennf_transformation,[],[f6])).
% 3.14/1.01  
% 3.14/1.01  fof(f51,plain,(
% 3.14/1.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.14/1.01    inference(nnf_transformation,[],[f30])).
% 3.14/1.01  
% 3.14/1.01  fof(f66,plain,(
% 3.14/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.14/1.01    inference(cnf_transformation,[],[f51])).
% 3.14/1.01  
% 3.14/1.01  fof(f14,axiom,(
% 3.14/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 3.14/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.01  
% 3.14/1.01  fof(f35,plain,(
% 3.14/1.01    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.14/1.01    inference(ennf_transformation,[],[f14])).
% 3.14/1.01  
% 3.14/1.01  fof(f36,plain,(
% 3.14/1.01    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.14/1.01    inference(flattening,[],[f35])).
% 3.14/1.01  
% 3.14/1.01  fof(f77,plain,(
% 3.14/1.01    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.14/1.01    inference(cnf_transformation,[],[f36])).
% 3.14/1.01  
% 3.14/1.01  fof(f7,axiom,(
% 3.14/1.01    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.14/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.01  
% 3.14/1.01  fof(f68,plain,(
% 3.14/1.01    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.14/1.01    inference(cnf_transformation,[],[f7])).
% 3.14/1.01  
% 3.14/1.01  fof(f11,axiom,(
% 3.14/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 3.14/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.01  
% 3.14/1.01  fof(f34,plain,(
% 3.14/1.01    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.14/1.01    inference(ennf_transformation,[],[f11])).
% 3.14/1.01  
% 3.14/1.01  fof(f73,plain,(
% 3.14/1.01    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.14/1.01    inference(cnf_transformation,[],[f34])).
% 3.14/1.01  
% 3.14/1.01  fof(f13,axiom,(
% 3.14/1.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.14/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.01  
% 3.14/1.01  fof(f75,plain,(
% 3.14/1.01    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.14/1.01    inference(cnf_transformation,[],[f13])).
% 3.14/1.01  
% 3.14/1.01  fof(f19,axiom,(
% 3.14/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.14/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.01  
% 3.14/1.01  fof(f40,plain,(
% 3.14/1.01    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/1.01    inference(ennf_transformation,[],[f19])).
% 3.14/1.01  
% 3.14/1.01  fof(f83,plain,(
% 3.14/1.01    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/1.01    inference(cnf_transformation,[],[f40])).
% 3.14/1.01  
% 3.14/1.01  fof(f96,plain,(
% 3.14/1.01    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1)),
% 3.14/1.01    inference(cnf_transformation,[],[f58])).
% 3.14/1.01  
% 3.14/1.01  fof(f88,plain,(
% 3.14/1.01    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.14/1.01    inference(cnf_transformation,[],[f45])).
% 3.14/1.01  
% 3.14/1.01  fof(f100,plain,(
% 3.14/1.01    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 3.14/1.01    inference(equality_resolution,[],[f88])).
% 3.14/1.01  
% 3.14/1.01  fof(f3,axiom,(
% 3.14/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.14/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/1.01  
% 3.14/1.01  fof(f49,plain,(
% 3.14/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.14/1.01    inference(nnf_transformation,[],[f3])).
% 3.14/1.01  
% 3.14/1.01  fof(f50,plain,(
% 3.14/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.14/1.01    inference(flattening,[],[f49])).
% 3.14/1.01  
% 3.14/1.01  fof(f62,plain,(
% 3.14/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.14/1.01    inference(cnf_transformation,[],[f50])).
% 3.14/1.01  
% 3.14/1.01  fof(f98,plain,(
% 3.14/1.01    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.14/1.01    inference(equality_resolution,[],[f62])).
% 3.14/1.01  
% 3.14/1.01  cnf(c_29,plain,
% 3.14/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.14/1.01      | v1_partfun1(X0,X1)
% 3.14/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/1.01      | ~ v1_funct_1(X0)
% 3.14/1.01      | k1_xboole_0 = X2 ),
% 3.14/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_34,negated_conjecture,
% 3.14/1.01      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 3.14/1.01      inference(cnf_transformation,[],[f93]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_477,plain,
% 3.14/1.01      ( v1_partfun1(X0,X1)
% 3.14/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/1.01      | ~ v1_funct_1(X0)
% 3.14/1.01      | u1_struct_0(sK2) != X2
% 3.14/1.01      | u1_struct_0(sK1) != X1
% 3.14/1.01      | sK3 != X0
% 3.14/1.01      | k1_xboole_0 = X2 ),
% 3.14/1.01      inference(resolution_lifted,[status(thm)],[c_29,c_34]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_478,plain,
% 3.14/1.01      ( v1_partfun1(sK3,u1_struct_0(sK1))
% 3.14/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 3.14/1.01      | ~ v1_funct_1(sK3)
% 3.14/1.01      | k1_xboole_0 = u1_struct_0(sK2) ),
% 3.14/1.01      inference(unflattening,[status(thm)],[c_477]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_35,negated_conjecture,
% 3.14/1.01      ( v1_funct_1(sK3) ),
% 3.14/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_33,negated_conjecture,
% 3.14/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 3.14/1.01      inference(cnf_transformation,[],[f94]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_480,plain,
% 3.14/1.01      ( v1_partfun1(sK3,u1_struct_0(sK1)) | k1_xboole_0 = u1_struct_0(sK2) ),
% 3.14/1.01      inference(global_propositional_subsumption,
% 3.14/1.01                [status(thm)],
% 3.14/1.01                [c_478,c_35,c_33]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_27,plain,
% 3.14/1.01      ( ~ v1_partfun1(X0,X1)
% 3.14/1.01      | ~ v4_relat_1(X0,X1)
% 3.14/1.01      | ~ v1_relat_1(X0)
% 3.14/1.01      | k1_relat_1(X0) = X1 ),
% 3.14/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_23,plain,
% 3.14/1.01      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.14/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_546,plain,
% 3.14/1.01      ( v4_relat_1(X0,X1)
% 3.14/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.14/1.01      | sK3 != X0 ),
% 3.14/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_33]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_547,plain,
% 3.14/1.01      ( v4_relat_1(sK3,X0)
% 3.14/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.14/1.01      inference(unflattening,[status(thm)],[c_546]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_593,plain,
% 3.14/1.01      ( ~ v1_partfun1(X0,X1)
% 3.14/1.01      | ~ v1_relat_1(X0)
% 3.14/1.01      | X2 != X1
% 3.14/1.01      | k1_relat_1(X0) = X1
% 3.14/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 3.14/1.01      | sK3 != X0 ),
% 3.14/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_547]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_594,plain,
% 3.14/1.01      ( ~ v1_partfun1(sK3,X0)
% 3.14/1.01      | ~ v1_relat_1(sK3)
% 3.14/1.01      | k1_relat_1(sK3) = X0
% 3.14/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.14/1.01      inference(unflattening,[status(thm)],[c_593]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_729,plain,
% 3.14/1.01      ( ~ v1_relat_1(sK3)
% 3.14/1.01      | u1_struct_0(sK2) = k1_xboole_0
% 3.14/1.01      | u1_struct_0(sK1) != X0
% 3.14/1.01      | k1_relat_1(sK3) = X0
% 3.14/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.14/1.01      | sK3 != sK3 ),
% 3.14/1.01      inference(resolution_lifted,[status(thm)],[c_480,c_594]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_730,plain,
% 3.14/1.01      ( ~ v1_relat_1(sK3)
% 3.14/1.01      | u1_struct_0(sK2) = k1_xboole_0
% 3.14/1.01      | k1_relat_1(sK3) = u1_struct_0(sK1)
% 3.14/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0)) ),
% 3.14/1.01      inference(unflattening,[status(thm)],[c_729]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_945,plain,
% 3.14/1.01      ( ~ v1_relat_1(sK3)
% 3.14/1.01      | sP0_iProver_split
% 3.14/1.01      | u1_struct_0(sK2) = k1_xboole_0
% 3.14/1.01      | k1_relat_1(sK3) = u1_struct_0(sK1) ),
% 3.14/1.01      inference(splitting,
% 3.14/1.01                [splitting(split),new_symbols(definition,[])],
% 3.14/1.01                [c_730]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_1290,plain,
% 3.14/1.01      ( u1_struct_0(sK2) = k1_xboole_0
% 3.14/1.01      | k1_relat_1(sK3) = u1_struct_0(sK1)
% 3.14/1.01      | v1_relat_1(sK3) != iProver_top
% 3.14/1.01      | sP0_iProver_split = iProver_top ),
% 3.14/1.01      inference(predicate_to_equality,[status(thm)],[c_945]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_30,plain,
% 3.14/1.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.14/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_36,negated_conjecture,
% 3.14/1.01      ( l1_struct_0(sK2) ),
% 3.14/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_390,plain,
% 3.14/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK2 != X0 ),
% 3.14/1.01      inference(resolution_lifted,[status(thm)],[c_30,c_36]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_391,plain,
% 3.14/1.01      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 3.14/1.01      inference(unflattening,[status(thm)],[c_390]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_37,negated_conjecture,
% 3.14/1.01      ( l1_struct_0(sK1) ),
% 3.14/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_395,plain,
% 3.14/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 3.14/1.01      inference(resolution_lifted,[status(thm)],[c_30,c_37]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_396,plain,
% 3.14/1.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.14/1.01      inference(unflattening,[status(thm)],[c_395]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_1384,plain,
% 3.14/1.01      ( k2_struct_0(sK2) = k1_xboole_0
% 3.14/1.01      | k2_struct_0(sK1) = k1_relat_1(sK3)
% 3.14/1.01      | v1_relat_1(sK3) != iProver_top
% 3.14/1.01      | sP0_iProver_split = iProver_top ),
% 3.14/1.01      inference(demodulation,[status(thm)],[c_1290,c_391,c_396]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_949,plain,( X0 = X0 ),theory(equality) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_1486,plain,
% 3.14/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
% 3.14/1.01      inference(instantiation,[status(thm)],[c_949]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_6,plain,
% 3.14/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.14/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_507,plain,
% 3.14/1.01      ( ~ v1_relat_1(X0)
% 3.14/1.01      | v1_relat_1(X1)
% 3.14/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(X0)
% 3.14/1.01      | sK3 != X1 ),
% 3.14/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_33]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_508,plain,
% 3.14/1.01      ( ~ v1_relat_1(X0)
% 3.14/1.01      | v1_relat_1(sK3)
% 3.14/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(X0) ),
% 3.14/1.01      inference(unflattening,[status(thm)],[c_507]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_1487,plain,
% 3.14/1.01      ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
% 3.14/1.01      | v1_relat_1(sK3)
% 3.14/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
% 3.14/1.01      inference(instantiation,[status(thm)],[c_508]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_1489,plain,
% 3.14/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
% 3.14/1.01      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != iProver_top
% 3.14/1.01      | v1_relat_1(sK3) = iProver_top ),
% 3.14/1.01      inference(predicate_to_equality,[status(thm)],[c_1487]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_944,plain,
% 3.14/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0))
% 3.14/1.01      | ~ sP0_iProver_split ),
% 3.14/1.01      inference(splitting,
% 3.14/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.14/1.01                [c_730]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_1291,plain,
% 3.14/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0))
% 3.14/1.01      | sP0_iProver_split != iProver_top ),
% 3.14/1.01      inference(predicate_to_equality,[status(thm)],[c_944]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_1379,plain,
% 3.14/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),X0))
% 3.14/1.01      | sP0_iProver_split != iProver_top ),
% 3.14/1.01      inference(light_normalisation,[status(thm)],[c_1291,c_391,c_396]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_1542,plain,
% 3.14/1.01      ( sP0_iProver_split != iProver_top ),
% 3.14/1.01      inference(equality_resolution,[status(thm)],[c_1379]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_12,plain,
% 3.14/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.14/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_1648,plain,
% 3.14/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
% 3.14/1.01      inference(instantiation,[status(thm)],[c_12]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_1649,plain,
% 3.14/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = iProver_top ),
% 3.14/1.01      inference(predicate_to_equality,[status(thm)],[c_1648]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_1829,plain,
% 3.14/1.01      ( k2_struct_0(sK2) = k1_xboole_0 | k2_struct_0(sK1) = k1_relat_1(sK3) ),
% 3.14/1.01      inference(global_propositional_subsumption,
% 3.14/1.01                [status(thm)],
% 3.14/1.01                [c_1384,c_1486,c_1489,c_1542,c_1649]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_32,negated_conjecture,
% 3.14/1.01      ( k1_xboole_0 != k2_struct_0(sK2) | k1_xboole_0 = k2_struct_0(sK1) ),
% 3.14/1.01      inference(cnf_transformation,[],[f95]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_1841,plain,
% 3.14/1.01      ( k2_struct_0(sK1) = k1_relat_1(sK3) | k2_struct_0(sK1) = k1_xboole_0 ),
% 3.14/1.01      inference(superposition,[status(thm)],[c_1829,c_32]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_22,plain,
% 3.14/1.01      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.14/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_8,plain,
% 3.14/1.01      ( r1_tarski(k2_relat_1(X0),X1) | ~ v5_relat_1(X0,X1) | ~ v1_relat_1(X0) ),
% 3.14/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_402,plain,
% 3.14/1.01      ( r1_tarski(k2_relat_1(X0),X1)
% 3.14/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.14/1.01      | ~ v1_relat_1(X0) ),
% 3.14/1.01      inference(resolution,[status(thm)],[c_22,c_8]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_522,plain,
% 3.14/1.01      ( r1_tarski(k2_relat_1(X0),X1)
% 3.14/1.01      | ~ v1_relat_1(X0)
% 3.14/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
% 3.14/1.01      | sK3 != X0 ),
% 3.14/1.01      inference(resolution_lifted,[status(thm)],[c_402,c_33]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_523,plain,
% 3.14/1.01      ( r1_tarski(k2_relat_1(sK3),X0)
% 3.14/1.01      | ~ v1_relat_1(sK3)
% 3.14/1.01      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
% 3.14/1.01      inference(unflattening,[status(thm)],[c_522]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_1294,plain,
% 3.14/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.14/1.01      | r1_tarski(k2_relat_1(sK3),X1) = iProver_top
% 3.14/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.14/1.01      inference(predicate_to_equality,[status(thm)],[c_523]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_1417,plain,
% 3.14/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.14/1.01      | r1_tarski(k2_relat_1(sK3),X1) = iProver_top
% 3.14/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.14/1.01      inference(light_normalisation,[status(thm)],[c_1294,c_391,c_396]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_1807,plain,
% 3.14/1.01      ( r1_tarski(k2_relat_1(sK3),X1) = iProver_top
% 3.14/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.14/1.01      inference(global_propositional_subsumption,
% 3.14/1.01                [status(thm)],
% 3.14/1.01                [c_1417,c_1486,c_1489,c_1649]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_1808,plain,
% 3.14/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.14/1.01      | r1_tarski(k2_relat_1(sK3),X1) = iProver_top ),
% 3.14/1.01      inference(renaming,[status(thm)],[c_1807]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_1817,plain,
% 3.14/1.01      ( r1_tarski(k2_relat_1(sK3),k2_struct_0(sK2)) = iProver_top ),
% 3.14/1.01      inference(equality_resolution,[status(thm)],[c_1808]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_18,plain,
% 3.14/1.01      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.14/1.01      | ~ v1_relat_1(X0)
% 3.14/1.01      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 3.14/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_1299,plain,
% 3.14/1.01      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 3.14/1.01      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.14/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.14/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_4316,plain,
% 3.14/1.01      ( k5_relat_1(sK3,k6_relat_1(k2_struct_0(sK2))) = sK3
% 3.14/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.14/1.01      inference(superposition,[status(thm)],[c_1817,c_1299]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_4865,plain,
% 3.14/1.01      ( k5_relat_1(sK3,k6_relat_1(k2_struct_0(sK2))) = sK3 ),
% 3.14/1.01      inference(global_propositional_subsumption,
% 3.14/1.01                [status(thm)],
% 3.14/1.01                [c_4316,c_1486,c_1489,c_1649]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_9,plain,
% 3.14/1.01      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.14/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_1304,plain,
% 3.14/1.01      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.14/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_1295,plain,
% 3.14/1.01      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(X0)
% 3.14/1.01      | v1_relat_1(X0) != iProver_top
% 3.14/1.01      | v1_relat_1(sK3) = iProver_top ),
% 3.14/1.01      inference(predicate_to_equality,[status(thm)],[c_508]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_1399,plain,
% 3.14/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(X0)
% 3.14/1.01      | v1_relat_1(X0) != iProver_top
% 3.14/1.01      | v1_relat_1(sK3) = iProver_top ),
% 3.14/1.01      inference(light_normalisation,[status(thm)],[c_1295,c_391,c_396]) ).
% 3.14/1.01  
% 3.14/1.01  cnf(c_1929,plain,
% 3.14/1.01      ( k2_struct_0(sK1) = k1_xboole_0
% 3.14/1.01      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_struct_0(sK2))) != k1_zfmisc_1(X0)
% 3.14/1.01      | v1_relat_1(X0) != iProver_top
% 3.14/1.01      | v1_relat_1(sK3) = iProver_top ),
% 3.14/1.02      inference(superposition,[status(thm)],[c_1841,c_1399]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2394,plain,
% 3.14/1.02      ( v1_relat_1(sK3) = iProver_top ),
% 3.14/1.02      inference(global_propositional_subsumption,
% 3.14/1.02                [status(thm)],
% 3.14/1.02                [c_1929,c_1486,c_1489,c_1649]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_14,plain,
% 3.14/1.02      ( ~ v1_relat_1(X0)
% 3.14/1.02      | ~ v1_relat_1(X1)
% 3.14/1.02      | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
% 3.14/1.02      inference(cnf_transformation,[],[f73]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1301,plain,
% 3.14/1.02      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 3.14/1.02      | v1_relat_1(X0) != iProver_top
% 3.14/1.02      | v1_relat_1(X1) != iProver_top ),
% 3.14/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_4563,plain,
% 3.14/1.02      ( k10_relat_1(sK3,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK3,X0))
% 3.14/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.14/1.02      inference(superposition,[status(thm)],[c_2394,c_1301]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_4648,plain,
% 3.14/1.02      ( k10_relat_1(sK3,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(X0))) ),
% 3.14/1.02      inference(superposition,[status(thm)],[c_1304,c_4563]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_17,plain,
% 3.14/1.02      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.14/1.02      inference(cnf_transformation,[],[f75]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_4660,plain,
% 3.14/1.02      ( k1_relat_1(k5_relat_1(sK3,k6_relat_1(X0))) = k10_relat_1(sK3,X0) ),
% 3.14/1.02      inference(light_normalisation,[status(thm)],[c_4648,c_17]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_5209,plain,
% 3.14/1.02      ( k10_relat_1(sK3,k2_struct_0(sK2)) = k1_relat_1(sK3) ),
% 3.14/1.02      inference(superposition,[status(thm)],[c_4865,c_4660]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_24,plain,
% 3.14/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/1.02      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.14/1.02      inference(cnf_transformation,[],[f83]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_537,plain,
% 3.14/1.02      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.14/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.14/1.02      | sK3 != X2 ),
% 3.14/1.02      inference(resolution_lifted,[status(thm)],[c_24,c_33]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_538,plain,
% 3.14/1.02      ( k8_relset_1(X0,X1,sK3,X2) = k10_relat_1(sK3,X2)
% 3.14/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.14/1.02      inference(unflattening,[status(thm)],[c_537]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1412,plain,
% 3.14/1.02      ( k8_relset_1(X0,X1,sK3,X2) = k10_relat_1(sK3,X2)
% 3.14/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.14/1.02      inference(light_normalisation,[status(thm)],[c_538,c_391,c_396]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1747,plain,
% 3.14/1.02      ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,X0) = k10_relat_1(sK3,X0) ),
% 3.14/1.02      inference(equality_resolution,[status(thm)],[c_1412]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_31,negated_conjecture,
% 3.14/1.02      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
% 3.14/1.02      inference(cnf_transformation,[],[f96]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1350,plain,
% 3.14/1.02      ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
% 3.14/1.02      inference(light_normalisation,[status(thm)],[c_31,c_391,c_396]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_2697,plain,
% 3.14/1.02      ( k10_relat_1(sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
% 3.14/1.02      inference(demodulation,[status(thm)],[c_1747,c_1350]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_5674,plain,
% 3.14/1.02      ( k2_struct_0(sK1) != k1_relat_1(sK3) ),
% 3.14/1.02      inference(demodulation,[status(thm)],[c_5209,c_2697]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_5695,plain,
% 3.14/1.02      ( k2_struct_0(sK1) = k1_xboole_0 ),
% 3.14/1.02      inference(superposition,[status(thm)],[c_1841,c_5674]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_5697,plain,
% 3.14/1.02      ( k1_relat_1(sK3) != k1_xboole_0 ),
% 3.14/1.02      inference(demodulation,[status(thm)],[c_5695,c_5674]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_28,plain,
% 3.14/1.02      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.14/1.02      | v1_partfun1(X0,k1_xboole_0)
% 3.14/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.14/1.02      | ~ v1_funct_1(X0) ),
% 3.14/1.02      inference(cnf_transformation,[],[f100]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_460,plain,
% 3.14/1.02      ( v1_partfun1(X0,k1_xboole_0)
% 3.14/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.14/1.02      | ~ v1_funct_1(X0)
% 3.14/1.02      | u1_struct_0(sK2) != X1
% 3.14/1.02      | u1_struct_0(sK1) != k1_xboole_0
% 3.14/1.02      | sK3 != X0 ),
% 3.14/1.02      inference(resolution_lifted,[status(thm)],[c_28,c_34]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_461,plain,
% 3.14/1.02      ( v1_partfun1(sK3,k1_xboole_0)
% 3.14/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))))
% 3.14/1.02      | ~ v1_funct_1(sK3)
% 3.14/1.02      | u1_struct_0(sK1) != k1_xboole_0 ),
% 3.14/1.02      inference(unflattening,[status(thm)],[c_460]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_463,plain,
% 3.14/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))))
% 3.14/1.02      | v1_partfun1(sK3,k1_xboole_0)
% 3.14/1.02      | u1_struct_0(sK1) != k1_xboole_0 ),
% 3.14/1.02      inference(global_propositional_subsumption,[status(thm)],[c_461,c_35]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_464,plain,
% 3.14/1.02      ( v1_partfun1(sK3,k1_xboole_0)
% 3.14/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))))
% 3.14/1.02      | u1_struct_0(sK1) != k1_xboole_0 ),
% 3.14/1.02      inference(renaming,[status(thm)],[c_463]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_558,plain,
% 3.14/1.02      ( v1_partfun1(sK3,k1_xboole_0)
% 3.14/1.02      | u1_struct_0(sK1) != k1_xboole_0
% 3.14/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2)))
% 3.14/1.02      | sK3 != sK3 ),
% 3.14/1.02      inference(resolution_lifted,[status(thm)],[c_33,c_464]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_708,plain,
% 3.14/1.02      ( ~ v1_relat_1(sK3)
% 3.14/1.02      | u1_struct_0(sK1) != k1_xboole_0
% 3.14/1.02      | k1_relat_1(sK3) = X0
% 3.14/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.14/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2)))
% 3.14/1.02      | sK3 != sK3
% 3.14/1.02      | k1_xboole_0 != X0 ),
% 3.14/1.02      inference(resolution_lifted,[status(thm)],[c_558,c_594]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_709,plain,
% 3.14/1.02      ( ~ v1_relat_1(sK3)
% 3.14/1.02      | u1_struct_0(sK1) != k1_xboole_0
% 3.14/1.02      | k1_relat_1(sK3) = k1_xboole_0
% 3.14/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
% 3.14/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))) ),
% 3.14/1.02      inference(unflattening,[status(thm)],[c_708]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_947,plain,
% 3.14/1.02      ( ~ v1_relat_1(sK3)
% 3.14/1.02      | sP1_iProver_split
% 3.14/1.02      | u1_struct_0(sK1) != k1_xboole_0
% 3.14/1.02      | k1_relat_1(sK3) = k1_xboole_0
% 3.14/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))) ),
% 3.14/1.02      inference(splitting,
% 3.14/1.02                [splitting(split),new_symbols(definition,[])],
% 3.14/1.02                [c_709]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1292,plain,
% 3.14/1.02      ( u1_struct_0(sK1) != k1_xboole_0
% 3.14/1.02      | k1_relat_1(sK3) = k1_xboole_0
% 3.14/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2)))
% 3.14/1.02      | v1_relat_1(sK3) != iProver_top
% 3.14/1.02      | sP1_iProver_split = iProver_top ),
% 3.14/1.02      inference(predicate_to_equality,[status(thm)],[c_947]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1424,plain,
% 3.14/1.02      ( k2_struct_0(sK1) != k1_xboole_0
% 3.14/1.02      | k1_relat_1(sK3) = k1_xboole_0
% 3.14/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK2)))
% 3.14/1.02      | v1_relat_1(sK3) != iProver_top
% 3.14/1.02      | sP1_iProver_split = iProver_top ),
% 3.14/1.02      inference(light_normalisation,[status(thm)],[c_1292,c_391,c_396]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_3,plain,
% 3.14/1.02      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.14/1.02      inference(cnf_transformation,[],[f98]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1425,plain,
% 3.14/1.02      ( k2_struct_0(sK1) != k1_xboole_0
% 3.14/1.02      | k1_relat_1(sK3) = k1_xboole_0
% 3.14/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k1_xboole_0)
% 3.14/1.02      | v1_relat_1(sK3) != iProver_top
% 3.14/1.02      | sP1_iProver_split = iProver_top ),
% 3.14/1.02      inference(demodulation,[status(thm)],[c_1424,c_3]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_946,plain,
% 3.14/1.02      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
% 3.14/1.02      | ~ sP1_iProver_split ),
% 3.14/1.02      inference(splitting,
% 3.14/1.02                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 3.14/1.02                [c_709]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1293,plain,
% 3.14/1.02      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
% 3.14/1.02      | sP1_iProver_split != iProver_top ),
% 3.14/1.02      inference(predicate_to_equality,[status(thm)],[c_946]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1369,plain,
% 3.14/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k1_xboole_0)
% 3.14/1.02      | sP1_iProver_split != iProver_top ),
% 3.14/1.02      inference(light_normalisation,[status(thm)],[c_1293,c_3,c_391,c_396]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_1431,plain,
% 3.14/1.02      ( k2_struct_0(sK1) != k1_xboole_0
% 3.14/1.02      | k1_relat_1(sK3) = k1_xboole_0
% 3.14/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k1_xboole_0)
% 3.14/1.02      | v1_relat_1(sK3) != iProver_top ),
% 3.14/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_1425,c_1369]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_3387,plain,
% 3.14/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k1_xboole_0)
% 3.14/1.02      | k1_relat_1(sK3) = k1_xboole_0
% 3.14/1.02      | k2_struct_0(sK1) != k1_xboole_0 ),
% 3.14/1.02      inference(global_propositional_subsumption,
% 3.14/1.02                [status(thm)],
% 3.14/1.02                [c_1431,c_1486,c_1489,c_1649]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_3388,plain,
% 3.14/1.02      ( k2_struct_0(sK1) != k1_xboole_0
% 3.14/1.02      | k1_relat_1(sK3) = k1_xboole_0
% 3.14/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k1_xboole_0) ),
% 3.14/1.02      inference(renaming,[status(thm)],[c_3387]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_5709,plain,
% 3.14/1.02      ( k1_relat_1(sK3) = k1_xboole_0
% 3.14/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK2))) != k1_zfmisc_1(k1_xboole_0)
% 3.14/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 3.14/1.02      inference(demodulation,[status(thm)],[c_5695,c_3388]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_5785,plain,
% 3.14/1.02      ( k1_relat_1(sK3) = k1_xboole_0
% 3.14/1.02      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK2))) != k1_zfmisc_1(k1_xboole_0) ),
% 3.14/1.02      inference(equality_resolution_simp,[status(thm)],[c_5709]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_5788,plain,
% 3.14/1.02      ( k1_relat_1(sK3) = k1_xboole_0
% 3.14/1.02      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
% 3.14/1.02      inference(demodulation,[status(thm)],[c_5785,c_3]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_5789,plain,
% 3.14/1.02      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 3.14/1.02      inference(equality_resolution_simp,[status(thm)],[c_5788]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_5792,plain,
% 3.14/1.02      ( k1_xboole_0 != k1_xboole_0 ),
% 3.14/1.02      inference(light_normalisation,[status(thm)],[c_5697,c_5789]) ).
% 3.14/1.02  
% 3.14/1.02  cnf(c_5793,plain,
% 3.14/1.02      ( $false ),
% 3.14/1.02      inference(equality_resolution_simp,[status(thm)],[c_5792]) ).
% 3.14/1.02  
% 3.14/1.02  
% 3.14/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.14/1.02  
% 3.14/1.02  ------                               Statistics
% 3.14/1.02  
% 3.14/1.02  ------ General
% 3.14/1.02  
% 3.14/1.02  abstr_ref_over_cycles:                  0
% 3.14/1.02  abstr_ref_under_cycles:                 0
% 3.14/1.02  gc_basic_clause_elim:                   0
% 3.14/1.02  forced_gc_time:                         0
% 3.14/1.02  parsing_time:                           0.014
% 3.14/1.02  unif_index_cands_time:                  0.
% 3.14/1.02  unif_index_add_time:                    0.
% 3.14/1.02  orderings_time:                         0.
% 3.14/1.02  out_proof_time:                         0.016
% 3.14/1.02  total_time:                             0.248
% 3.14/1.02  num_of_symbols:                         61
% 3.14/1.02  num_of_terms:                           4512
% 3.14/1.02  
% 3.14/1.02  ------ Preprocessing
% 3.14/1.02  
% 3.14/1.02  num_of_splits:                          2
% 3.14/1.02  num_of_split_atoms:                     2
% 3.14/1.02  num_of_reused_defs:                     0
% 3.14/1.02  num_eq_ax_congr_red:                    20
% 3.14/1.02  num_of_sem_filtered_clauses:            1
% 3.14/1.02  num_of_subtypes:                        0
% 3.14/1.02  monotx_restored_types:                  0
% 3.14/1.02  sat_num_of_epr_types:                   0
% 3.14/1.02  sat_num_of_non_cyclic_types:            0
% 3.14/1.02  sat_guarded_non_collapsed_types:        0
% 3.14/1.02  num_pure_diseq_elim:                    0
% 3.14/1.02  simp_replaced_by:                       0
% 3.14/1.02  res_preprocessed:                       159
% 3.14/1.02  prep_upred:                             0
% 3.14/1.02  prep_unflattend:                        33
% 3.14/1.02  smt_new_axioms:                         0
% 3.14/1.02  pred_elim_cands:                        3
% 3.14/1.02  pred_elim:                              8
% 3.14/1.02  pred_elim_cl:                           10
% 3.14/1.02  pred_elim_cycles:                       12
% 3.14/1.02  merged_defs:                            0
% 3.14/1.02  merged_defs_ncl:                        0
% 3.14/1.02  bin_hyper_res:                          0
% 3.14/1.02  prep_cycles:                            4
% 3.14/1.02  pred_elim_time:                         0.011
% 3.14/1.02  splitting_time:                         0.
% 3.14/1.02  sem_filter_time:                        0.
% 3.14/1.02  monotx_time:                            0.
% 3.14/1.02  subtype_inf_time:                       0.
% 3.14/1.02  
% 3.14/1.02  ------ Problem properties
% 3.14/1.02  
% 3.14/1.02  clauses:                                30
% 3.14/1.02  conjectures:                            2
% 3.14/1.02  epr:                                    3
% 3.14/1.02  horn:                                   27
% 3.14/1.02  ground:                                 8
% 3.14/1.02  unary:                                  12
% 3.14/1.02  binary:                                 10
% 3.14/1.02  lits:                                   59
% 3.14/1.02  lits_eq:                                31
% 3.14/1.02  fd_pure:                                0
% 3.14/1.02  fd_pseudo:                              0
% 3.14/1.02  fd_cond:                                2
% 3.14/1.02  fd_pseudo_cond:                         1
% 3.14/1.02  ac_symbols:                             0
% 3.14/1.02  
% 3.14/1.02  ------ Propositional Solver
% 3.14/1.02  
% 3.14/1.02  prop_solver_calls:                      28
% 3.14/1.02  prop_fast_solver_calls:                 930
% 3.14/1.02  smt_solver_calls:                       0
% 3.14/1.02  smt_fast_solver_calls:                  0
% 3.14/1.02  prop_num_of_clauses:                    2116
% 3.14/1.02  prop_preprocess_simplified:             7258
% 3.14/1.02  prop_fo_subsumed:                       19
% 3.14/1.02  prop_solver_time:                       0.
% 3.14/1.02  smt_solver_time:                        0.
% 3.14/1.02  smt_fast_solver_time:                   0.
% 3.14/1.02  prop_fast_solver_time:                  0.
% 3.14/1.02  prop_unsat_core_time:                   0.
% 3.14/1.02  
% 3.14/1.02  ------ QBF
% 3.14/1.02  
% 3.14/1.02  qbf_q_res:                              0
% 3.14/1.02  qbf_num_tautologies:                    0
% 3.14/1.02  qbf_prep_cycles:                        0
% 3.14/1.02  
% 3.14/1.02  ------ BMC1
% 3.14/1.02  
% 3.14/1.02  bmc1_current_bound:                     -1
% 3.14/1.02  bmc1_last_solved_bound:                 -1
% 3.14/1.02  bmc1_unsat_core_size:                   -1
% 3.14/1.02  bmc1_unsat_core_parents_size:           -1
% 3.14/1.02  bmc1_merge_next_fun:                    0
% 3.14/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.14/1.02  
% 3.14/1.02  ------ Instantiation
% 3.14/1.02  
% 3.14/1.02  inst_num_of_clauses:                    853
% 3.14/1.02  inst_num_in_passive:                    456
% 3.14/1.02  inst_num_in_active:                     348
% 3.14/1.02  inst_num_in_unprocessed:                49
% 3.14/1.02  inst_num_of_loops:                      390
% 3.14/1.02  inst_num_of_learning_restarts:          0
% 3.14/1.02  inst_num_moves_active_passive:          40
% 3.14/1.02  inst_lit_activity:                      0
% 3.14/1.02  inst_lit_activity_moves:                0
% 3.14/1.02  inst_num_tautologies:                   0
% 3.14/1.02  inst_num_prop_implied:                  0
% 3.14/1.02  inst_num_existing_simplified:           0
% 3.14/1.02  inst_num_eq_res_simplified:             0
% 3.14/1.02  inst_num_child_elim:                    0
% 3.14/1.02  inst_num_of_dismatching_blockings:      151
% 3.14/1.02  inst_num_of_non_proper_insts:           748
% 3.14/1.02  inst_num_of_duplicates:                 0
% 3.14/1.02  inst_inst_num_from_inst_to_res:         0
% 3.14/1.02  inst_dismatching_checking_time:         0.
% 3.14/1.02  
% 3.14/1.02  ------ Resolution
% 3.14/1.02  
% 3.14/1.02  res_num_of_clauses:                     0
% 3.14/1.02  res_num_in_passive:                     0
% 3.14/1.02  res_num_in_active:                      0
% 3.14/1.02  res_num_of_loops:                       163
% 3.14/1.02  res_forward_subset_subsumed:            56
% 3.14/1.02  res_backward_subset_subsumed:           6
% 3.14/1.02  res_forward_subsumed:                   0
% 3.14/1.02  res_backward_subsumed:                  0
% 3.14/1.02  res_forward_subsumption_resolution:     0
% 3.14/1.02  res_backward_subsumption_resolution:    0
% 3.14/1.02  res_clause_to_clause_subsumption:       155
% 3.14/1.02  res_orphan_elimination:                 0
% 3.14/1.02  res_tautology_del:                      73
% 3.14/1.02  res_num_eq_res_simplified:              0
% 3.14/1.02  res_num_sel_changes:                    0
% 3.14/1.02  res_moves_from_active_to_pass:          0
% 3.14/1.02  
% 3.14/1.02  ------ Superposition
% 3.14/1.02  
% 3.14/1.02  sup_time_total:                         0.
% 3.14/1.02  sup_time_generating:                    0.
% 3.14/1.02  sup_time_sim_full:                      0.
% 3.14/1.02  sup_time_sim_immed:                     0.
% 3.14/1.02  
% 3.14/1.02  sup_num_of_clauses:                     58
% 3.14/1.02  sup_num_in_active:                      39
% 3.14/1.02  sup_num_in_passive:                     19
% 3.14/1.02  sup_num_of_loops:                       77
% 3.14/1.02  sup_fw_superposition:                   82
% 3.14/1.02  sup_bw_superposition:                   20
% 3.14/1.02  sup_immediate_simplified:               37
% 3.14/1.02  sup_given_eliminated:                   0
% 3.14/1.02  comparisons_done:                       0
% 3.14/1.02  comparisons_avoided:                    21
% 3.14/1.02  
% 3.14/1.02  ------ Simplifications
% 3.14/1.02  
% 3.14/1.02  
% 3.14/1.02  sim_fw_subset_subsumed:                 26
% 3.14/1.02  sim_bw_subset_subsumed:                 4
% 3.14/1.02  sim_fw_subsumed:                        3
% 3.14/1.02  sim_bw_subsumed:                        3
% 3.14/1.02  sim_fw_subsumption_res:                 1
% 3.14/1.02  sim_bw_subsumption_res:                 0
% 3.14/1.02  sim_tautology_del:                      1
% 3.14/1.02  sim_eq_tautology_del:                   10
% 3.14/1.02  sim_eq_res_simp:                        11
% 3.14/1.02  sim_fw_demodulated:                     21
% 3.14/1.02  sim_bw_demodulated:                     37
% 3.14/1.02  sim_light_normalised:                   19
% 3.14/1.02  sim_joinable_taut:                      0
% 3.14/1.02  sim_joinable_simp:                      0
% 3.14/1.02  sim_ac_normalised:                      0
% 3.14/1.02  sim_smt_subsumption:                    0
% 3.14/1.02  
%------------------------------------------------------------------------------
