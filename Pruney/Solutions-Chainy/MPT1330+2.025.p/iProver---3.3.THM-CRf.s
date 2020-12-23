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
% DateTime   : Thu Dec  3 12:16:58 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :  161 (3286 expanded)
%              Number of clauses        :  102 (1037 expanded)
%              Number of leaves         :   17 ( 934 expanded)
%              Depth                    :   34
%              Number of atoms          :  506 (19490 expanded)
%              Number of equality atoms :  259 (7908 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0)
          & ( k1_xboole_0 = k2_struct_0(X0)
            | k1_xboole_0 != k2_struct_0(X1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,k2_struct_0(X1)) != k2_struct_0(X0)
        & ( k1_xboole_0 = k2_struct_0(X0)
          | k1_xboole_0 != k2_struct_0(X1) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
            ( k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) != k2_struct_0(X0)
            & ( k1_xboole_0 = k2_struct_0(X0)
              | k1_xboole_0 != k2_struct_0(sK1) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
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
              ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(sK0)
              & ( k1_xboole_0 = k2_struct_0(sK0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0)
    & ( k1_xboole_0 = k2_struct_0(sK0)
      | k1_xboole_0 != k2_struct_0(sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f43,f42,f41])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f16,axiom,(
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

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f67,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f73,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f65])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f37])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f47])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_14,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_17,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_373,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_374,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_376,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_374,c_26,c_24])).

cnf(c_415,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) != X1
    | k1_relat_1(X0) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_376])).

cnf(c_416,plain,
    ( ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ v1_relat_1(sK2)
    | u1_struct_0(sK1) = k1_xboole_0
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_441,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK2)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) != X1
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_416])).

cnf(c_442,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
    | ~ v1_relat_1(sK2)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_616,plain,
    ( ~ v1_relat_1(sK2)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_442])).

cnf(c_695,plain,
    ( ~ v1_relat_1(sK2)
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_616])).

cnf(c_771,plain,
    ( ~ v1_relat_1(sK2)
    | sP0_iProver_split
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_695])).

cnf(c_1029,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_771])).

cnf(c_21,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_27,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_267,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_268,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_267])).

cnf(c_28,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_272,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_273,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_1113,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_1029,c_268,c_273])).

cnf(c_777,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1231,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_777])).

cnf(c_770,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_695])).

cnf(c_1030,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_770])).

cnf(c_1098,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1030,c_268,c_273])).

cnf(c_1261,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1098])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_559,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_24])).

cnf(c_560,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_559])).

cnf(c_1224,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_1319,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1224])).

cnf(c_1320,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1319])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1427,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1428,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1427])).

cnf(c_1449,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1113,c_1231,c_1261,c_1320,c_1428])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1460,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1449,c_23])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_7,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_280,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | X1 != X2
    | k3_xboole_0(X3,X2) = X3
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_7])).

cnf(c_281,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k3_xboole_0(k2_relat_1(X0),X1) = k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_299,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k3_xboole_0(k2_relat_1(X0),X2) = k2_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_13,c_281])).

cnf(c_574,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(k2_relat_1(X0),X1) = k2_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_299,c_24])).

cnf(c_575,plain,
    ( ~ v1_relat_1(sK2)
    | k3_xboole_0(k2_relat_1(sK2),X0) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_574])).

cnf(c_1031,plain,
    ( k3_xboole_0(k2_relat_1(sK2),X0) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_575])).

cnf(c_1162,plain,
    ( k3_xboole_0(k2_relat_1(sK2),X0) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1031,c_268,c_273])).

cnf(c_1185,plain,
    ( ~ v1_relat_1(sK2)
    | k3_xboole_0(k2_relat_1(sK2),X0) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1162])).

cnf(c_1433,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
    | k3_xboole_0(k2_relat_1(sK2),X0) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1162,c_1185,c_1231,c_1319,c_1427])).

cnf(c_1434,plain,
    ( k3_xboole_0(k2_relat_1(sK2),X0) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
    inference(renaming,[status(thm)],[c_1433])).

cnf(c_1440,plain,
    ( k3_xboole_0(k2_relat_1(sK2),k2_struct_0(sK1)) = k2_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_1434])).

cnf(c_1032,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_560])).

cnf(c_1122,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1032,c_268,c_273])).

cnf(c_1569,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1460,c_1122])).

cnf(c_1945,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1569,c_1231,c_1320,c_1428])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1040,plain,
    ( k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2416,plain,
    ( k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0)) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1945,c_1040])).

cnf(c_2507,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,k2_struct_0(sK1)) ),
    inference(superposition,[status(thm)],[c_1440,c_2416])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1039,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2287,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1945,c_1039])).

cnf(c_2508,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2507,c_2287])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_589,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_590,plain,
    ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_589])).

cnf(c_1129,plain,
    ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_590,c_268,c_273])).

cnf(c_1381,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(equality_resolution,[status(thm)],[c_1129])).

cnf(c_22,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1060,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_22,c_268,c_273])).

cnf(c_2510,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_1381,c_1060])).

cnf(c_3503,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2508,c_2510])).

cnf(c_3506,plain,
    ( k2_struct_0(sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1460,c_3503])).

cnf(c_3558,plain,
    ( k1_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3506,c_3503])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_356,plain,
    ( v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK0) != k1_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_357,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | u1_struct_0(sK0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_359,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | v1_partfun1(sK2,k1_xboole_0)
    | u1_struct_0(sK0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_357,c_26])).

cnf(c_360,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | u1_struct_0(sK0) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_359])).

cnf(c_396,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ v1_relat_1(X0)
    | u1_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(X0) = X1
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_360])).

cnf(c_397,plain,
    ( ~ v4_relat_1(sK2,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ v1_relat_1(sK2)
    | u1_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_409,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ v1_relat_1(sK2)
    | u1_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_397,c_14])).

cnf(c_598,plain,
    ( ~ v1_relat_1(sK2)
    | u1_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_409])).

cnf(c_699,plain,
    ( ~ v1_relat_1(sK2)
    | u1_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) ),
    inference(equality_resolution_simp,[status(thm)],[c_598])).

cnf(c_1028,plain,
    ( u1_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_699])).

cnf(c_1169,plain,
    ( k2_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1028,c_268,c_273])).

cnf(c_2,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1170,plain,
    ( k2_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k1_xboole_0)
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1169,c_2])).

cnf(c_2910,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k1_xboole_0)
    | k1_relat_1(sK2) = k1_xboole_0
    | k2_struct_0(sK0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1170,c_1231,c_1320,c_1428])).

cnf(c_2911,plain,
    ( k2_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k1_xboole_0) ),
    inference(renaming,[status(thm)],[c_2910])).

cnf(c_3565,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))) != k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3506,c_2911])).

cnf(c_3645,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))) != k1_zfmisc_1(k1_xboole_0) ),
    inference(equality_resolution_simp,[status(thm)],[c_3565])).

cnf(c_3648,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3645,c_2])).

cnf(c_3649,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3648])).

cnf(c_3652,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3558,c_3649])).

cnf(c_3653,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3652])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:50:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.42/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.42/0.98  
% 2.42/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.42/0.98  
% 2.42/0.98  ------  iProver source info
% 2.42/0.98  
% 2.42/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.42/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.42/0.98  git: non_committed_changes: false
% 2.42/0.98  git: last_make_outside_of_git: false
% 2.42/0.98  
% 2.42/0.98  ------ 
% 2.42/0.98  
% 2.42/0.98  ------ Input Options
% 2.42/0.98  
% 2.42/0.98  --out_options                           all
% 2.42/0.98  --tptp_safe_out                         true
% 2.42/0.98  --problem_path                          ""
% 2.42/0.98  --include_path                          ""
% 2.42/0.98  --clausifier                            res/vclausify_rel
% 2.42/0.98  --clausifier_options                    --mode clausify
% 2.42/0.98  --stdin                                 false
% 2.42/0.98  --stats_out                             all
% 2.42/0.98  
% 2.42/0.98  ------ General Options
% 2.42/0.98  
% 2.42/0.98  --fof                                   false
% 2.42/0.98  --time_out_real                         305.
% 2.42/0.98  --time_out_virtual                      -1.
% 2.42/0.98  --symbol_type_check                     false
% 2.42/0.98  --clausify_out                          false
% 2.42/0.98  --sig_cnt_out                           false
% 2.42/0.98  --trig_cnt_out                          false
% 2.42/0.98  --trig_cnt_out_tolerance                1.
% 2.42/0.98  --trig_cnt_out_sk_spl                   false
% 2.42/0.98  --abstr_cl_out                          false
% 2.42/0.98  
% 2.42/0.98  ------ Global Options
% 2.42/0.98  
% 2.42/0.98  --schedule                              default
% 2.42/0.98  --add_important_lit                     false
% 2.42/0.98  --prop_solver_per_cl                    1000
% 2.42/0.98  --min_unsat_core                        false
% 2.42/0.98  --soft_assumptions                      false
% 2.42/0.98  --soft_lemma_size                       3
% 2.42/0.98  --prop_impl_unit_size                   0
% 2.42/0.98  --prop_impl_unit                        []
% 2.42/0.98  --share_sel_clauses                     true
% 2.42/0.98  --reset_solvers                         false
% 2.42/0.98  --bc_imp_inh                            [conj_cone]
% 2.42/0.98  --conj_cone_tolerance                   3.
% 2.42/0.98  --extra_neg_conj                        none
% 2.42/0.98  --large_theory_mode                     true
% 2.42/0.98  --prolific_symb_bound                   200
% 2.42/0.98  --lt_threshold                          2000
% 2.42/0.98  --clause_weak_htbl                      true
% 2.42/0.98  --gc_record_bc_elim                     false
% 2.42/0.98  
% 2.42/0.98  ------ Preprocessing Options
% 2.42/0.98  
% 2.42/0.98  --preprocessing_flag                    true
% 2.42/0.98  --time_out_prep_mult                    0.1
% 2.42/0.98  --splitting_mode                        input
% 2.42/0.98  --splitting_grd                         true
% 2.42/0.98  --splitting_cvd                         false
% 2.42/0.98  --splitting_cvd_svl                     false
% 2.42/0.98  --splitting_nvd                         32
% 2.42/0.98  --sub_typing                            true
% 2.42/0.98  --prep_gs_sim                           true
% 2.42/0.98  --prep_unflatten                        true
% 2.42/0.98  --prep_res_sim                          true
% 2.42/0.98  --prep_upred                            true
% 2.42/0.98  --prep_sem_filter                       exhaustive
% 2.42/0.98  --prep_sem_filter_out                   false
% 2.42/0.98  --pred_elim                             true
% 2.42/0.98  --res_sim_input                         true
% 2.42/0.98  --eq_ax_congr_red                       true
% 2.42/0.98  --pure_diseq_elim                       true
% 2.42/0.98  --brand_transform                       false
% 2.42/0.98  --non_eq_to_eq                          false
% 2.42/0.98  --prep_def_merge                        true
% 2.42/0.98  --prep_def_merge_prop_impl              false
% 2.42/0.98  --prep_def_merge_mbd                    true
% 2.42/0.98  --prep_def_merge_tr_red                 false
% 2.42/0.98  --prep_def_merge_tr_cl                  false
% 2.42/0.98  --smt_preprocessing                     true
% 2.42/0.98  --smt_ac_axioms                         fast
% 2.42/0.98  --preprocessed_out                      false
% 2.42/0.98  --preprocessed_stats                    false
% 2.42/0.98  
% 2.42/0.98  ------ Abstraction refinement Options
% 2.42/0.98  
% 2.42/0.98  --abstr_ref                             []
% 2.42/0.98  --abstr_ref_prep                        false
% 2.42/0.98  --abstr_ref_until_sat                   false
% 2.42/0.98  --abstr_ref_sig_restrict                funpre
% 2.42/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.42/0.98  --abstr_ref_under                       []
% 2.42/0.98  
% 2.42/0.98  ------ SAT Options
% 2.42/0.98  
% 2.42/0.98  --sat_mode                              false
% 2.42/0.98  --sat_fm_restart_options                ""
% 2.42/0.98  --sat_gr_def                            false
% 2.42/0.98  --sat_epr_types                         true
% 2.42/0.98  --sat_non_cyclic_types                  false
% 2.42/0.98  --sat_finite_models                     false
% 2.42/0.98  --sat_fm_lemmas                         false
% 2.42/0.98  --sat_fm_prep                           false
% 2.42/0.98  --sat_fm_uc_incr                        true
% 2.42/0.98  --sat_out_model                         small
% 2.42/0.98  --sat_out_clauses                       false
% 2.42/0.98  
% 2.42/0.98  ------ QBF Options
% 2.42/0.98  
% 2.42/0.98  --qbf_mode                              false
% 2.42/0.98  --qbf_elim_univ                         false
% 2.42/0.98  --qbf_dom_inst                          none
% 2.42/0.98  --qbf_dom_pre_inst                      false
% 2.42/0.98  --qbf_sk_in                             false
% 2.42/0.98  --qbf_pred_elim                         true
% 2.42/0.98  --qbf_split                             512
% 2.42/0.98  
% 2.42/0.98  ------ BMC1 Options
% 2.42/0.98  
% 2.42/0.98  --bmc1_incremental                      false
% 2.42/0.98  --bmc1_axioms                           reachable_all
% 2.42/0.98  --bmc1_min_bound                        0
% 2.42/0.98  --bmc1_max_bound                        -1
% 2.42/0.98  --bmc1_max_bound_default                -1
% 2.42/0.98  --bmc1_symbol_reachability              true
% 2.42/0.98  --bmc1_property_lemmas                  false
% 2.42/0.98  --bmc1_k_induction                      false
% 2.42/0.98  --bmc1_non_equiv_states                 false
% 2.42/0.98  --bmc1_deadlock                         false
% 2.42/0.98  --bmc1_ucm                              false
% 2.42/0.98  --bmc1_add_unsat_core                   none
% 2.42/0.98  --bmc1_unsat_core_children              false
% 2.42/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.42/0.98  --bmc1_out_stat                         full
% 2.42/0.98  --bmc1_ground_init                      false
% 2.42/0.98  --bmc1_pre_inst_next_state              false
% 2.42/0.98  --bmc1_pre_inst_state                   false
% 2.42/0.98  --bmc1_pre_inst_reach_state             false
% 2.42/0.98  --bmc1_out_unsat_core                   false
% 2.42/0.98  --bmc1_aig_witness_out                  false
% 2.42/0.98  --bmc1_verbose                          false
% 2.42/0.98  --bmc1_dump_clauses_tptp                false
% 2.42/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.42/0.98  --bmc1_dump_file                        -
% 2.42/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.42/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.42/0.98  --bmc1_ucm_extend_mode                  1
% 2.42/0.98  --bmc1_ucm_init_mode                    2
% 2.42/0.98  --bmc1_ucm_cone_mode                    none
% 2.42/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.42/0.98  --bmc1_ucm_relax_model                  4
% 2.42/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.42/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.42/0.98  --bmc1_ucm_layered_model                none
% 2.42/0.98  --bmc1_ucm_max_lemma_size               10
% 2.42/0.98  
% 2.42/0.98  ------ AIG Options
% 2.42/0.98  
% 2.42/0.98  --aig_mode                              false
% 2.42/0.98  
% 2.42/0.98  ------ Instantiation Options
% 2.42/0.98  
% 2.42/0.98  --instantiation_flag                    true
% 2.42/0.98  --inst_sos_flag                         false
% 2.42/0.98  --inst_sos_phase                        true
% 2.42/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.42/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.42/0.98  --inst_lit_sel_side                     num_symb
% 2.42/0.98  --inst_solver_per_active                1400
% 2.42/0.98  --inst_solver_calls_frac                1.
% 2.42/0.98  --inst_passive_queue_type               priority_queues
% 2.42/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.42/0.98  --inst_passive_queues_freq              [25;2]
% 2.42/0.98  --inst_dismatching                      true
% 2.42/0.98  --inst_eager_unprocessed_to_passive     true
% 2.42/0.98  --inst_prop_sim_given                   true
% 2.42/0.98  --inst_prop_sim_new                     false
% 2.42/0.98  --inst_subs_new                         false
% 2.42/0.98  --inst_eq_res_simp                      false
% 2.42/0.98  --inst_subs_given                       false
% 2.42/0.98  --inst_orphan_elimination               true
% 2.42/0.98  --inst_learning_loop_flag               true
% 2.42/0.98  --inst_learning_start                   3000
% 2.42/0.98  --inst_learning_factor                  2
% 2.42/0.98  --inst_start_prop_sim_after_learn       3
% 2.42/0.98  --inst_sel_renew                        solver
% 2.42/0.98  --inst_lit_activity_flag                true
% 2.42/0.98  --inst_restr_to_given                   false
% 2.42/0.98  --inst_activity_threshold               500
% 2.42/0.98  --inst_out_proof                        true
% 2.42/0.98  
% 2.42/0.98  ------ Resolution Options
% 2.42/0.98  
% 2.42/0.98  --resolution_flag                       true
% 2.42/0.98  --res_lit_sel                           adaptive
% 2.42/0.98  --res_lit_sel_side                      none
% 2.42/0.98  --res_ordering                          kbo
% 2.42/0.98  --res_to_prop_solver                    active
% 2.42/0.98  --res_prop_simpl_new                    false
% 2.42/0.98  --res_prop_simpl_given                  true
% 2.42/0.98  --res_passive_queue_type                priority_queues
% 2.42/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.42/0.98  --res_passive_queues_freq               [15;5]
% 2.42/0.98  --res_forward_subs                      full
% 2.42/0.98  --res_backward_subs                     full
% 2.42/0.98  --res_forward_subs_resolution           true
% 2.42/0.98  --res_backward_subs_resolution          true
% 2.42/0.98  --res_orphan_elimination                true
% 2.42/0.98  --res_time_limit                        2.
% 2.42/0.98  --res_out_proof                         true
% 2.42/0.98  
% 2.42/0.98  ------ Superposition Options
% 2.42/0.98  
% 2.42/0.98  --superposition_flag                    true
% 2.42/0.98  --sup_passive_queue_type                priority_queues
% 2.42/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.42/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.42/0.98  --demod_completeness_check              fast
% 2.42/0.98  --demod_use_ground                      true
% 2.42/0.98  --sup_to_prop_solver                    passive
% 2.42/0.98  --sup_prop_simpl_new                    true
% 2.42/0.98  --sup_prop_simpl_given                  true
% 2.42/0.98  --sup_fun_splitting                     false
% 2.42/0.98  --sup_smt_interval                      50000
% 2.42/0.98  
% 2.42/0.98  ------ Superposition Simplification Setup
% 2.42/0.98  
% 2.42/0.98  --sup_indices_passive                   []
% 2.42/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.42/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.42/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.42/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.42/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.42/0.98  --sup_full_bw                           [BwDemod]
% 2.42/0.98  --sup_immed_triv                        [TrivRules]
% 2.42/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.42/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.42/0.98  --sup_immed_bw_main                     []
% 2.42/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.42/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.42/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.42/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.42/0.98  
% 2.42/0.98  ------ Combination Options
% 2.42/0.98  
% 2.42/0.98  --comb_res_mult                         3
% 2.42/0.98  --comb_sup_mult                         2
% 2.42/0.98  --comb_inst_mult                        10
% 2.42/0.98  
% 2.42/0.98  ------ Debug Options
% 2.42/0.98  
% 2.42/0.98  --dbg_backtrace                         false
% 2.42/0.98  --dbg_dump_prop_clauses                 false
% 2.42/0.98  --dbg_dump_prop_clauses_file            -
% 2.42/0.98  --dbg_out_stat                          false
% 2.42/0.98  ------ Parsing...
% 2.42/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.42/0.98  
% 2.42/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.42/0.98  
% 2.42/0.98  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.42/0.98  
% 2.42/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.42/0.98  ------ Proving...
% 2.42/0.98  ------ Problem Properties 
% 2.42/0.98  
% 2.42/0.98  
% 2.42/0.98  clauses                                 27
% 2.42/0.98  conjectures                             2
% 2.42/0.98  EPR                                     0
% 2.42/0.98  Horn                                    23
% 2.42/0.98  unary                                   8
% 2.42/0.98  binary                                  10
% 2.42/0.98  lits                                    61
% 2.42/0.98  lits eq                                 42
% 2.42/0.98  fd_pure                                 0
% 2.42/0.98  fd_pseudo                               0
% 2.42/0.98  fd_cond                                 1
% 2.42/0.98  fd_pseudo_cond                          0
% 2.42/0.98  AC symbols                              0
% 2.42/0.98  
% 2.42/0.98  ------ Schedule dynamic 5 is on 
% 2.42/0.98  
% 2.42/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.42/0.98  
% 2.42/0.98  
% 2.42/0.98  ------ 
% 2.42/0.98  Current options:
% 2.42/0.98  ------ 
% 2.42/0.98  
% 2.42/0.98  ------ Input Options
% 2.42/0.98  
% 2.42/0.98  --out_options                           all
% 2.42/0.98  --tptp_safe_out                         true
% 2.42/0.98  --problem_path                          ""
% 2.42/0.98  --include_path                          ""
% 2.42/0.98  --clausifier                            res/vclausify_rel
% 2.42/0.98  --clausifier_options                    --mode clausify
% 2.42/0.98  --stdin                                 false
% 2.42/0.98  --stats_out                             all
% 2.42/0.98  
% 2.42/0.98  ------ General Options
% 2.42/0.98  
% 2.42/0.98  --fof                                   false
% 2.42/0.98  --time_out_real                         305.
% 2.42/0.98  --time_out_virtual                      -1.
% 2.42/0.98  --symbol_type_check                     false
% 2.42/0.98  --clausify_out                          false
% 2.42/0.98  --sig_cnt_out                           false
% 2.42/0.98  --trig_cnt_out                          false
% 2.42/0.98  --trig_cnt_out_tolerance                1.
% 2.42/0.98  --trig_cnt_out_sk_spl                   false
% 2.42/0.98  --abstr_cl_out                          false
% 2.42/0.98  
% 2.42/0.98  ------ Global Options
% 2.42/0.98  
% 2.42/0.98  --schedule                              default
% 2.42/0.98  --add_important_lit                     false
% 2.42/0.98  --prop_solver_per_cl                    1000
% 2.42/0.98  --min_unsat_core                        false
% 2.42/0.98  --soft_assumptions                      false
% 2.42/0.98  --soft_lemma_size                       3
% 2.42/0.98  --prop_impl_unit_size                   0
% 2.42/0.98  --prop_impl_unit                        []
% 2.42/0.98  --share_sel_clauses                     true
% 2.42/0.98  --reset_solvers                         false
% 2.42/0.98  --bc_imp_inh                            [conj_cone]
% 2.42/0.98  --conj_cone_tolerance                   3.
% 2.42/0.98  --extra_neg_conj                        none
% 2.42/0.98  --large_theory_mode                     true
% 2.42/0.98  --prolific_symb_bound                   200
% 2.42/0.98  --lt_threshold                          2000
% 2.42/0.98  --clause_weak_htbl                      true
% 2.42/0.98  --gc_record_bc_elim                     false
% 2.42/0.98  
% 2.42/0.98  ------ Preprocessing Options
% 2.42/0.98  
% 2.42/0.98  --preprocessing_flag                    true
% 2.42/0.98  --time_out_prep_mult                    0.1
% 2.42/0.98  --splitting_mode                        input
% 2.42/0.98  --splitting_grd                         true
% 2.42/0.98  --splitting_cvd                         false
% 2.42/0.98  --splitting_cvd_svl                     false
% 2.42/0.98  --splitting_nvd                         32
% 2.42/0.98  --sub_typing                            true
% 2.42/0.98  --prep_gs_sim                           true
% 2.42/0.98  --prep_unflatten                        true
% 2.42/0.98  --prep_res_sim                          true
% 2.42/0.98  --prep_upred                            true
% 2.42/0.98  --prep_sem_filter                       exhaustive
% 2.42/0.98  --prep_sem_filter_out                   false
% 2.42/0.98  --pred_elim                             true
% 2.42/0.98  --res_sim_input                         true
% 2.42/0.98  --eq_ax_congr_red                       true
% 2.42/0.98  --pure_diseq_elim                       true
% 2.42/0.98  --brand_transform                       false
% 2.42/0.98  --non_eq_to_eq                          false
% 2.42/0.98  --prep_def_merge                        true
% 2.42/0.98  --prep_def_merge_prop_impl              false
% 2.42/0.98  --prep_def_merge_mbd                    true
% 2.42/0.98  --prep_def_merge_tr_red                 false
% 2.42/0.98  --prep_def_merge_tr_cl                  false
% 2.42/0.98  --smt_preprocessing                     true
% 2.42/0.98  --smt_ac_axioms                         fast
% 2.42/0.98  --preprocessed_out                      false
% 2.42/0.98  --preprocessed_stats                    false
% 2.42/0.98  
% 2.42/0.98  ------ Abstraction refinement Options
% 2.42/0.98  
% 2.42/0.98  --abstr_ref                             []
% 2.42/0.98  --abstr_ref_prep                        false
% 2.42/0.98  --abstr_ref_until_sat                   false
% 2.42/0.98  --abstr_ref_sig_restrict                funpre
% 2.42/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.42/0.98  --abstr_ref_under                       []
% 2.42/0.98  
% 2.42/0.98  ------ SAT Options
% 2.42/0.98  
% 2.42/0.98  --sat_mode                              false
% 2.42/0.98  --sat_fm_restart_options                ""
% 2.42/0.98  --sat_gr_def                            false
% 2.42/0.98  --sat_epr_types                         true
% 2.42/0.98  --sat_non_cyclic_types                  false
% 2.42/0.98  --sat_finite_models                     false
% 2.42/0.98  --sat_fm_lemmas                         false
% 2.42/0.98  --sat_fm_prep                           false
% 2.42/0.98  --sat_fm_uc_incr                        true
% 2.42/0.98  --sat_out_model                         small
% 2.42/0.98  --sat_out_clauses                       false
% 2.42/0.98  
% 2.42/0.98  ------ QBF Options
% 2.42/0.98  
% 2.42/0.98  --qbf_mode                              false
% 2.42/0.98  --qbf_elim_univ                         false
% 2.42/0.98  --qbf_dom_inst                          none
% 2.42/0.98  --qbf_dom_pre_inst                      false
% 2.42/0.98  --qbf_sk_in                             false
% 2.42/0.98  --qbf_pred_elim                         true
% 2.42/0.98  --qbf_split                             512
% 2.42/0.98  
% 2.42/0.98  ------ BMC1 Options
% 2.42/0.98  
% 2.42/0.98  --bmc1_incremental                      false
% 2.42/0.98  --bmc1_axioms                           reachable_all
% 2.42/0.98  --bmc1_min_bound                        0
% 2.42/0.98  --bmc1_max_bound                        -1
% 2.42/0.98  --bmc1_max_bound_default                -1
% 2.42/0.98  --bmc1_symbol_reachability              true
% 2.42/0.98  --bmc1_property_lemmas                  false
% 2.42/0.98  --bmc1_k_induction                      false
% 2.42/0.98  --bmc1_non_equiv_states                 false
% 2.42/0.98  --bmc1_deadlock                         false
% 2.42/0.98  --bmc1_ucm                              false
% 2.42/0.98  --bmc1_add_unsat_core                   none
% 2.42/0.98  --bmc1_unsat_core_children              false
% 2.42/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.42/0.98  --bmc1_out_stat                         full
% 2.42/0.98  --bmc1_ground_init                      false
% 2.42/0.98  --bmc1_pre_inst_next_state              false
% 2.42/0.98  --bmc1_pre_inst_state                   false
% 2.42/0.98  --bmc1_pre_inst_reach_state             false
% 2.42/0.98  --bmc1_out_unsat_core                   false
% 2.42/0.98  --bmc1_aig_witness_out                  false
% 2.42/0.98  --bmc1_verbose                          false
% 2.42/0.98  --bmc1_dump_clauses_tptp                false
% 2.42/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.42/0.98  --bmc1_dump_file                        -
% 2.42/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.42/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.42/0.98  --bmc1_ucm_extend_mode                  1
% 2.42/0.98  --bmc1_ucm_init_mode                    2
% 2.42/0.98  --bmc1_ucm_cone_mode                    none
% 2.42/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.42/0.98  --bmc1_ucm_relax_model                  4
% 2.42/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.42/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.42/0.98  --bmc1_ucm_layered_model                none
% 2.42/0.98  --bmc1_ucm_max_lemma_size               10
% 2.42/0.98  
% 2.42/0.98  ------ AIG Options
% 2.42/0.98  
% 2.42/0.98  --aig_mode                              false
% 2.42/0.98  
% 2.42/0.98  ------ Instantiation Options
% 2.42/0.98  
% 2.42/0.98  --instantiation_flag                    true
% 2.42/0.98  --inst_sos_flag                         false
% 2.42/0.98  --inst_sos_phase                        true
% 2.42/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.42/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.42/0.98  --inst_lit_sel_side                     none
% 2.42/0.98  --inst_solver_per_active                1400
% 2.42/0.98  --inst_solver_calls_frac                1.
% 2.42/0.98  --inst_passive_queue_type               priority_queues
% 2.42/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.42/0.98  --inst_passive_queues_freq              [25;2]
% 2.42/0.98  --inst_dismatching                      true
% 2.42/0.98  --inst_eager_unprocessed_to_passive     true
% 2.42/0.98  --inst_prop_sim_given                   true
% 2.42/0.98  --inst_prop_sim_new                     false
% 2.42/0.98  --inst_subs_new                         false
% 2.42/0.98  --inst_eq_res_simp                      false
% 2.42/0.98  --inst_subs_given                       false
% 2.42/0.98  --inst_orphan_elimination               true
% 2.42/0.98  --inst_learning_loop_flag               true
% 2.42/0.98  --inst_learning_start                   3000
% 2.42/0.98  --inst_learning_factor                  2
% 2.42/0.98  --inst_start_prop_sim_after_learn       3
% 2.42/0.98  --inst_sel_renew                        solver
% 2.42/0.98  --inst_lit_activity_flag                true
% 2.42/0.98  --inst_restr_to_given                   false
% 2.42/0.98  --inst_activity_threshold               500
% 2.42/0.98  --inst_out_proof                        true
% 2.42/0.98  
% 2.42/0.98  ------ Resolution Options
% 2.42/0.98  
% 2.42/0.98  --resolution_flag                       false
% 2.42/0.98  --res_lit_sel                           adaptive
% 2.42/0.98  --res_lit_sel_side                      none
% 2.42/0.98  --res_ordering                          kbo
% 2.42/0.98  --res_to_prop_solver                    active
% 2.42/0.98  --res_prop_simpl_new                    false
% 2.42/0.98  --res_prop_simpl_given                  true
% 2.42/0.98  --res_passive_queue_type                priority_queues
% 2.42/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.42/0.98  --res_passive_queues_freq               [15;5]
% 2.42/0.98  --res_forward_subs                      full
% 2.42/0.98  --res_backward_subs                     full
% 2.42/0.98  --res_forward_subs_resolution           true
% 2.42/0.98  --res_backward_subs_resolution          true
% 2.42/0.98  --res_orphan_elimination                true
% 2.42/0.98  --res_time_limit                        2.
% 2.42/0.98  --res_out_proof                         true
% 2.42/0.98  
% 2.42/0.98  ------ Superposition Options
% 2.42/0.98  
% 2.42/0.98  --superposition_flag                    true
% 2.42/0.98  --sup_passive_queue_type                priority_queues
% 2.42/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.42/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.42/0.98  --demod_completeness_check              fast
% 2.42/0.98  --demod_use_ground                      true
% 2.42/0.98  --sup_to_prop_solver                    passive
% 2.42/0.98  --sup_prop_simpl_new                    true
% 2.42/0.98  --sup_prop_simpl_given                  true
% 2.42/0.98  --sup_fun_splitting                     false
% 2.42/0.98  --sup_smt_interval                      50000
% 2.42/0.98  
% 2.42/0.98  ------ Superposition Simplification Setup
% 2.42/0.98  
% 2.42/0.98  --sup_indices_passive                   []
% 2.42/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.42/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.42/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.42/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.42/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.42/0.98  --sup_full_bw                           [BwDemod]
% 2.42/0.98  --sup_immed_triv                        [TrivRules]
% 2.42/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.42/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.42/0.98  --sup_immed_bw_main                     []
% 2.42/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.42/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.42/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.42/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.42/0.98  
% 2.42/0.98  ------ Combination Options
% 2.42/0.98  
% 2.42/0.98  --comb_res_mult                         3
% 2.42/0.98  --comb_sup_mult                         2
% 2.42/0.98  --comb_inst_mult                        10
% 2.42/0.98  
% 2.42/0.98  ------ Debug Options
% 2.42/0.98  
% 2.42/0.98  --dbg_backtrace                         false
% 2.42/0.98  --dbg_dump_prop_clauses                 false
% 2.42/0.98  --dbg_dump_prop_clauses_file            -
% 2.42/0.98  --dbg_out_stat                          false
% 2.42/0.98  
% 2.42/0.98  
% 2.42/0.98  
% 2.42/0.98  
% 2.42/0.98  ------ Proving...
% 2.42/0.98  
% 2.42/0.98  
% 2.42/0.98  % SZS status Theorem for theBenchmark.p
% 2.42/0.98  
% 2.42/0.98   Resolution empty clause
% 2.42/0.98  
% 2.42/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.42/0.98  
% 2.42/0.98  fof(f19,conjecture,(
% 2.42/0.98    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 2.42/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.42/0.98  
% 2.42/0.98  fof(f20,negated_conjecture,(
% 2.42/0.98    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 2.42/0.98    inference(negated_conjecture,[],[f19])).
% 2.42/0.98  
% 2.42/0.98  fof(f35,plain,(
% 2.42/0.98    ? [X0] : (? [X1] : (? [X2] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 2.42/0.98    inference(ennf_transformation,[],[f20])).
% 2.42/0.98  
% 2.42/0.98  fof(f36,plain,(
% 2.42/0.98    ? [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 2.42/0.98    inference(flattening,[],[f35])).
% 2.42/0.98  
% 2.42/0.98  fof(f43,plain,(
% 2.42/0.98    ( ! [X0,X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.42/0.98    introduced(choice_axiom,[])).
% 2.42/0.98  
% 2.42/0.98  fof(f42,plain,(
% 2.42/0.98    ( ! [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))) )),
% 2.42/0.98    introduced(choice_axiom,[])).
% 2.42/0.98  
% 2.42/0.98  fof(f41,plain,(
% 2.42/0.98    ? [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(sK0) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 2.42/0.98    introduced(choice_axiom,[])).
% 2.42/0.98  
% 2.42/0.98  fof(f44,plain,(
% 2.42/0.98    ((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.42/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f43,f42,f41])).
% 2.42/0.98  
% 2.42/0.98  fof(f72,plain,(
% 2.42/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.42/0.98    inference(cnf_transformation,[],[f44])).
% 2.42/0.98  
% 2.42/0.98  fof(f12,axiom,(
% 2.42/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.42/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.42/0.98  
% 2.42/0.98  fof(f27,plain,(
% 2.42/0.98    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.42/0.98    inference(ennf_transformation,[],[f12])).
% 2.42/0.98  
% 2.42/0.98  fof(f58,plain,(
% 2.42/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.42/0.98    inference(cnf_transformation,[],[f27])).
% 2.42/0.98  
% 2.42/0.98  fof(f14,axiom,(
% 2.42/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.42/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.42/0.98  
% 2.42/0.98  fof(f29,plain,(
% 2.42/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.42/0.98    inference(ennf_transformation,[],[f14])).
% 2.42/0.98  
% 2.42/0.98  fof(f30,plain,(
% 2.42/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.42/0.98    inference(flattening,[],[f29])).
% 2.42/0.98  
% 2.42/0.98  fof(f40,plain,(
% 2.42/0.98    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.42/0.98    inference(nnf_transformation,[],[f30])).
% 2.42/0.98  
% 2.42/0.98  fof(f61,plain,(
% 2.42/0.98    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.42/0.98    inference(cnf_transformation,[],[f40])).
% 2.42/0.98  
% 2.42/0.98  fof(f16,axiom,(
% 2.42/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.42/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.42/0.98  
% 2.42/0.98  fof(f31,plain,(
% 2.42/0.98    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.42/0.98    inference(ennf_transformation,[],[f16])).
% 2.42/0.98  
% 2.42/0.98  fof(f32,plain,(
% 2.42/0.98    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.42/0.98    inference(flattening,[],[f31])).
% 2.42/0.98  
% 2.42/0.98  fof(f64,plain,(
% 2.42/0.98    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.42/0.98    inference(cnf_transformation,[],[f32])).
% 2.42/0.98  
% 2.42/0.99  fof(f71,plain,(
% 2.42/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.42/0.99    inference(cnf_transformation,[],[f44])).
% 2.42/0.99  
% 2.42/0.99  fof(f70,plain,(
% 2.42/0.99    v1_funct_1(sK2)),
% 2.42/0.99    inference(cnf_transformation,[],[f44])).
% 2.42/0.99  
% 2.42/0.99  fof(f18,axiom,(
% 2.42/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.42/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.42/0.99  
% 2.42/0.99  fof(f34,plain,(
% 2.42/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.42/0.99    inference(ennf_transformation,[],[f18])).
% 2.42/0.99  
% 2.42/0.99  fof(f67,plain,(
% 2.42/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.42/0.99    inference(cnf_transformation,[],[f34])).
% 2.42/0.99  
% 2.42/0.99  fof(f69,plain,(
% 2.42/0.99    l1_struct_0(sK1)),
% 2.42/0.99    inference(cnf_transformation,[],[f44])).
% 2.42/0.99  
% 2.42/0.99  fof(f68,plain,(
% 2.42/0.99    l1_struct_0(sK0)),
% 2.42/0.99    inference(cnf_transformation,[],[f44])).
% 2.42/0.99  
% 2.42/0.99  fof(f5,axiom,(
% 2.42/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.42/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.42/0.99  
% 2.42/0.99  fof(f23,plain,(
% 2.42/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.42/0.99    inference(ennf_transformation,[],[f5])).
% 2.42/0.99  
% 2.42/0.99  fof(f50,plain,(
% 2.42/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.42/0.99    inference(cnf_transformation,[],[f23])).
% 2.42/0.99  
% 2.42/0.99  fof(f7,axiom,(
% 2.42/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.42/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.42/0.99  
% 2.42/0.99  fof(f53,plain,(
% 2.42/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.42/0.99    inference(cnf_transformation,[],[f7])).
% 2.42/0.99  
% 2.42/0.99  fof(f73,plain,(
% 2.42/0.99    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)),
% 2.42/0.99    inference(cnf_transformation,[],[f44])).
% 2.42/0.99  
% 2.42/0.99  fof(f59,plain,(
% 2.42/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.42/0.99    inference(cnf_transformation,[],[f27])).
% 2.42/0.99  
% 2.42/0.99  fof(f1,axiom,(
% 2.42/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.42/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.42/0.99  
% 2.42/0.99  fof(f22,plain,(
% 2.42/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.42/0.99    inference(ennf_transformation,[],[f1])).
% 2.42/0.99  
% 2.42/0.99  fof(f45,plain,(
% 2.42/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.42/0.99    inference(cnf_transformation,[],[f22])).
% 2.42/0.99  
% 2.42/0.99  fof(f6,axiom,(
% 2.42/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.42/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.42/0.99  
% 2.42/0.99  fof(f24,plain,(
% 2.42/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.42/0.99    inference(ennf_transformation,[],[f6])).
% 2.42/0.99  
% 2.42/0.99  fof(f39,plain,(
% 2.42/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.42/0.99    inference(nnf_transformation,[],[f24])).
% 2.42/0.99  
% 2.42/0.99  fof(f51,plain,(
% 2.42/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.42/0.99    inference(cnf_transformation,[],[f39])).
% 2.42/0.99  
% 2.42/0.99  fof(f8,axiom,(
% 2.42/0.99    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 2.42/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.42/0.99  
% 2.42/0.99  fof(f25,plain,(
% 2.42/0.99    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.42/0.99    inference(ennf_transformation,[],[f8])).
% 2.42/0.99  
% 2.42/0.99  fof(f54,plain,(
% 2.42/0.99    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 2.42/0.99    inference(cnf_transformation,[],[f25])).
% 2.42/0.99  
% 2.42/0.99  fof(f9,axiom,(
% 2.42/0.99    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.42/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.42/0.99  
% 2.42/0.99  fof(f26,plain,(
% 2.42/0.99    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.42/0.99    inference(ennf_transformation,[],[f9])).
% 2.42/0.99  
% 2.42/0.99  fof(f55,plain,(
% 2.42/0.99    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.42/0.99    inference(cnf_transformation,[],[f26])).
% 2.42/0.99  
% 2.42/0.99  fof(f13,axiom,(
% 2.42/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.42/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.42/0.99  
% 2.42/0.99  fof(f28,plain,(
% 2.42/0.99    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.42/0.99    inference(ennf_transformation,[],[f13])).
% 2.42/0.99  
% 2.42/0.99  fof(f60,plain,(
% 2.42/0.99    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.42/0.99    inference(cnf_transformation,[],[f28])).
% 2.42/0.99  
% 2.42/0.99  fof(f74,plain,(
% 2.42/0.99    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0)),
% 2.42/0.99    inference(cnf_transformation,[],[f44])).
% 2.42/0.99  
% 2.42/0.99  fof(f65,plain,(
% 2.42/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.42/0.99    inference(cnf_transformation,[],[f32])).
% 2.42/0.99  
% 2.42/0.99  fof(f79,plain,(
% 2.42/0.99    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 2.42/0.99    inference(equality_resolution,[],[f65])).
% 2.42/0.99  
% 2.42/0.99  fof(f2,axiom,(
% 2.42/0.99    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.42/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.42/0.99  
% 2.42/0.99  fof(f37,plain,(
% 2.42/0.99    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.42/0.99    inference(nnf_transformation,[],[f2])).
% 2.42/0.99  
% 2.42/0.99  fof(f38,plain,(
% 2.42/0.99    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.42/0.99    inference(flattening,[],[f37])).
% 2.42/0.99  
% 2.42/0.99  fof(f47,plain,(
% 2.42/0.99    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 2.42/0.99    inference(cnf_transformation,[],[f38])).
% 2.42/0.99  
% 2.42/0.99  fof(f77,plain,(
% 2.42/0.99    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 2.42/0.99    inference(equality_resolution,[],[f47])).
% 2.42/0.99  
% 2.42/0.99  cnf(c_24,negated_conjecture,
% 2.42/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.42/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_14,plain,
% 2.42/0.99      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.42/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_17,plain,
% 2.42/0.99      ( ~ v1_partfun1(X0,X1)
% 2.42/0.99      | ~ v4_relat_1(X0,X1)
% 2.42/0.99      | ~ v1_relat_1(X0)
% 2.42/0.99      | k1_relat_1(X0) = X1 ),
% 2.42/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_19,plain,
% 2.42/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.42/0.99      | v1_partfun1(X0,X1)
% 2.42/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.42/0.99      | ~ v1_funct_1(X0)
% 2.42/0.99      | k1_xboole_0 = X2 ),
% 2.42/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_25,negated_conjecture,
% 2.42/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.42/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_373,plain,
% 2.42/0.99      ( v1_partfun1(X0,X1)
% 2.42/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.42/0.99      | ~ v1_funct_1(X0)
% 2.42/0.99      | u1_struct_0(sK1) != X2
% 2.42/0.99      | u1_struct_0(sK0) != X1
% 2.42/0.99      | sK2 != X0
% 2.42/0.99      | k1_xboole_0 = X2 ),
% 2.42/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_374,plain,
% 2.42/0.99      ( v1_partfun1(sK2,u1_struct_0(sK0))
% 2.42/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.42/0.99      | ~ v1_funct_1(sK2)
% 2.42/0.99      | k1_xboole_0 = u1_struct_0(sK1) ),
% 2.42/0.99      inference(unflattening,[status(thm)],[c_373]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_26,negated_conjecture,
% 2.42/0.99      ( v1_funct_1(sK2) ),
% 2.42/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_376,plain,
% 2.42/0.99      ( v1_partfun1(sK2,u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK1) ),
% 2.42/0.99      inference(global_propositional_subsumption,
% 2.42/0.99                [status(thm)],
% 2.42/0.99                [c_374,c_26,c_24]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_415,plain,
% 2.42/0.99      ( ~ v4_relat_1(X0,X1)
% 2.42/0.99      | ~ v1_relat_1(X0)
% 2.42/0.99      | u1_struct_0(sK1) = k1_xboole_0
% 2.42/0.99      | u1_struct_0(sK0) != X1
% 2.42/0.99      | k1_relat_1(X0) = X1
% 2.42/0.99      | sK2 != X0 ),
% 2.42/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_376]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_416,plain,
% 2.42/0.99      ( ~ v4_relat_1(sK2,u1_struct_0(sK0))
% 2.42/0.99      | ~ v1_relat_1(sK2)
% 2.42/0.99      | u1_struct_0(sK1) = k1_xboole_0
% 2.42/0.99      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 2.42/0.99      inference(unflattening,[status(thm)],[c_415]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_441,plain,
% 2.42/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.42/0.99      | ~ v1_relat_1(sK2)
% 2.42/0.99      | u1_struct_0(sK1) = k1_xboole_0
% 2.42/0.99      | u1_struct_0(sK0) != X1
% 2.42/0.99      | u1_struct_0(sK0) = k1_relat_1(sK2)
% 2.42/0.99      | sK2 != X0 ),
% 2.42/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_416]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_442,plain,
% 2.42/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
% 2.42/0.99      | ~ v1_relat_1(sK2)
% 2.42/0.99      | u1_struct_0(sK1) = k1_xboole_0
% 2.42/0.99      | u1_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.42/0.99      inference(unflattening,[status(thm)],[c_441]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_616,plain,
% 2.42/0.99      ( ~ v1_relat_1(sK2)
% 2.42/0.99      | u1_struct_0(sK1) = k1_xboole_0
% 2.42/0.99      | u1_struct_0(sK0) = k1_relat_1(sK2)
% 2.42/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))
% 2.42/0.99      | sK2 != sK2 ),
% 2.42/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_442]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_695,plain,
% 2.42/0.99      ( ~ v1_relat_1(sK2)
% 2.42/0.99      | u1_struct_0(sK1) = k1_xboole_0
% 2.42/0.99      | u1_struct_0(sK0) = k1_relat_1(sK2)
% 2.42/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)) ),
% 2.42/0.99      inference(equality_resolution_simp,[status(thm)],[c_616]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_771,plain,
% 2.42/0.99      ( ~ v1_relat_1(sK2)
% 2.42/0.99      | sP0_iProver_split
% 2.42/0.99      | u1_struct_0(sK1) = k1_xboole_0
% 2.42/0.99      | u1_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.42/0.99      inference(splitting,
% 2.42/0.99                [splitting(split),new_symbols(definition,[])],
% 2.42/0.99                [c_695]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1029,plain,
% 2.42/0.99      ( u1_struct_0(sK1) = k1_xboole_0
% 2.42/0.99      | u1_struct_0(sK0) = k1_relat_1(sK2)
% 2.42/0.99      | v1_relat_1(sK2) != iProver_top
% 2.42/0.99      | sP0_iProver_split = iProver_top ),
% 2.42/0.99      inference(predicate_to_equality,[status(thm)],[c_771]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_21,plain,
% 2.42/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.42/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_27,negated_conjecture,
% 2.42/0.99      ( l1_struct_0(sK1) ),
% 2.42/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_267,plain,
% 2.42/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.42/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_268,plain,
% 2.42/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.42/0.99      inference(unflattening,[status(thm)],[c_267]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_28,negated_conjecture,
% 2.42/0.99      ( l1_struct_0(sK0) ),
% 2.42/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_272,plain,
% 2.42/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.42/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_273,plain,
% 2.42/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.42/0.99      inference(unflattening,[status(thm)],[c_272]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1113,plain,
% 2.42/0.99      ( k2_struct_0(sK1) = k1_xboole_0
% 2.42/0.99      | k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.42/0.99      | v1_relat_1(sK2) != iProver_top
% 2.42/0.99      | sP0_iProver_split = iProver_top ),
% 2.42/0.99      inference(demodulation,[status(thm)],[c_1029,c_268,c_273]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_777,plain,( X0 = X0 ),theory(equality) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1231,plain,
% 2.42/0.99      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.42/0.99      inference(instantiation,[status(thm)],[c_777]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_770,plain,
% 2.42/0.99      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))
% 2.42/0.99      | ~ sP0_iProver_split ),
% 2.42/0.99      inference(splitting,
% 2.42/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.42/0.99                [c_695]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1030,plain,
% 2.42/0.99      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))
% 2.42/0.99      | sP0_iProver_split != iProver_top ),
% 2.42/0.99      inference(predicate_to_equality,[status(thm)],[c_770]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1098,plain,
% 2.42/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))
% 2.42/0.99      | sP0_iProver_split != iProver_top ),
% 2.42/0.99      inference(light_normalisation,[status(thm)],[c_1030,c_268,c_273]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1261,plain,
% 2.42/0.99      ( sP0_iProver_split != iProver_top ),
% 2.42/0.99      inference(equality_resolution,[status(thm)],[c_1098]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_5,plain,
% 2.42/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.42/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_559,plain,
% 2.42/0.99      ( ~ v1_relat_1(X0)
% 2.42/0.99      | v1_relat_1(X1)
% 2.42/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0)
% 2.42/0.99      | sK2 != X1 ),
% 2.42/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_24]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_560,plain,
% 2.42/0.99      ( ~ v1_relat_1(X0)
% 2.42/0.99      | v1_relat_1(sK2)
% 2.42/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0) ),
% 2.42/0.99      inference(unflattening,[status(thm)],[c_559]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1224,plain,
% 2.42/0.99      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 2.42/0.99      | v1_relat_1(sK2)
% 2.42/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.42/0.99      inference(instantiation,[status(thm)],[c_560]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1319,plain,
% 2.42/0.99      ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.42/0.99      | v1_relat_1(sK2)
% 2.42/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.42/0.99      inference(instantiation,[status(thm)],[c_1224]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1320,plain,
% 2.42/0.99      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.42/0.99      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.42/0.99      | v1_relat_1(sK2) = iProver_top ),
% 2.42/0.99      inference(predicate_to_equality,[status(thm)],[c_1319]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_8,plain,
% 2.42/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.42/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1427,plain,
% 2.42/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.42/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1428,plain,
% 2.42/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.42/0.99      inference(predicate_to_equality,[status(thm)],[c_1427]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1449,plain,
% 2.42/0.99      ( k2_struct_0(sK1) = k1_xboole_0 | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.42/0.99      inference(global_propositional_subsumption,
% 2.42/0.99                [status(thm)],
% 2.42/0.99                [c_1113,c_1231,c_1261,c_1320,c_1428]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_23,negated_conjecture,
% 2.42/0.99      ( k1_xboole_0 != k2_struct_0(sK1) | k1_xboole_0 = k2_struct_0(sK0) ),
% 2.42/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1460,plain,
% 2.42/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2) | k2_struct_0(sK0) = k1_xboole_0 ),
% 2.42/0.99      inference(superposition,[status(thm)],[c_1449,c_23]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_13,plain,
% 2.42/0.99      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.42/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_0,plain,
% 2.42/0.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.42/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_7,plain,
% 2.42/0.99      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 2.42/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_280,plain,
% 2.42/0.99      ( ~ v5_relat_1(X0,X1)
% 2.42/0.99      | ~ v1_relat_1(X0)
% 2.42/0.99      | X1 != X2
% 2.42/0.99      | k3_xboole_0(X3,X2) = X3
% 2.42/0.99      | k2_relat_1(X0) != X3 ),
% 2.42/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_7]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_281,plain,
% 2.42/0.99      ( ~ v5_relat_1(X0,X1)
% 2.42/0.99      | ~ v1_relat_1(X0)
% 2.42/0.99      | k3_xboole_0(k2_relat_1(X0),X1) = k2_relat_1(X0) ),
% 2.42/0.99      inference(unflattening,[status(thm)],[c_280]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_299,plain,
% 2.42/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.42/0.99      | ~ v1_relat_1(X0)
% 2.42/0.99      | k3_xboole_0(k2_relat_1(X0),X2) = k2_relat_1(X0) ),
% 2.42/0.99      inference(resolution,[status(thm)],[c_13,c_281]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_574,plain,
% 2.42/0.99      ( ~ v1_relat_1(X0)
% 2.42/0.99      | k3_xboole_0(k2_relat_1(X0),X1) = k2_relat_1(X0)
% 2.42/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
% 2.42/0.99      | sK2 != X0 ),
% 2.42/0.99      inference(resolution_lifted,[status(thm)],[c_299,c_24]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_575,plain,
% 2.42/0.99      ( ~ v1_relat_1(sK2)
% 2.42/0.99      | k3_xboole_0(k2_relat_1(sK2),X0) = k2_relat_1(sK2)
% 2.42/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
% 2.42/0.99      inference(unflattening,[status(thm)],[c_574]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1031,plain,
% 2.42/0.99      ( k3_xboole_0(k2_relat_1(sK2),X0) = k2_relat_1(sK2)
% 2.42/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
% 2.42/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.42/0.99      inference(predicate_to_equality,[status(thm)],[c_575]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1162,plain,
% 2.42/0.99      ( k3_xboole_0(k2_relat_1(sK2),X0) = k2_relat_1(sK2)
% 2.42/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
% 2.42/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.42/0.99      inference(light_normalisation,[status(thm)],[c_1031,c_268,c_273]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1185,plain,
% 2.42/0.99      ( ~ v1_relat_1(sK2)
% 2.42/0.99      | k3_xboole_0(k2_relat_1(sK2),X0) = k2_relat_1(sK2)
% 2.42/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
% 2.42/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1162]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1433,plain,
% 2.42/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0))
% 2.42/0.99      | k3_xboole_0(k2_relat_1(sK2),X0) = k2_relat_1(sK2) ),
% 2.42/0.99      inference(global_propositional_subsumption,
% 2.42/0.99                [status(thm)],
% 2.42/0.99                [c_1162,c_1185,c_1231,c_1319,c_1427]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1434,plain,
% 2.42/0.99      ( k3_xboole_0(k2_relat_1(sK2),X0) = k2_relat_1(sK2)
% 2.42/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
% 2.42/0.99      inference(renaming,[status(thm)],[c_1433]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1440,plain,
% 2.42/0.99      ( k3_xboole_0(k2_relat_1(sK2),k2_struct_0(sK1)) = k2_relat_1(sK2) ),
% 2.42/0.99      inference(equality_resolution,[status(thm)],[c_1434]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1032,plain,
% 2.42/0.99      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0)
% 2.42/0.99      | v1_relat_1(X0) != iProver_top
% 2.42/0.99      | v1_relat_1(sK2) = iProver_top ),
% 2.42/0.99      inference(predicate_to_equality,[status(thm)],[c_560]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1122,plain,
% 2.42/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(X0)
% 2.42/0.99      | v1_relat_1(X0) != iProver_top
% 2.42/0.99      | v1_relat_1(sK2) = iProver_top ),
% 2.42/0.99      inference(light_normalisation,[status(thm)],[c_1032,c_268,c_273]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1569,plain,
% 2.42/0.99      ( k2_struct_0(sK0) = k1_xboole_0
% 2.42/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))) != k1_zfmisc_1(X0)
% 2.42/0.99      | v1_relat_1(X0) != iProver_top
% 2.42/0.99      | v1_relat_1(sK2) = iProver_top ),
% 2.42/0.99      inference(superposition,[status(thm)],[c_1460,c_1122]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1945,plain,
% 2.42/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 2.42/0.99      inference(global_propositional_subsumption,
% 2.42/0.99                [status(thm)],
% 2.42/0.99                [c_1569,c_1231,c_1320,c_1428]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_9,plain,
% 2.42/0.99      ( ~ v1_relat_1(X0)
% 2.42/0.99      | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
% 2.42/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1040,plain,
% 2.42/0.99      ( k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1)
% 2.42/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.42/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_2416,plain,
% 2.42/0.99      ( k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0)) = k10_relat_1(sK2,X0) ),
% 2.42/0.99      inference(superposition,[status(thm)],[c_1945,c_1040]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_2507,plain,
% 2.42/0.99      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,k2_struct_0(sK1)) ),
% 2.42/0.99      inference(superposition,[status(thm)],[c_1440,c_2416]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_10,plain,
% 2.42/0.99      ( ~ v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 2.42/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1039,plain,
% 2.42/0.99      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 2.42/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.42/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_2287,plain,
% 2.42/0.99      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.42/0.99      inference(superposition,[status(thm)],[c_1945,c_1039]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_2508,plain,
% 2.42/0.99      ( k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2) ),
% 2.42/0.99      inference(light_normalisation,[status(thm)],[c_2507,c_2287]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_15,plain,
% 2.42/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.42/0.99      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.42/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_589,plain,
% 2.42/0.99      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 2.42/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.42/0.99      | sK2 != X2 ),
% 2.42/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_590,plain,
% 2.42/0.99      ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
% 2.42/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.42/0.99      inference(unflattening,[status(thm)],[c_589]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1129,plain,
% 2.42/0.99      ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
% 2.42/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.42/0.99      inference(light_normalisation,[status(thm)],[c_590,c_268,c_273]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1381,plain,
% 2.42/0.99      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0) ),
% 2.42/0.99      inference(equality_resolution,[status(thm)],[c_1129]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_22,negated_conjecture,
% 2.42/0.99      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
% 2.42/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1060,plain,
% 2.42/0.99      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
% 2.42/0.99      inference(light_normalisation,[status(thm)],[c_22,c_268,c_273]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_2510,plain,
% 2.42/0.99      ( k10_relat_1(sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
% 2.42/0.99      inference(demodulation,[status(thm)],[c_1381,c_1060]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_3503,plain,
% 2.42/0.99      ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 2.42/0.99      inference(demodulation,[status(thm)],[c_2508,c_2510]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_3506,plain,
% 2.42/0.99      ( k2_struct_0(sK0) = k1_xboole_0 ),
% 2.42/0.99      inference(superposition,[status(thm)],[c_1460,c_3503]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_3558,plain,
% 2.42/0.99      ( k1_relat_1(sK2) != k1_xboole_0 ),
% 2.42/0.99      inference(demodulation,[status(thm)],[c_3506,c_3503]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_18,plain,
% 2.42/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.42/0.99      | v1_partfun1(X0,k1_xboole_0)
% 2.42/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.42/0.99      | ~ v1_funct_1(X0) ),
% 2.42/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_356,plain,
% 2.42/0.99      ( v1_partfun1(X0,k1_xboole_0)
% 2.42/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.42/0.99      | ~ v1_funct_1(X0)
% 2.42/0.99      | u1_struct_0(sK1) != X1
% 2.42/0.99      | u1_struct_0(sK0) != k1_xboole_0
% 2.42/0.99      | sK2 != X0 ),
% 2.42/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_357,plain,
% 2.42/0.99      ( v1_partfun1(sK2,k1_xboole_0)
% 2.42/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
% 2.42/0.99      | ~ v1_funct_1(sK2)
% 2.42/0.99      | u1_struct_0(sK0) != k1_xboole_0 ),
% 2.42/0.99      inference(unflattening,[status(thm)],[c_356]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_359,plain,
% 2.42/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
% 2.42/0.99      | v1_partfun1(sK2,k1_xboole_0)
% 2.42/0.99      | u1_struct_0(sK0) != k1_xboole_0 ),
% 2.42/0.99      inference(global_propositional_subsumption,[status(thm)],[c_357,c_26]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_360,plain,
% 2.42/0.99      ( v1_partfun1(sK2,k1_xboole_0)
% 2.42/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
% 2.42/0.99      | u1_struct_0(sK0) != k1_xboole_0 ),
% 2.42/0.99      inference(renaming,[status(thm)],[c_359]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_396,plain,
% 2.42/0.99      ( ~ v4_relat_1(X0,X1)
% 2.42/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
% 2.42/0.99      | ~ v1_relat_1(X0)
% 2.42/0.99      | u1_struct_0(sK0) != k1_xboole_0
% 2.42/0.99      | k1_relat_1(X0) = X1
% 2.42/0.99      | sK2 != X0
% 2.42/0.99      | k1_xboole_0 != X1 ),
% 2.42/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_360]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_397,plain,
% 2.42/0.99      ( ~ v4_relat_1(sK2,k1_xboole_0)
% 2.42/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
% 2.42/0.99      | ~ v1_relat_1(sK2)
% 2.42/0.99      | u1_struct_0(sK0) != k1_xboole_0
% 2.42/0.99      | k1_relat_1(sK2) = k1_xboole_0 ),
% 2.42/0.99      inference(unflattening,[status(thm)],[c_396]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_409,plain,
% 2.42/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
% 2.42/0.99      | ~ v1_relat_1(sK2)
% 2.42/0.99      | u1_struct_0(sK0) != k1_xboole_0
% 2.42/0.99      | k1_relat_1(sK2) = k1_xboole_0 ),
% 2.42/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_397,c_14]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_598,plain,
% 2.42/0.99      ( ~ v1_relat_1(sK2)
% 2.42/0.99      | u1_struct_0(sK0) != k1_xboole_0
% 2.42/0.99      | k1_relat_1(sK2) = k1_xboole_0
% 2.42/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
% 2.42/0.99      | sK2 != sK2 ),
% 2.42/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_409]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_699,plain,
% 2.42/0.99      ( ~ v1_relat_1(sK2)
% 2.42/0.99      | u1_struct_0(sK0) != k1_xboole_0
% 2.42/0.99      | k1_relat_1(sK2) = k1_xboole_0
% 2.42/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) ),
% 2.42/0.99      inference(equality_resolution_simp,[status(thm)],[c_598]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1028,plain,
% 2.42/0.99      ( u1_struct_0(sK0) != k1_xboole_0
% 2.42/0.99      | k1_relat_1(sK2) = k1_xboole_0
% 2.42/0.99      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
% 2.42/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.42/0.99      inference(predicate_to_equality,[status(thm)],[c_699]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1169,plain,
% 2.42/0.99      ( k2_struct_0(sK0) != k1_xboole_0
% 2.42/0.99      | k1_relat_1(sK2) = k1_xboole_0
% 2.42/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))
% 2.42/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.42/0.99      inference(light_normalisation,[status(thm)],[c_1028,c_268,c_273]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_2,plain,
% 2.42/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.42/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_1170,plain,
% 2.42/0.99      ( k2_struct_0(sK0) != k1_xboole_0
% 2.42/0.99      | k1_relat_1(sK2) = k1_xboole_0
% 2.42/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k1_xboole_0)
% 2.42/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.42/0.99      inference(demodulation,[status(thm)],[c_1169,c_2]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_2910,plain,
% 2.42/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k1_xboole_0)
% 2.42/0.99      | k1_relat_1(sK2) = k1_xboole_0
% 2.42/0.99      | k2_struct_0(sK0) != k1_xboole_0 ),
% 2.42/0.99      inference(global_propositional_subsumption,
% 2.42/0.99                [status(thm)],
% 2.42/0.99                [c_1170,c_1231,c_1320,c_1428]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_2911,plain,
% 2.42/0.99      ( k2_struct_0(sK0) != k1_xboole_0
% 2.42/0.99      | k1_relat_1(sK2) = k1_xboole_0
% 2.42/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k1_xboole_0) ),
% 2.42/0.99      inference(renaming,[status(thm)],[c_2910]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_3565,plain,
% 2.42/0.99      ( k1_relat_1(sK2) = k1_xboole_0
% 2.42/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))) != k1_zfmisc_1(k1_xboole_0)
% 2.42/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.42/0.99      inference(demodulation,[status(thm)],[c_3506,c_2911]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_3645,plain,
% 2.42/0.99      ( k1_relat_1(sK2) = k1_xboole_0
% 2.42/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))) != k1_zfmisc_1(k1_xboole_0) ),
% 2.42/0.99      inference(equality_resolution_simp,[status(thm)],[c_3565]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_3648,plain,
% 2.42/0.99      ( k1_relat_1(sK2) = k1_xboole_0
% 2.42/0.99      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
% 2.42/0.99      inference(demodulation,[status(thm)],[c_3645,c_2]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_3649,plain,
% 2.42/0.99      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 2.42/0.99      inference(equality_resolution_simp,[status(thm)],[c_3648]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_3652,plain,
% 2.42/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 2.42/0.99      inference(light_normalisation,[status(thm)],[c_3558,c_3649]) ).
% 2.42/0.99  
% 2.42/0.99  cnf(c_3653,plain,
% 2.42/0.99      ( $false ),
% 2.42/0.99      inference(equality_resolution_simp,[status(thm)],[c_3652]) ).
% 2.42/0.99  
% 2.42/0.99  
% 2.42/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.42/0.99  
% 2.42/0.99  ------                               Statistics
% 2.42/0.99  
% 2.42/0.99  ------ General
% 2.42/0.99  
% 2.42/0.99  abstr_ref_over_cycles:                  0
% 2.42/0.99  abstr_ref_under_cycles:                 0
% 2.42/0.99  gc_basic_clause_elim:                   0
% 2.42/0.99  forced_gc_time:                         0
% 2.42/0.99  parsing_time:                           0.009
% 2.42/0.99  unif_index_cands_time:                  0.
% 2.42/0.99  unif_index_add_time:                    0.
% 2.42/0.99  orderings_time:                         0.
% 2.42/0.99  out_proof_time:                         0.024
% 2.42/0.99  total_time:                             0.169
% 2.42/0.99  num_of_symbols:                         57
% 2.42/0.99  num_of_terms:                           2700
% 2.42/0.99  
% 2.42/0.99  ------ Preprocessing
% 2.42/0.99  
% 2.42/0.99  num_of_splits:                          3
% 2.42/0.99  num_of_split_atoms:                     3
% 2.42/0.99  num_of_reused_defs:                     0
% 2.42/0.99  num_eq_ax_congr_red:                    10
% 2.42/0.99  num_of_sem_filtered_clauses:            1
% 2.42/0.99  num_of_subtypes:                        0
% 2.42/0.99  monotx_restored_types:                  0
% 2.42/0.99  sat_num_of_epr_types:                   0
% 2.42/0.99  sat_num_of_non_cyclic_types:            0
% 2.42/0.99  sat_guarded_non_collapsed_types:        0
% 2.42/0.99  num_pure_diseq_elim:                    0
% 2.42/0.99  simp_replaced_by:                       0
% 2.42/0.99  res_preprocessed:                       134
% 2.42/0.99  prep_upred:                             0
% 2.42/0.99  prep_unflattend:                        27
% 2.42/0.99  smt_new_axioms:                         0
% 2.42/0.99  pred_elim_cands:                        1
% 2.42/0.99  pred_elim:                              8
% 2.42/0.99  pred_elim_cl:                           5
% 2.42/0.99  pred_elim_cycles:                       11
% 2.42/0.99  merged_defs:                            0
% 2.42/0.99  merged_defs_ncl:                        0
% 2.42/0.99  bin_hyper_res:                          0
% 2.42/0.99  prep_cycles:                            4
% 2.42/0.99  pred_elim_time:                         0.008
% 2.42/0.99  splitting_time:                         0.
% 2.42/0.99  sem_filter_time:                        0.
% 2.42/0.99  monotx_time:                            0.
% 2.42/0.99  subtype_inf_time:                       0.
% 2.42/0.99  
% 2.42/0.99  ------ Problem properties
% 2.42/0.99  
% 2.42/0.99  clauses:                                27
% 2.42/0.99  conjectures:                            2
% 2.42/0.99  epr:                                    0
% 2.42/0.99  horn:                                   23
% 2.42/0.99  ground:                                 9
% 2.42/0.99  unary:                                  8
% 2.42/0.99  binary:                                 10
% 2.42/0.99  lits:                                   61
% 2.42/0.99  lits_eq:                                42
% 2.42/0.99  fd_pure:                                0
% 2.42/0.99  fd_pseudo:                              0
% 2.42/0.99  fd_cond:                                1
% 2.42/0.99  fd_pseudo_cond:                         0
% 2.42/0.99  ac_symbols:                             0
% 2.42/0.99  
% 2.42/0.99  ------ Propositional Solver
% 2.42/0.99  
% 2.42/0.99  prop_solver_calls:                      28
% 2.42/0.99  prop_fast_solver_calls:                 827
% 2.42/0.99  smt_solver_calls:                       0
% 2.42/0.99  smt_fast_solver_calls:                  0
% 2.42/0.99  prop_num_of_clauses:                    1113
% 2.42/0.99  prop_preprocess_simplified:             3995
% 2.42/0.99  prop_fo_subsumed:                       20
% 2.42/0.99  prop_solver_time:                       0.
% 2.42/0.99  smt_solver_time:                        0.
% 2.42/0.99  smt_fast_solver_time:                   0.
% 2.42/0.99  prop_fast_solver_time:                  0.
% 2.42/0.99  prop_unsat_core_time:                   0.
% 2.42/0.99  
% 2.42/0.99  ------ QBF
% 2.42/0.99  
% 2.42/0.99  qbf_q_res:                              0
% 2.42/0.99  qbf_num_tautologies:                    0
% 2.42/0.99  qbf_prep_cycles:                        0
% 2.42/0.99  
% 2.42/0.99  ------ BMC1
% 2.42/0.99  
% 2.42/0.99  bmc1_current_bound:                     -1
% 2.42/0.99  bmc1_last_solved_bound:                 -1
% 2.42/0.99  bmc1_unsat_core_size:                   -1
% 2.42/0.99  bmc1_unsat_core_parents_size:           -1
% 2.42/0.99  bmc1_merge_next_fun:                    0
% 2.42/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.42/0.99  
% 2.42/0.99  ------ Instantiation
% 2.42/0.99  
% 2.42/0.99  inst_num_of_clauses:                    567
% 2.42/0.99  inst_num_in_passive:                    71
% 2.42/0.99  inst_num_in_active:                     278
% 2.42/0.99  inst_num_in_unprocessed:                218
% 2.42/0.99  inst_num_of_loops:                      310
% 2.42/0.99  inst_num_of_learning_restarts:          0
% 2.42/0.99  inst_num_moves_active_passive:          28
% 2.42/0.99  inst_lit_activity:                      0
% 2.42/0.99  inst_lit_activity_moves:                0
% 2.42/0.99  inst_num_tautologies:                   0
% 2.42/0.99  inst_num_prop_implied:                  0
% 2.42/0.99  inst_num_existing_simplified:           0
% 2.42/0.99  inst_num_eq_res_simplified:             0
% 2.42/0.99  inst_num_child_elim:                    0
% 2.42/0.99  inst_num_of_dismatching_blockings:      131
% 2.42/0.99  inst_num_of_non_proper_insts:           479
% 2.42/0.99  inst_num_of_duplicates:                 0
% 2.42/0.99  inst_inst_num_from_inst_to_res:         0
% 2.42/0.99  inst_dismatching_checking_time:         0.
% 2.42/0.99  
% 2.42/0.99  ------ Resolution
% 2.42/0.99  
% 2.42/0.99  res_num_of_clauses:                     0
% 2.42/0.99  res_num_in_passive:                     0
% 2.42/0.99  res_num_in_active:                      0
% 2.42/0.99  res_num_of_loops:                       138
% 2.42/0.99  res_forward_subset_subsumed:            72
% 2.42/0.99  res_backward_subset_subsumed:           4
% 2.42/0.99  res_forward_subsumed:                   0
% 2.42/0.99  res_backward_subsumed:                  0
% 2.42/0.99  res_forward_subsumption_resolution:     1
% 2.42/0.99  res_backward_subsumption_resolution:    0
% 2.42/0.99  res_clause_to_clause_subsumption:       109
% 2.42/0.99  res_orphan_elimination:                 0
% 2.42/0.99  res_tautology_del:                      68
% 2.42/0.99  res_num_eq_res_simplified:              2
% 2.42/0.99  res_num_sel_changes:                    0
% 2.42/0.99  res_moves_from_active_to_pass:          0
% 2.42/0.99  
% 2.42/0.99  ------ Superposition
% 2.42/0.99  
% 2.42/0.99  sup_time_total:                         0.
% 2.42/0.99  sup_time_generating:                    0.
% 2.42/0.99  sup_time_sim_full:                      0.
% 2.42/0.99  sup_time_sim_immed:                     0.
% 2.42/0.99  
% 2.42/0.99  sup_num_of_clauses:                     34
% 2.42/0.99  sup_num_in_active:                      23
% 2.42/0.99  sup_num_in_passive:                     11
% 2.42/0.99  sup_num_of_loops:                       60
% 2.42/0.99  sup_fw_superposition:                   61
% 2.42/0.99  sup_bw_superposition:                   20
% 2.42/0.99  sup_immediate_simplified:               39
% 2.42/0.99  sup_given_eliminated:                   0
% 2.42/0.99  comparisons_done:                       0
% 2.42/0.99  comparisons_avoided:                    18
% 2.42/0.99  
% 2.42/0.99  ------ Simplifications
% 2.42/0.99  
% 2.42/0.99  
% 2.42/0.99  sim_fw_subset_subsumed:                 24
% 2.42/0.99  sim_bw_subset_subsumed:                 11
% 2.42/0.99  sim_fw_subsumed:                        4
% 2.42/0.99  sim_bw_subsumed:                        2
% 2.42/0.99  sim_fw_subsumption_res:                 0
% 2.42/0.99  sim_bw_subsumption_res:                 0
% 2.42/0.99  sim_tautology_del:                      2
% 2.42/0.99  sim_eq_tautology_del:                   14
% 2.42/0.99  sim_eq_res_simp:                        10
% 2.42/0.99  sim_fw_demodulated:                     26
% 2.42/0.99  sim_bw_demodulated:                     36
% 2.42/0.99  sim_light_normalised:                   15
% 2.42/0.99  sim_joinable_taut:                      0
% 2.42/0.99  sim_joinable_simp:                      0
% 2.42/0.99  sim_ac_normalised:                      0
% 2.42/0.99  sim_smt_subsumption:                    0
% 2.42/0.99  
%------------------------------------------------------------------------------
