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
% DateTime   : Thu Dec  3 12:16:55 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :  183 (1297 expanded)
%              Number of clauses        :  108 ( 391 expanded)
%              Number of leaves         :   24 ( 358 expanded)
%              Depth                    :   23
%              Number of atoms          :  497 (7177 expanded)
%              Number of equality atoms :  281 (2858 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f74,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f69,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f71,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f55,f65])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f82,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f57,f65])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f78,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f53,f65])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f60,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f63,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f72,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

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
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f83,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f47])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f80,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f56,f65])).

fof(f75,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f84,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f46])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_778,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_29,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_273,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_29])).

cnf(c_274,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_273])).

cnf(c_30,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_278,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_279,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_278])).

cnf(c_805,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_778,c_274,c_279])).

cnf(c_15,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_5,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_285,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_15,c_5])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_295,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_285,c_14])).

cnf(c_10,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_305,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X2)) = X0 ),
    inference(resolution,[status(thm)],[c_295,c_10])).

cnf(c_309,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relat_1(X0,k6_partfun1(X2)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_305,c_14])).

cnf(c_777,plain,
    ( k5_relat_1(X0,k6_partfun1(X1)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_309])).

cnf(c_1071,plain,
    ( k5_relat_1(sK2,k6_partfun1(k2_struct_0(sK1))) = sK2 ),
    inference(superposition,[status(thm)],[c_805,c_777])).

cnf(c_13,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_782,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_781,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1519,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_805,c_781])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_783,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2662,plain,
    ( k1_relat_1(k5_relat_1(sK2,X0)) = k10_relat_1(sK2,k1_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1519,c_783])).

cnf(c_3041,plain,
    ( k1_relat_1(k5_relat_1(sK2,k6_partfun1(X0))) = k10_relat_1(sK2,k1_relat_1(k6_partfun1(X0))) ),
    inference(superposition,[status(thm)],[c_782,c_2662])).

cnf(c_9,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3050,plain,
    ( k1_relat_1(k5_relat_1(sK2,k6_partfun1(X0))) = k10_relat_1(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_3041,c_9])).

cnf(c_3433,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1071,c_3050])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_780,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2466,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_805,c_780])).

cnf(c_24,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_812,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_24,c_274,c_279])).

cnf(c_2494,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2466,c_812])).

cnf(c_3688,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3433,c_2494])).

cnf(c_536,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1000,plain,
    ( X0 != X1
    | k2_struct_0(sK0) != X1
    | k2_struct_0(sK0) = X0 ),
    inference(instantiation,[status(thm)],[c_536])).

cnf(c_3584,plain,
    ( k8_relset_1(X0,X1,X2,X3) != X4
    | k2_struct_0(sK0) != X4
    | k2_struct_0(sK0) = k8_relset_1(X0,X1,X2,X3) ),
    inference(instantiation,[status(thm)],[c_1000])).

cnf(c_3585,plain,
    ( k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k2_struct_0(sK0) = k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k2_struct_0(sK0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3584])).

cnf(c_3,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_784,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2465,plain,
    ( k8_relset_1(X0,X1,k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_784,c_780])).

cnf(c_6,plain,
    ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2485,plain,
    ( k8_relset_1(X0,X1,k1_xboole_0,X2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2465,c_6])).

cnf(c_16,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_19,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_325,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_16,c_19])).

cnf(c_329,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_325,c_19,c_16,c_14])).

cnf(c_330,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_329])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_386,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_387,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_389,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_387,c_28,c_26])).

cnf(c_427,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) != X1
    | k1_relat_1(X0) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_330,c_389])).

cnf(c_428,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
    | u1_struct_0(sK1) = k1_xboole_0
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_531,plain,
    ( sP0_iProver_split
    | u1_struct_0(sK1) = k1_xboole_0
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_428])).

cnf(c_773,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | k1_relat_1(sK2) = u1_struct_0(sK0)
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_531])).

cnf(c_815,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_773,c_274,c_279])).

cnf(c_879,plain,
    ( sP0_iProver_split
    | k2_struct_0(sK1) = k1_xboole_0
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_815])).

cnf(c_530,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_428])).

cnf(c_898,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_530])).

cnf(c_964,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_815,c_26,c_879,c_898])).

cnf(c_965,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(renaming,[status(thm)],[c_964])).

cnf(c_968,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_965,c_805])).

cnf(c_0,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1419,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_968,c_0])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k8_relset_1(X1,X1,k6_partfun1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_779,plain,
    ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2215,plain,
    ( k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2) = sK2
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1419,c_779])).

cnf(c_11,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2223,plain,
    ( k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2) = sK2
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2215,c_11])).

cnf(c_2567,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2485,c_2223])).

cnf(c_2213,plain,
    ( k8_relset_1(X0,X0,k6_partfun1(X0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_784,c_779])).

cnf(c_2411,plain,
    ( k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11,c_2213])).

cnf(c_546,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k8_relset_1(X0,X2,X4,X6) = k8_relset_1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_2354,plain,
    ( X0 != u1_struct_0(sK1)
    | X1 != u1_struct_0(sK0)
    | X2 != k2_struct_0(sK1)
    | X3 != sK2
    | k8_relset_1(X1,X0,X3,X2) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_546])).

cnf(c_2356,plain,
    ( k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    | k1_xboole_0 != u1_struct_0(sK1)
    | k1_xboole_0 != u1_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK1)
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2354])).

cnf(c_1224,plain,
    ( X0 != X1
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != X1
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = X0 ),
    inference(instantiation,[status(thm)],[c_536])).

cnf(c_1495,plain,
    ( X0 != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = X0
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1224])).

cnf(c_2353,plain,
    ( k8_relset_1(X0,X1,X2,X3) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k8_relset_1(X0,X1,X2,X3)
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1495])).

cnf(c_2355,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2353])).

cnf(c_1278,plain,
    ( u1_struct_0(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_536])).

cnf(c_1925,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k1_xboole_0 = u1_struct_0(sK1)
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1278])).

cnf(c_1270,plain,
    ( u1_struct_0(sK0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_536])).

cnf(c_1863,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1270])).

cnf(c_933,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != X0
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k2_struct_0(sK0)
    | k2_struct_0(sK0) != X0 ),
    inference(instantiation,[status(thm)],[c_536])).

cnf(c_1225,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k8_relset_1(X0,X1,X2,X3)
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k2_struct_0(sK0)
    | k2_struct_0(sK0) != k8_relset_1(X0,X1,X2,X3) ),
    inference(instantiation,[status(thm)],[c_933])).

cnf(c_1227,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k2_struct_0(sK0)
    | k2_struct_0(sK0) != k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1225])).

cnf(c_535,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1223,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_535])).

cnf(c_1077,plain,
    ( k2_struct_0(sK0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_536])).

cnf(c_1078,plain,
    ( k2_struct_0(sK0) != k1_xboole_0
    | k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1077])).

cnf(c_1044,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_536])).

cnf(c_1045,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1044])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_971,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_965,c_25])).

cnf(c_935,plain,
    ( k2_struct_0(sK1) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_536])).

cnf(c_936,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | k1_xboole_0 = k2_struct_0(sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_1,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_91,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_90,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3688,c_3585,c_2567,c_2411,c_2356,c_2355,c_1925,c_1863,c_1227,c_1223,c_1078,c_1045,c_971,c_965,c_936,c_279,c_274,c_91,c_90,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:43:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 2.62/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/0.99  
% 2.62/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.62/0.99  
% 2.62/0.99  ------  iProver source info
% 2.62/0.99  
% 2.62/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.62/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.62/0.99  git: non_committed_changes: false
% 2.62/0.99  git: last_make_outside_of_git: false
% 2.62/0.99  
% 2.62/0.99  ------ 
% 2.62/0.99  
% 2.62/0.99  ------ Input Options
% 2.62/0.99  
% 2.62/0.99  --out_options                           all
% 2.62/0.99  --tptp_safe_out                         true
% 2.62/0.99  --problem_path                          ""
% 2.62/0.99  --include_path                          ""
% 2.62/0.99  --clausifier                            res/vclausify_rel
% 2.62/0.99  --clausifier_options                    --mode clausify
% 2.62/0.99  --stdin                                 false
% 2.62/0.99  --stats_out                             all
% 2.62/0.99  
% 2.62/0.99  ------ General Options
% 2.62/0.99  
% 2.62/0.99  --fof                                   false
% 2.62/0.99  --time_out_real                         305.
% 2.62/0.99  --time_out_virtual                      -1.
% 2.62/0.99  --symbol_type_check                     false
% 2.62/0.99  --clausify_out                          false
% 2.62/0.99  --sig_cnt_out                           false
% 2.62/0.99  --trig_cnt_out                          false
% 2.62/0.99  --trig_cnt_out_tolerance                1.
% 2.62/0.99  --trig_cnt_out_sk_spl                   false
% 2.62/0.99  --abstr_cl_out                          false
% 2.62/0.99  
% 2.62/0.99  ------ Global Options
% 2.62/0.99  
% 2.62/0.99  --schedule                              default
% 2.62/0.99  --add_important_lit                     false
% 2.62/0.99  --prop_solver_per_cl                    1000
% 2.62/0.99  --min_unsat_core                        false
% 2.62/0.99  --soft_assumptions                      false
% 2.62/0.99  --soft_lemma_size                       3
% 2.62/0.99  --prop_impl_unit_size                   0
% 2.62/0.99  --prop_impl_unit                        []
% 2.62/0.99  --share_sel_clauses                     true
% 2.62/0.99  --reset_solvers                         false
% 2.62/0.99  --bc_imp_inh                            [conj_cone]
% 2.62/0.99  --conj_cone_tolerance                   3.
% 2.62/0.99  --extra_neg_conj                        none
% 2.62/0.99  --large_theory_mode                     true
% 2.62/0.99  --prolific_symb_bound                   200
% 2.62/0.99  --lt_threshold                          2000
% 2.62/0.99  --clause_weak_htbl                      true
% 2.62/0.99  --gc_record_bc_elim                     false
% 2.62/0.99  
% 2.62/0.99  ------ Preprocessing Options
% 2.62/0.99  
% 2.62/0.99  --preprocessing_flag                    true
% 2.62/0.99  --time_out_prep_mult                    0.1
% 2.62/0.99  --splitting_mode                        input
% 2.62/0.99  --splitting_grd                         true
% 2.62/0.99  --splitting_cvd                         false
% 2.62/0.99  --splitting_cvd_svl                     false
% 2.62/0.99  --splitting_nvd                         32
% 2.62/0.99  --sub_typing                            true
% 2.62/0.99  --prep_gs_sim                           true
% 2.62/0.99  --prep_unflatten                        true
% 2.62/0.99  --prep_res_sim                          true
% 2.62/0.99  --prep_upred                            true
% 2.62/0.99  --prep_sem_filter                       exhaustive
% 2.62/0.99  --prep_sem_filter_out                   false
% 2.62/0.99  --pred_elim                             true
% 2.62/0.99  --res_sim_input                         true
% 2.62/0.99  --eq_ax_congr_red                       true
% 2.62/0.99  --pure_diseq_elim                       true
% 2.62/0.99  --brand_transform                       false
% 2.62/0.99  --non_eq_to_eq                          false
% 2.62/0.99  --prep_def_merge                        true
% 2.62/0.99  --prep_def_merge_prop_impl              false
% 2.62/0.99  --prep_def_merge_mbd                    true
% 2.62/0.99  --prep_def_merge_tr_red                 false
% 2.62/0.99  --prep_def_merge_tr_cl                  false
% 2.62/0.99  --smt_preprocessing                     true
% 2.62/0.99  --smt_ac_axioms                         fast
% 2.62/0.99  --preprocessed_out                      false
% 2.62/0.99  --preprocessed_stats                    false
% 2.62/0.99  
% 2.62/0.99  ------ Abstraction refinement Options
% 2.62/0.99  
% 2.62/0.99  --abstr_ref                             []
% 2.62/0.99  --abstr_ref_prep                        false
% 2.62/0.99  --abstr_ref_until_sat                   false
% 2.62/0.99  --abstr_ref_sig_restrict                funpre
% 2.62/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.62/0.99  --abstr_ref_under                       []
% 2.62/0.99  
% 2.62/0.99  ------ SAT Options
% 2.62/0.99  
% 2.62/0.99  --sat_mode                              false
% 2.62/0.99  --sat_fm_restart_options                ""
% 2.62/0.99  --sat_gr_def                            false
% 2.62/0.99  --sat_epr_types                         true
% 2.62/0.99  --sat_non_cyclic_types                  false
% 2.62/0.99  --sat_finite_models                     false
% 2.62/0.99  --sat_fm_lemmas                         false
% 2.62/0.99  --sat_fm_prep                           false
% 2.62/0.99  --sat_fm_uc_incr                        true
% 2.62/0.99  --sat_out_model                         small
% 2.62/0.99  --sat_out_clauses                       false
% 2.62/0.99  
% 2.62/0.99  ------ QBF Options
% 2.62/0.99  
% 2.62/0.99  --qbf_mode                              false
% 2.62/0.99  --qbf_elim_univ                         false
% 2.62/0.99  --qbf_dom_inst                          none
% 2.62/0.99  --qbf_dom_pre_inst                      false
% 2.62/0.99  --qbf_sk_in                             false
% 2.62/0.99  --qbf_pred_elim                         true
% 2.62/0.99  --qbf_split                             512
% 2.62/0.99  
% 2.62/0.99  ------ BMC1 Options
% 2.62/0.99  
% 2.62/0.99  --bmc1_incremental                      false
% 2.62/0.99  --bmc1_axioms                           reachable_all
% 2.62/0.99  --bmc1_min_bound                        0
% 2.62/0.99  --bmc1_max_bound                        -1
% 2.62/0.99  --bmc1_max_bound_default                -1
% 2.62/0.99  --bmc1_symbol_reachability              true
% 2.62/0.99  --bmc1_property_lemmas                  false
% 2.62/0.99  --bmc1_k_induction                      false
% 2.62/0.99  --bmc1_non_equiv_states                 false
% 2.62/0.99  --bmc1_deadlock                         false
% 2.62/0.99  --bmc1_ucm                              false
% 2.62/0.99  --bmc1_add_unsat_core                   none
% 2.62/0.99  --bmc1_unsat_core_children              false
% 2.62/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.62/0.99  --bmc1_out_stat                         full
% 2.62/0.99  --bmc1_ground_init                      false
% 2.62/0.99  --bmc1_pre_inst_next_state              false
% 2.62/0.99  --bmc1_pre_inst_state                   false
% 2.62/0.99  --bmc1_pre_inst_reach_state             false
% 2.62/0.99  --bmc1_out_unsat_core                   false
% 2.62/0.99  --bmc1_aig_witness_out                  false
% 2.62/0.99  --bmc1_verbose                          false
% 2.62/0.99  --bmc1_dump_clauses_tptp                false
% 2.62/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.62/0.99  --bmc1_dump_file                        -
% 2.62/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.62/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.62/0.99  --bmc1_ucm_extend_mode                  1
% 2.62/0.99  --bmc1_ucm_init_mode                    2
% 2.62/0.99  --bmc1_ucm_cone_mode                    none
% 2.62/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.62/0.99  --bmc1_ucm_relax_model                  4
% 2.62/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.62/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.62/0.99  --bmc1_ucm_layered_model                none
% 2.62/0.99  --bmc1_ucm_max_lemma_size               10
% 2.62/0.99  
% 2.62/0.99  ------ AIG Options
% 2.62/0.99  
% 2.62/0.99  --aig_mode                              false
% 2.62/0.99  
% 2.62/0.99  ------ Instantiation Options
% 2.62/0.99  
% 2.62/0.99  --instantiation_flag                    true
% 2.62/0.99  --inst_sos_flag                         false
% 2.62/0.99  --inst_sos_phase                        true
% 2.62/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.62/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.62/0.99  --inst_lit_sel_side                     num_symb
% 2.62/0.99  --inst_solver_per_active                1400
% 2.62/0.99  --inst_solver_calls_frac                1.
% 2.62/0.99  --inst_passive_queue_type               priority_queues
% 2.62/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.62/0.99  --inst_passive_queues_freq              [25;2]
% 2.62/0.99  --inst_dismatching                      true
% 2.62/0.99  --inst_eager_unprocessed_to_passive     true
% 2.62/0.99  --inst_prop_sim_given                   true
% 2.62/0.99  --inst_prop_sim_new                     false
% 2.62/0.99  --inst_subs_new                         false
% 2.62/0.99  --inst_eq_res_simp                      false
% 2.62/0.99  --inst_subs_given                       false
% 2.62/0.99  --inst_orphan_elimination               true
% 2.62/0.99  --inst_learning_loop_flag               true
% 2.62/0.99  --inst_learning_start                   3000
% 2.62/0.99  --inst_learning_factor                  2
% 2.62/0.99  --inst_start_prop_sim_after_learn       3
% 2.62/0.99  --inst_sel_renew                        solver
% 2.62/0.99  --inst_lit_activity_flag                true
% 2.62/0.99  --inst_restr_to_given                   false
% 2.62/0.99  --inst_activity_threshold               500
% 2.62/0.99  --inst_out_proof                        true
% 2.62/0.99  
% 2.62/0.99  ------ Resolution Options
% 2.62/0.99  
% 2.62/0.99  --resolution_flag                       true
% 2.62/0.99  --res_lit_sel                           adaptive
% 2.62/0.99  --res_lit_sel_side                      none
% 2.62/0.99  --res_ordering                          kbo
% 2.62/0.99  --res_to_prop_solver                    active
% 2.62/0.99  --res_prop_simpl_new                    false
% 2.62/0.99  --res_prop_simpl_given                  true
% 2.62/0.99  --res_passive_queue_type                priority_queues
% 2.62/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.62/0.99  --res_passive_queues_freq               [15;5]
% 2.62/0.99  --res_forward_subs                      full
% 2.62/0.99  --res_backward_subs                     full
% 2.62/0.99  --res_forward_subs_resolution           true
% 2.62/0.99  --res_backward_subs_resolution          true
% 2.62/0.99  --res_orphan_elimination                true
% 2.62/0.99  --res_time_limit                        2.
% 2.62/0.99  --res_out_proof                         true
% 2.62/0.99  
% 2.62/0.99  ------ Superposition Options
% 2.62/0.99  
% 2.62/0.99  --superposition_flag                    true
% 2.62/0.99  --sup_passive_queue_type                priority_queues
% 2.62/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.62/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.62/0.99  --demod_completeness_check              fast
% 2.62/0.99  --demod_use_ground                      true
% 2.62/0.99  --sup_to_prop_solver                    passive
% 2.62/0.99  --sup_prop_simpl_new                    true
% 2.62/0.99  --sup_prop_simpl_given                  true
% 2.62/0.99  --sup_fun_splitting                     false
% 2.62/0.99  --sup_smt_interval                      50000
% 2.62/0.99  
% 2.62/0.99  ------ Superposition Simplification Setup
% 2.62/0.99  
% 2.62/0.99  --sup_indices_passive                   []
% 2.62/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.62/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.99  --sup_full_bw                           [BwDemod]
% 2.62/0.99  --sup_immed_triv                        [TrivRules]
% 2.62/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.62/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.99  --sup_immed_bw_main                     []
% 2.62/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.62/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/0.99  
% 2.62/0.99  ------ Combination Options
% 2.62/0.99  
% 2.62/0.99  --comb_res_mult                         3
% 2.62/0.99  --comb_sup_mult                         2
% 2.62/0.99  --comb_inst_mult                        10
% 2.62/0.99  
% 2.62/0.99  ------ Debug Options
% 2.62/0.99  
% 2.62/0.99  --dbg_backtrace                         false
% 2.62/0.99  --dbg_dump_prop_clauses                 false
% 2.62/0.99  --dbg_dump_prop_clauses_file            -
% 2.62/0.99  --dbg_out_stat                          false
% 2.62/0.99  ------ Parsing...
% 2.62/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.62/0.99  
% 2.62/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.62/0.99  
% 2.62/0.99  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.62/0.99  
% 2.62/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.62/0.99  ------ Proving...
% 2.62/0.99  ------ Problem Properties 
% 2.62/0.99  
% 2.62/0.99  
% 2.62/0.99  clauses                                 23
% 2.62/0.99  conjectures                             3
% 2.62/0.99  EPR                                     0
% 2.62/0.99  Horn                                    20
% 2.62/0.99  unary                                   12
% 2.62/0.99  binary                                  7
% 2.62/0.99  lits                                    39
% 2.62/0.99  lits eq                                 22
% 2.62/0.99  fd_pure                                 0
% 2.62/0.99  fd_pseudo                               0
% 2.62/0.99  fd_cond                                 1
% 2.62/0.99  fd_pseudo_cond                          0
% 2.62/0.99  AC symbols                              0
% 2.62/0.99  
% 2.62/0.99  ------ Schedule dynamic 5 is on 
% 2.62/0.99  
% 2.62/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.62/0.99  
% 2.62/0.99  
% 2.62/0.99  ------ 
% 2.62/0.99  Current options:
% 2.62/0.99  ------ 
% 2.62/0.99  
% 2.62/0.99  ------ Input Options
% 2.62/0.99  
% 2.62/0.99  --out_options                           all
% 2.62/0.99  --tptp_safe_out                         true
% 2.62/0.99  --problem_path                          ""
% 2.62/0.99  --include_path                          ""
% 2.62/0.99  --clausifier                            res/vclausify_rel
% 2.62/0.99  --clausifier_options                    --mode clausify
% 2.62/0.99  --stdin                                 false
% 2.62/0.99  --stats_out                             all
% 2.62/0.99  
% 2.62/0.99  ------ General Options
% 2.62/0.99  
% 2.62/0.99  --fof                                   false
% 2.62/0.99  --time_out_real                         305.
% 2.62/0.99  --time_out_virtual                      -1.
% 2.62/0.99  --symbol_type_check                     false
% 2.62/0.99  --clausify_out                          false
% 2.62/0.99  --sig_cnt_out                           false
% 2.62/0.99  --trig_cnt_out                          false
% 2.62/0.99  --trig_cnt_out_tolerance                1.
% 2.62/0.99  --trig_cnt_out_sk_spl                   false
% 2.62/0.99  --abstr_cl_out                          false
% 2.62/0.99  
% 2.62/0.99  ------ Global Options
% 2.62/0.99  
% 2.62/0.99  --schedule                              default
% 2.62/0.99  --add_important_lit                     false
% 2.62/0.99  --prop_solver_per_cl                    1000
% 2.62/0.99  --min_unsat_core                        false
% 2.62/0.99  --soft_assumptions                      false
% 2.62/0.99  --soft_lemma_size                       3
% 2.62/0.99  --prop_impl_unit_size                   0
% 2.62/0.99  --prop_impl_unit                        []
% 2.62/0.99  --share_sel_clauses                     true
% 2.62/0.99  --reset_solvers                         false
% 2.62/0.99  --bc_imp_inh                            [conj_cone]
% 2.62/0.99  --conj_cone_tolerance                   3.
% 2.62/0.99  --extra_neg_conj                        none
% 2.62/0.99  --large_theory_mode                     true
% 2.62/0.99  --prolific_symb_bound                   200
% 2.62/0.99  --lt_threshold                          2000
% 2.62/0.99  --clause_weak_htbl                      true
% 2.62/0.99  --gc_record_bc_elim                     false
% 2.62/0.99  
% 2.62/0.99  ------ Preprocessing Options
% 2.62/0.99  
% 2.62/0.99  --preprocessing_flag                    true
% 2.62/0.99  --time_out_prep_mult                    0.1
% 2.62/0.99  --splitting_mode                        input
% 2.62/0.99  --splitting_grd                         true
% 2.62/0.99  --splitting_cvd                         false
% 2.62/0.99  --splitting_cvd_svl                     false
% 2.62/0.99  --splitting_nvd                         32
% 2.62/0.99  --sub_typing                            true
% 2.62/0.99  --prep_gs_sim                           true
% 2.62/0.99  --prep_unflatten                        true
% 2.62/0.99  --prep_res_sim                          true
% 2.62/0.99  --prep_upred                            true
% 2.62/0.99  --prep_sem_filter                       exhaustive
% 2.62/0.99  --prep_sem_filter_out                   false
% 2.62/0.99  --pred_elim                             true
% 2.62/0.99  --res_sim_input                         true
% 2.62/0.99  --eq_ax_congr_red                       true
% 2.62/0.99  --pure_diseq_elim                       true
% 2.62/0.99  --brand_transform                       false
% 2.62/0.99  --non_eq_to_eq                          false
% 2.62/0.99  --prep_def_merge                        true
% 2.62/0.99  --prep_def_merge_prop_impl              false
% 2.62/0.99  --prep_def_merge_mbd                    true
% 2.62/0.99  --prep_def_merge_tr_red                 false
% 2.62/0.99  --prep_def_merge_tr_cl                  false
% 2.62/0.99  --smt_preprocessing                     true
% 2.62/0.99  --smt_ac_axioms                         fast
% 2.62/0.99  --preprocessed_out                      false
% 2.62/0.99  --preprocessed_stats                    false
% 2.62/0.99  
% 2.62/0.99  ------ Abstraction refinement Options
% 2.62/0.99  
% 2.62/0.99  --abstr_ref                             []
% 2.62/0.99  --abstr_ref_prep                        false
% 2.62/0.99  --abstr_ref_until_sat                   false
% 2.62/0.99  --abstr_ref_sig_restrict                funpre
% 2.62/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.62/0.99  --abstr_ref_under                       []
% 2.62/0.99  
% 2.62/0.99  ------ SAT Options
% 2.62/0.99  
% 2.62/0.99  --sat_mode                              false
% 2.62/0.99  --sat_fm_restart_options                ""
% 2.62/0.99  --sat_gr_def                            false
% 2.62/0.99  --sat_epr_types                         true
% 2.62/0.99  --sat_non_cyclic_types                  false
% 2.62/0.99  --sat_finite_models                     false
% 2.62/0.99  --sat_fm_lemmas                         false
% 2.62/0.99  --sat_fm_prep                           false
% 2.62/0.99  --sat_fm_uc_incr                        true
% 2.62/0.99  --sat_out_model                         small
% 2.62/0.99  --sat_out_clauses                       false
% 2.62/0.99  
% 2.62/0.99  ------ QBF Options
% 2.62/0.99  
% 2.62/0.99  --qbf_mode                              false
% 2.62/0.99  --qbf_elim_univ                         false
% 2.62/0.99  --qbf_dom_inst                          none
% 2.62/0.99  --qbf_dom_pre_inst                      false
% 2.62/0.99  --qbf_sk_in                             false
% 2.62/0.99  --qbf_pred_elim                         true
% 2.62/0.99  --qbf_split                             512
% 2.62/0.99  
% 2.62/0.99  ------ BMC1 Options
% 2.62/0.99  
% 2.62/0.99  --bmc1_incremental                      false
% 2.62/0.99  --bmc1_axioms                           reachable_all
% 2.62/0.99  --bmc1_min_bound                        0
% 2.62/0.99  --bmc1_max_bound                        -1
% 2.62/0.99  --bmc1_max_bound_default                -1
% 2.62/0.99  --bmc1_symbol_reachability              true
% 2.62/0.99  --bmc1_property_lemmas                  false
% 2.62/0.99  --bmc1_k_induction                      false
% 2.62/0.99  --bmc1_non_equiv_states                 false
% 2.62/0.99  --bmc1_deadlock                         false
% 2.62/0.99  --bmc1_ucm                              false
% 2.62/0.99  --bmc1_add_unsat_core                   none
% 2.62/0.99  --bmc1_unsat_core_children              false
% 2.62/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.62/0.99  --bmc1_out_stat                         full
% 2.62/0.99  --bmc1_ground_init                      false
% 2.62/0.99  --bmc1_pre_inst_next_state              false
% 2.62/0.99  --bmc1_pre_inst_state                   false
% 2.62/0.99  --bmc1_pre_inst_reach_state             false
% 2.62/0.99  --bmc1_out_unsat_core                   false
% 2.62/0.99  --bmc1_aig_witness_out                  false
% 2.62/0.99  --bmc1_verbose                          false
% 2.62/0.99  --bmc1_dump_clauses_tptp                false
% 2.62/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.62/0.99  --bmc1_dump_file                        -
% 2.62/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.62/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.62/0.99  --bmc1_ucm_extend_mode                  1
% 2.62/0.99  --bmc1_ucm_init_mode                    2
% 2.62/0.99  --bmc1_ucm_cone_mode                    none
% 2.62/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.62/0.99  --bmc1_ucm_relax_model                  4
% 2.62/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.62/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.62/0.99  --bmc1_ucm_layered_model                none
% 2.62/0.99  --bmc1_ucm_max_lemma_size               10
% 2.62/0.99  
% 2.62/0.99  ------ AIG Options
% 2.62/0.99  
% 2.62/0.99  --aig_mode                              false
% 2.62/0.99  
% 2.62/0.99  ------ Instantiation Options
% 2.62/0.99  
% 2.62/0.99  --instantiation_flag                    true
% 2.62/0.99  --inst_sos_flag                         false
% 2.62/0.99  --inst_sos_phase                        true
% 2.62/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.62/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.62/0.99  --inst_lit_sel_side                     none
% 2.62/0.99  --inst_solver_per_active                1400
% 2.62/0.99  --inst_solver_calls_frac                1.
% 2.62/0.99  --inst_passive_queue_type               priority_queues
% 2.62/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.62/0.99  --inst_passive_queues_freq              [25;2]
% 2.62/0.99  --inst_dismatching                      true
% 2.62/0.99  --inst_eager_unprocessed_to_passive     true
% 2.62/0.99  --inst_prop_sim_given                   true
% 2.62/0.99  --inst_prop_sim_new                     false
% 2.62/0.99  --inst_subs_new                         false
% 2.62/0.99  --inst_eq_res_simp                      false
% 2.62/0.99  --inst_subs_given                       false
% 2.62/0.99  --inst_orphan_elimination               true
% 2.62/0.99  --inst_learning_loop_flag               true
% 2.62/0.99  --inst_learning_start                   3000
% 2.62/0.99  --inst_learning_factor                  2
% 2.62/0.99  --inst_start_prop_sim_after_learn       3
% 2.62/0.99  --inst_sel_renew                        solver
% 2.62/0.99  --inst_lit_activity_flag                true
% 2.62/0.99  --inst_restr_to_given                   false
% 2.62/0.99  --inst_activity_threshold               500
% 2.62/0.99  --inst_out_proof                        true
% 2.62/0.99  
% 2.62/0.99  ------ Resolution Options
% 2.62/0.99  
% 2.62/0.99  --resolution_flag                       false
% 2.62/0.99  --res_lit_sel                           adaptive
% 2.62/0.99  --res_lit_sel_side                      none
% 2.62/0.99  --res_ordering                          kbo
% 2.62/0.99  --res_to_prop_solver                    active
% 2.62/0.99  --res_prop_simpl_new                    false
% 2.62/0.99  --res_prop_simpl_given                  true
% 2.62/0.99  --res_passive_queue_type                priority_queues
% 2.62/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.62/0.99  --res_passive_queues_freq               [15;5]
% 2.62/0.99  --res_forward_subs                      full
% 2.62/0.99  --res_backward_subs                     full
% 2.62/0.99  --res_forward_subs_resolution           true
% 2.62/0.99  --res_backward_subs_resolution          true
% 2.62/0.99  --res_orphan_elimination                true
% 2.62/0.99  --res_time_limit                        2.
% 2.62/0.99  --res_out_proof                         true
% 2.62/0.99  
% 2.62/0.99  ------ Superposition Options
% 2.62/0.99  
% 2.62/0.99  --superposition_flag                    true
% 2.62/0.99  --sup_passive_queue_type                priority_queues
% 2.62/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.62/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.62/0.99  --demod_completeness_check              fast
% 2.62/0.99  --demod_use_ground                      true
% 2.62/0.99  --sup_to_prop_solver                    passive
% 2.62/0.99  --sup_prop_simpl_new                    true
% 2.62/0.99  --sup_prop_simpl_given                  true
% 2.62/0.99  --sup_fun_splitting                     false
% 2.62/0.99  --sup_smt_interval                      50000
% 2.62/0.99  
% 2.62/0.99  ------ Superposition Simplification Setup
% 2.62/0.99  
% 2.62/0.99  --sup_indices_passive                   []
% 2.62/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.62/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.99  --sup_full_bw                           [BwDemod]
% 2.62/0.99  --sup_immed_triv                        [TrivRules]
% 2.62/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.62/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.99  --sup_immed_bw_main                     []
% 2.62/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.62/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/0.99  
% 2.62/0.99  ------ Combination Options
% 2.62/0.99  
% 2.62/0.99  --comb_res_mult                         3
% 2.62/0.99  --comb_sup_mult                         2
% 2.62/0.99  --comb_inst_mult                        10
% 2.62/0.99  
% 2.62/0.99  ------ Debug Options
% 2.62/0.99  
% 2.62/0.99  --dbg_backtrace                         false
% 2.62/0.99  --dbg_dump_prop_clauses                 false
% 2.62/0.99  --dbg_dump_prop_clauses_file            -
% 2.62/0.99  --dbg_out_stat                          false
% 2.62/0.99  
% 2.62/0.99  
% 2.62/0.99  
% 2.62/0.99  
% 2.62/0.99  ------ Proving...
% 2.62/0.99  
% 2.62/0.99  
% 2.62/0.99  % SZS status Theorem for theBenchmark.p
% 2.62/0.99  
% 2.62/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.62/0.99  
% 2.62/0.99  fof(f19,conjecture,(
% 2.62/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 2.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f20,negated_conjecture,(
% 2.62/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 2.62/0.99    inference(negated_conjecture,[],[f19])).
% 2.62/0.99  
% 2.62/0.99  fof(f35,plain,(
% 2.62/0.99    ? [X0] : (? [X1] : (? [X2] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 2.62/0.99    inference(ennf_transformation,[],[f20])).
% 2.62/0.99  
% 2.62/0.99  fof(f36,plain,(
% 2.62/0.99    ? [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 2.62/0.99    inference(flattening,[],[f35])).
% 2.62/0.99  
% 2.62/0.99  fof(f43,plain,(
% 2.62/0.99    ( ! [X0,X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.62/0.99    introduced(choice_axiom,[])).
% 2.62/0.99  
% 2.62/0.99  fof(f42,plain,(
% 2.62/0.99    ( ! [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))) )),
% 2.62/0.99    introduced(choice_axiom,[])).
% 2.62/0.99  
% 2.62/0.99  fof(f41,plain,(
% 2.62/0.99    ? [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(sK0) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 2.62/0.99    introduced(choice_axiom,[])).
% 2.62/0.99  
% 2.62/0.99  fof(f44,plain,(
% 2.62/0.99    ((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.62/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f43,f42,f41])).
% 2.62/0.99  
% 2.62/0.99  fof(f74,plain,(
% 2.62/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.62/0.99    inference(cnf_transformation,[],[f44])).
% 2.62/0.99  
% 2.62/0.99  fof(f18,axiom,(
% 2.62/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f34,plain,(
% 2.62/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.62/0.99    inference(ennf_transformation,[],[f18])).
% 2.62/0.99  
% 2.62/0.99  fof(f69,plain,(
% 2.62/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f34])).
% 2.62/0.99  
% 2.62/0.99  fof(f71,plain,(
% 2.62/0.99    l1_struct_0(sK1)),
% 2.62/0.99    inference(cnf_transformation,[],[f44])).
% 2.62/0.99  
% 2.62/0.99  fof(f70,plain,(
% 2.62/0.99    l1_struct_0(sK0)),
% 2.62/0.99    inference(cnf_transformation,[],[f44])).
% 2.62/0.99  
% 2.62/0.99  fof(f12,axiom,(
% 2.62/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f27,plain,(
% 2.62/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/0.99    inference(ennf_transformation,[],[f12])).
% 2.62/0.99  
% 2.62/0.99  fof(f61,plain,(
% 2.62/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.62/0.99    inference(cnf_transformation,[],[f27])).
% 2.62/0.99  
% 2.62/0.99  fof(f4,axiom,(
% 2.62/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f22,plain,(
% 2.62/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.62/0.99    inference(ennf_transformation,[],[f4])).
% 2.62/0.99  
% 2.62/0.99  fof(f39,plain,(
% 2.62/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.62/0.99    inference(nnf_transformation,[],[f22])).
% 2.62/0.99  
% 2.62/0.99  fof(f49,plain,(
% 2.62/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f39])).
% 2.62/0.99  
% 2.62/0.99  fof(f11,axiom,(
% 2.62/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f26,plain,(
% 2.62/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/0.99    inference(ennf_transformation,[],[f11])).
% 2.62/0.99  
% 2.62/0.99  fof(f59,plain,(
% 2.62/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.62/0.99    inference(cnf_transformation,[],[f26])).
% 2.62/0.99  
% 2.62/0.99  fof(f8,axiom,(
% 2.62/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 2.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f24,plain,(
% 2.62/0.99    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.62/0.99    inference(ennf_transformation,[],[f8])).
% 2.62/0.99  
% 2.62/0.99  fof(f25,plain,(
% 2.62/0.99    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.62/0.99    inference(flattening,[],[f24])).
% 2.62/0.99  
% 2.62/0.99  fof(f55,plain,(
% 2.62/0.99    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f25])).
% 2.62/0.99  
% 2.62/0.99  fof(f15,axiom,(
% 2.62/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f65,plain,(
% 2.62/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f15])).
% 2.62/0.99  
% 2.62/0.99  fof(f79,plain,(
% 2.62/0.99    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.62/0.99    inference(definition_unfolding,[],[f55,f65])).
% 2.62/0.99  
% 2.62/0.99  fof(f10,axiom,(
% 2.62/0.99    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f57,plain,(
% 2.62/0.99    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.62/0.99    inference(cnf_transformation,[],[f10])).
% 2.62/0.99  
% 2.62/0.99  fof(f82,plain,(
% 2.62/0.99    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 2.62/0.99    inference(definition_unfolding,[],[f57,f65])).
% 2.62/0.99  
% 2.62/0.99  fof(f6,axiom,(
% 2.62/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))))),
% 2.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f23,plain,(
% 2.62/0.99    ! [X0] : (! [X1] : (k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.62/0.99    inference(ennf_transformation,[],[f6])).
% 2.62/0.99  
% 2.62/0.99  fof(f52,plain,(
% 2.62/0.99    ( ! [X0,X1] : (k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f23])).
% 2.62/0.99  
% 2.62/0.99  fof(f7,axiom,(
% 2.62/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f53,plain,(
% 2.62/0.99    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.62/0.99    inference(cnf_transformation,[],[f7])).
% 2.62/0.99  
% 2.62/0.99  fof(f78,plain,(
% 2.62/0.99    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.62/0.99    inference(definition_unfolding,[],[f53,f65])).
% 2.62/0.99  
% 2.62/0.99  fof(f13,axiom,(
% 2.62/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f28,plain,(
% 2.62/0.99    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/0.99    inference(ennf_transformation,[],[f13])).
% 2.62/0.99  
% 2.62/0.99  fof(f62,plain,(
% 2.62/0.99    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.62/0.99    inference(cnf_transformation,[],[f28])).
% 2.62/0.99  
% 2.62/0.99  fof(f76,plain,(
% 2.62/0.99    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0)),
% 2.62/0.99    inference(cnf_transformation,[],[f44])).
% 2.62/0.99  
% 2.62/0.99  fof(f2,axiom,(
% 2.62/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f48,plain,(
% 2.62/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.62/0.99    inference(cnf_transformation,[],[f2])).
% 2.62/0.99  
% 2.62/0.99  fof(f5,axiom,(
% 2.62/0.99    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 2.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f51,plain,(
% 2.62/0.99    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f5])).
% 2.62/0.99  
% 2.62/0.99  fof(f60,plain,(
% 2.62/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.62/0.99    inference(cnf_transformation,[],[f27])).
% 2.62/0.99  
% 2.62/0.99  fof(f14,axiom,(
% 2.62/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f29,plain,(
% 2.62/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.62/0.99    inference(ennf_transformation,[],[f14])).
% 2.62/0.99  
% 2.62/0.99  fof(f30,plain,(
% 2.62/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.62/0.99    inference(flattening,[],[f29])).
% 2.62/0.99  
% 2.62/0.99  fof(f40,plain,(
% 2.62/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.62/0.99    inference(nnf_transformation,[],[f30])).
% 2.62/0.99  
% 2.62/0.99  fof(f63,plain,(
% 2.62/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f40])).
% 2.62/0.99  
% 2.62/0.99  fof(f16,axiom,(
% 2.62/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f31,plain,(
% 2.62/0.99    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.62/0.99    inference(ennf_transformation,[],[f16])).
% 2.62/0.99  
% 2.62/0.99  fof(f32,plain,(
% 2.62/0.99    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.62/0.99    inference(flattening,[],[f31])).
% 2.62/0.99  
% 2.62/0.99  fof(f66,plain,(
% 2.62/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f32])).
% 2.62/0.99  
% 2.62/0.99  fof(f73,plain,(
% 2.62/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.62/0.99    inference(cnf_transformation,[],[f44])).
% 2.62/0.99  
% 2.62/0.99  fof(f72,plain,(
% 2.62/0.99    v1_funct_1(sK2)),
% 2.62/0.99    inference(cnf_transformation,[],[f44])).
% 2.62/0.99  
% 2.62/0.99  fof(f1,axiom,(
% 2.62/0.99    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f37,plain,(
% 2.62/0.99    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.62/0.99    inference(nnf_transformation,[],[f1])).
% 2.62/0.99  
% 2.62/0.99  fof(f38,plain,(
% 2.62/0.99    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.62/0.99    inference(flattening,[],[f37])).
% 2.62/0.99  
% 2.62/0.99  fof(f47,plain,(
% 2.62/0.99    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 2.62/0.99    inference(cnf_transformation,[],[f38])).
% 2.62/0.99  
% 2.62/0.99  fof(f83,plain,(
% 2.62/0.99    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.62/0.99    inference(equality_resolution,[],[f47])).
% 2.62/0.99  
% 2.62/0.99  fof(f17,axiom,(
% 2.62/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 2.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f33,plain,(
% 2.62/0.99    ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.62/0.99    inference(ennf_transformation,[],[f17])).
% 2.62/0.99  
% 2.62/0.99  fof(f68,plain,(
% 2.62/0.99    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.62/0.99    inference(cnf_transformation,[],[f33])).
% 2.62/0.99  
% 2.62/0.99  fof(f9,axiom,(
% 2.62/0.99    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f56,plain,(
% 2.62/0.99    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.62/0.99    inference(cnf_transformation,[],[f9])).
% 2.62/0.99  
% 2.62/0.99  fof(f80,plain,(
% 2.62/0.99    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 2.62/0.99    inference(definition_unfolding,[],[f56,f65])).
% 2.62/0.99  
% 2.62/0.99  fof(f75,plain,(
% 2.62/0.99    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)),
% 2.62/0.99    inference(cnf_transformation,[],[f44])).
% 2.62/0.99  
% 2.62/0.99  fof(f46,plain,(
% 2.62/0.99    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 2.62/0.99    inference(cnf_transformation,[],[f38])).
% 2.62/0.99  
% 2.62/0.99  fof(f84,plain,(
% 2.62/0.99    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 2.62/0.99    inference(equality_resolution,[],[f46])).
% 2.62/0.99  
% 2.62/0.99  fof(f45,plain,(
% 2.62/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 2.62/0.99    inference(cnf_transformation,[],[f38])).
% 2.62/0.99  
% 2.62/0.99  cnf(c_26,negated_conjecture,
% 2.62/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.62/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_778,plain,
% 2.62/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_23,plain,
% 2.62/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.62/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_29,negated_conjecture,
% 2.62/0.99      ( l1_struct_0(sK1) ),
% 2.62/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_273,plain,
% 2.62/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.62/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_29]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_274,plain,
% 2.62/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.62/0.99      inference(unflattening,[status(thm)],[c_273]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_30,negated_conjecture,
% 2.62/0.99      ( l1_struct_0(sK0) ),
% 2.62/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_278,plain,
% 2.62/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.62/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_279,plain,
% 2.62/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.62/0.99      inference(unflattening,[status(thm)],[c_278]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_805,plain,
% 2.62/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.62/0.99      inference(light_normalisation,[status(thm)],[c_778,c_274,c_279]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_15,plain,
% 2.62/0.99      ( v5_relat_1(X0,X1)
% 2.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.62/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_5,plain,
% 2.62/0.99      ( r1_tarski(k2_relat_1(X0),X1)
% 2.62/0.99      | ~ v5_relat_1(X0,X1)
% 2.62/0.99      | ~ v1_relat_1(X0) ),
% 2.62/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_285,plain,
% 2.62/0.99      ( r1_tarski(k2_relat_1(X0),X1)
% 2.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.62/0.99      | ~ v1_relat_1(X0) ),
% 2.62/0.99      inference(resolution,[status(thm)],[c_15,c_5]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_14,plain,
% 2.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/0.99      | v1_relat_1(X0) ),
% 2.62/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_295,plain,
% 2.62/0.99      ( r1_tarski(k2_relat_1(X0),X1)
% 2.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.62/0.99      inference(forward_subsumption_resolution,
% 2.62/0.99                [status(thm)],
% 2.62/0.99                [c_285,c_14]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_10,plain,
% 2.62/0.99      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.62/0.99      | ~ v1_relat_1(X0)
% 2.62/0.99      | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
% 2.62/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_305,plain,
% 2.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/0.99      | ~ v1_relat_1(X0)
% 2.62/0.99      | k5_relat_1(X0,k6_partfun1(X2)) = X0 ),
% 2.62/0.99      inference(resolution,[status(thm)],[c_295,c_10]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_309,plain,
% 2.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/0.99      | k5_relat_1(X0,k6_partfun1(X2)) = X0 ),
% 2.62/0.99      inference(global_propositional_subsumption,
% 2.62/0.99                [status(thm)],
% 2.62/0.99                [c_305,c_14]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_777,plain,
% 2.62/0.99      ( k5_relat_1(X0,k6_partfun1(X1)) = X0
% 2.62/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_309]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1071,plain,
% 2.62/0.99      ( k5_relat_1(sK2,k6_partfun1(k2_struct_0(sK1))) = sK2 ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_805,c_777]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_13,plain,
% 2.62/0.99      ( v1_relat_1(k6_partfun1(X0)) ),
% 2.62/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_782,plain,
% 2.62/0.99      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_781,plain,
% 2.62/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.62/0.99      | v1_relat_1(X0) = iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1519,plain,
% 2.62/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_805,c_781]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_7,plain,
% 2.62/0.99      ( ~ v1_relat_1(X0)
% 2.62/0.99      | ~ v1_relat_1(X1)
% 2.62/0.99      | k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0)) ),
% 2.62/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_783,plain,
% 2.62/0.99      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
% 2.62/0.99      | v1_relat_1(X1) != iProver_top
% 2.62/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2662,plain,
% 2.62/0.99      ( k1_relat_1(k5_relat_1(sK2,X0)) = k10_relat_1(sK2,k1_relat_1(X0))
% 2.62/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_1519,c_783]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3041,plain,
% 2.62/0.99      ( k1_relat_1(k5_relat_1(sK2,k6_partfun1(X0))) = k10_relat_1(sK2,k1_relat_1(k6_partfun1(X0))) ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_782,c_2662]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_9,plain,
% 2.62/0.99      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 2.62/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3050,plain,
% 2.62/0.99      ( k1_relat_1(k5_relat_1(sK2,k6_partfun1(X0))) = k10_relat_1(sK2,X0) ),
% 2.62/0.99      inference(light_normalisation,[status(thm)],[c_3041,c_9]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3433,plain,
% 2.62/0.99      ( k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2) ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_1071,c_3050]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_17,plain,
% 2.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/0.99      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.62/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_780,plain,
% 2.62/0.99      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 2.62/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2466,plain,
% 2.62/0.99      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0) ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_805,c_780]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_24,negated_conjecture,
% 2.62/0.99      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
% 2.62/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_812,plain,
% 2.62/0.99      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
% 2.62/0.99      inference(light_normalisation,[status(thm)],[c_24,c_274,c_279]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2494,plain,
% 2.62/0.99      ( k10_relat_1(sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
% 2.62/0.99      inference(demodulation,[status(thm)],[c_2466,c_812]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3688,plain,
% 2.62/0.99      ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 2.62/0.99      inference(demodulation,[status(thm)],[c_3433,c_2494]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_536,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1000,plain,
% 2.62/0.99      ( X0 != X1 | k2_struct_0(sK0) != X1 | k2_struct_0(sK0) = X0 ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_536]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3584,plain,
% 2.62/0.99      ( k8_relset_1(X0,X1,X2,X3) != X4
% 2.62/0.99      | k2_struct_0(sK0) != X4
% 2.62/0.99      | k2_struct_0(sK0) = k8_relset_1(X0,X1,X2,X3) ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_1000]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3585,plain,
% 2.62/0.99      ( k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.62/0.99      | k2_struct_0(sK0) = k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 2.62/0.99      | k2_struct_0(sK0) != k1_xboole_0 ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_3584]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3,plain,
% 2.62/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.62/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_784,plain,
% 2.62/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2465,plain,
% 2.62/0.99      ( k8_relset_1(X0,X1,k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,X2) ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_784,c_780]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_6,plain,
% 2.62/0.99      ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.62/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2485,plain,
% 2.62/0.99      ( k8_relset_1(X0,X1,k1_xboole_0,X2) = k1_xboole_0 ),
% 2.62/0.99      inference(demodulation,[status(thm)],[c_2465,c_6]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_16,plain,
% 2.62/0.99      ( v4_relat_1(X0,X1)
% 2.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.62/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_19,plain,
% 2.62/0.99      ( ~ v1_partfun1(X0,X1)
% 2.62/0.99      | ~ v4_relat_1(X0,X1)
% 2.62/0.99      | ~ v1_relat_1(X0)
% 2.62/0.99      | k1_relat_1(X0) = X1 ),
% 2.62/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_325,plain,
% 2.62/0.99      ( ~ v1_partfun1(X0,X1)
% 2.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/0.99      | ~ v1_relat_1(X0)
% 2.62/0.99      | k1_relat_1(X0) = X1 ),
% 2.62/0.99      inference(resolution,[status(thm)],[c_16,c_19]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_329,plain,
% 2.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/0.99      | ~ v1_partfun1(X0,X1)
% 2.62/0.99      | k1_relat_1(X0) = X1 ),
% 2.62/0.99      inference(global_propositional_subsumption,
% 2.62/0.99                [status(thm)],
% 2.62/0.99                [c_325,c_19,c_16,c_14]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_330,plain,
% 2.62/0.99      ( ~ v1_partfun1(X0,X1)
% 2.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/0.99      | k1_relat_1(X0) = X1 ),
% 2.62/0.99      inference(renaming,[status(thm)],[c_329]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_21,plain,
% 2.62/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.62/0.99      | v1_partfun1(X0,X1)
% 2.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/0.99      | ~ v1_funct_1(X0)
% 2.62/0.99      | k1_xboole_0 = X2 ),
% 2.62/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_27,negated_conjecture,
% 2.62/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.62/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_386,plain,
% 2.62/0.99      ( v1_partfun1(X0,X1)
% 2.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/0.99      | ~ v1_funct_1(X0)
% 2.62/0.99      | u1_struct_0(sK1) != X2
% 2.62/0.99      | u1_struct_0(sK0) != X1
% 2.62/0.99      | sK2 != X0
% 2.62/0.99      | k1_xboole_0 = X2 ),
% 2.62/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_387,plain,
% 2.62/0.99      ( v1_partfun1(sK2,u1_struct_0(sK0))
% 2.62/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.62/0.99      | ~ v1_funct_1(sK2)
% 2.62/0.99      | k1_xboole_0 = u1_struct_0(sK1) ),
% 2.62/0.99      inference(unflattening,[status(thm)],[c_386]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_28,negated_conjecture,
% 2.62/0.99      ( v1_funct_1(sK2) ),
% 2.62/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_389,plain,
% 2.62/0.99      ( v1_partfun1(sK2,u1_struct_0(sK0))
% 2.62/0.99      | k1_xboole_0 = u1_struct_0(sK1) ),
% 2.62/0.99      inference(global_propositional_subsumption,
% 2.62/0.99                [status(thm)],
% 2.62/0.99                [c_387,c_28,c_26]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_427,plain,
% 2.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/0.99      | u1_struct_0(sK1) = k1_xboole_0
% 2.62/0.99      | u1_struct_0(sK0) != X1
% 2.62/0.99      | k1_relat_1(X0) = X1
% 2.62/0.99      | sK2 != X0 ),
% 2.62/0.99      inference(resolution_lifted,[status(thm)],[c_330,c_389]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_428,plain,
% 2.62/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
% 2.62/0.99      | u1_struct_0(sK1) = k1_xboole_0
% 2.62/0.99      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 2.62/0.99      inference(unflattening,[status(thm)],[c_427]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_531,plain,
% 2.62/0.99      ( sP0_iProver_split
% 2.62/0.99      | u1_struct_0(sK1) = k1_xboole_0
% 2.62/0.99      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 2.62/0.99      inference(splitting,
% 2.62/0.99                [splitting(split),new_symbols(definition,[])],
% 2.62/0.99                [c_428]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_773,plain,
% 2.62/0.99      ( u1_struct_0(sK1) = k1_xboole_0
% 2.62/0.99      | k1_relat_1(sK2) = u1_struct_0(sK0)
% 2.62/0.99      | sP0_iProver_split = iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_531]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_815,plain,
% 2.62/0.99      ( k2_struct_0(sK1) = k1_xboole_0
% 2.62/0.99      | k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.62/0.99      | sP0_iProver_split = iProver_top ),
% 2.62/0.99      inference(demodulation,[status(thm)],[c_773,c_274,c_279]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_879,plain,
% 2.62/0.99      ( sP0_iProver_split
% 2.62/0.99      | k2_struct_0(sK1) = k1_xboole_0
% 2.62/0.99      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.62/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_815]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_530,plain,
% 2.62/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
% 2.62/0.99      | ~ sP0_iProver_split ),
% 2.62/0.99      inference(splitting,
% 2.62/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.62/0.99                [c_428]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_898,plain,
% 2.62/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.62/0.99      | ~ sP0_iProver_split ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_530]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_964,plain,
% 2.62/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.62/0.99      | k2_struct_0(sK1) = k1_xboole_0 ),
% 2.62/0.99      inference(global_propositional_subsumption,
% 2.62/0.99                [status(thm)],
% 2.62/0.99                [c_815,c_26,c_879,c_898]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_965,plain,
% 2.62/0.99      ( k2_struct_0(sK1) = k1_xboole_0
% 2.62/0.99      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.62/0.99      inference(renaming,[status(thm)],[c_964]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_968,plain,
% 2.62/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.62/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) = iProver_top ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_965,c_805]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_0,plain,
% 2.62/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.62/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1419,plain,
% 2.62/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.62/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.62/0.99      inference(demodulation,[status(thm)],[c_968,c_0]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_22,plain,
% 2.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.62/0.99      | k8_relset_1(X1,X1,k6_partfun1(X1),X0) = X0 ),
% 2.62/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_779,plain,
% 2.62/0.99      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
% 2.62/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2215,plain,
% 2.62/0.99      ( k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2) = sK2
% 2.62/0.99      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_1419,c_779]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_11,plain,
% 2.62/0.99      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 2.62/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2223,plain,
% 2.62/0.99      ( k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2) = sK2
% 2.62/0.99      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.62/0.99      inference(light_normalisation,[status(thm)],[c_2215,c_11]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2567,plain,
% 2.62/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2) | sK2 = k1_xboole_0 ),
% 2.62/0.99      inference(demodulation,[status(thm)],[c_2485,c_2223]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2213,plain,
% 2.62/0.99      ( k8_relset_1(X0,X0,k6_partfun1(X0),k1_xboole_0) = k1_xboole_0 ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_784,c_779]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2411,plain,
% 2.62/0.99      ( k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_11,c_2213]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_546,plain,
% 2.62/0.99      ( X0 != X1
% 2.62/0.99      | X2 != X3
% 2.62/0.99      | X4 != X5
% 2.62/0.99      | X6 != X7
% 2.62/0.99      | k8_relset_1(X0,X2,X4,X6) = k8_relset_1(X1,X3,X5,X7) ),
% 2.62/0.99      theory(equality) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2354,plain,
% 2.62/0.99      ( X0 != u1_struct_0(sK1)
% 2.62/0.99      | X1 != u1_struct_0(sK0)
% 2.62/0.99      | X2 != k2_struct_0(sK1)
% 2.62/0.99      | X3 != sK2
% 2.62/0.99      | k8_relset_1(X1,X0,X3,X2) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_546]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2356,plain,
% 2.62/0.99      ( k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
% 2.62/0.99      | k1_xboole_0 != u1_struct_0(sK1)
% 2.62/0.99      | k1_xboole_0 != u1_struct_0(sK0)
% 2.62/0.99      | k1_xboole_0 != k2_struct_0(sK1)
% 2.62/0.99      | k1_xboole_0 != sK2 ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_2354]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1224,plain,
% 2.62/0.99      ( X0 != X1
% 2.62/0.99      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != X1
% 2.62/0.99      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = X0 ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_536]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1495,plain,
% 2.62/0.99      ( X0 != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
% 2.62/0.99      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = X0
% 2.62/0.99      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_1224]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2353,plain,
% 2.62/0.99      ( k8_relset_1(X0,X1,X2,X3) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
% 2.62/0.99      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k8_relset_1(X0,X1,X2,X3)
% 2.62/0.99      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_1495]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2355,plain,
% 2.62/0.99      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
% 2.62/0.99      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 2.62/0.99      | k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_2353]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1278,plain,
% 2.62/0.99      ( u1_struct_0(X0) != X1
% 2.62/0.99      | k1_xboole_0 != X1
% 2.62/0.99      | k1_xboole_0 = u1_struct_0(X0) ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_536]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1925,plain,
% 2.62/0.99      ( u1_struct_0(sK1) != k2_struct_0(sK1)
% 2.62/0.99      | k1_xboole_0 = u1_struct_0(sK1)
% 2.62/0.99      | k1_xboole_0 != k2_struct_0(sK1) ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_1278]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1270,plain,
% 2.62/0.99      ( u1_struct_0(sK0) != X0
% 2.62/0.99      | k1_xboole_0 != X0
% 2.62/0.99      | k1_xboole_0 = u1_struct_0(sK0) ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_536]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1863,plain,
% 2.62/0.99      ( u1_struct_0(sK0) != k2_struct_0(sK0)
% 2.62/0.99      | k1_xboole_0 = u1_struct_0(sK0)
% 2.62/0.99      | k1_xboole_0 != k2_struct_0(sK0) ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_1270]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_933,plain,
% 2.62/0.99      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != X0
% 2.62/0.99      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k2_struct_0(sK0)
% 2.62/0.99      | k2_struct_0(sK0) != X0 ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_536]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1225,plain,
% 2.62/0.99      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k8_relset_1(X0,X1,X2,X3)
% 2.62/0.99      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k2_struct_0(sK0)
% 2.62/0.99      | k2_struct_0(sK0) != k8_relset_1(X0,X1,X2,X3) ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_933]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1227,plain,
% 2.62/0.99      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 2.62/0.99      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k2_struct_0(sK0)
% 2.62/0.99      | k2_struct_0(sK0) != k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_1225]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_535,plain,( X0 = X0 ),theory(equality) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1223,plain,
% 2.62/0.99      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_535]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1077,plain,
% 2.62/0.99      ( k2_struct_0(sK0) != X0
% 2.62/0.99      | k1_xboole_0 != X0
% 2.62/0.99      | k1_xboole_0 = k2_struct_0(sK0) ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_536]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1078,plain,
% 2.62/0.99      ( k2_struct_0(sK0) != k1_xboole_0
% 2.62/0.99      | k1_xboole_0 = k2_struct_0(sK0)
% 2.62/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_1077]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1044,plain,
% 2.62/0.99      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_536]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1045,plain,
% 2.62/0.99      ( sK2 != k1_xboole_0
% 2.62/0.99      | k1_xboole_0 = sK2
% 2.62/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_1044]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_25,negated_conjecture,
% 2.62/0.99      ( k1_xboole_0 != k2_struct_0(sK1)
% 2.62/0.99      | k1_xboole_0 = k2_struct_0(sK0) ),
% 2.62/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_971,plain,
% 2.62/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.62/0.99      | k2_struct_0(sK0) = k1_xboole_0 ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_965,c_25]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_935,plain,
% 2.62/0.99      ( k2_struct_0(sK1) != X0
% 2.62/0.99      | k1_xboole_0 != X0
% 2.62/0.99      | k1_xboole_0 = k2_struct_0(sK1) ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_536]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_936,plain,
% 2.62/0.99      ( k2_struct_0(sK1) != k1_xboole_0
% 2.62/0.99      | k1_xboole_0 = k2_struct_0(sK1)
% 2.62/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_935]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1,plain,
% 2.62/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.62/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_91,plain,
% 2.62/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2,plain,
% 2.62/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.62/0.99      | k1_xboole_0 = X1
% 2.62/0.99      | k1_xboole_0 = X0 ),
% 2.62/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_90,plain,
% 2.62/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.62/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(contradiction,plain,
% 2.62/0.99      ( $false ),
% 2.62/0.99      inference(minisat,
% 2.62/0.99                [status(thm)],
% 2.62/0.99                [c_3688,c_3585,c_2567,c_2411,c_2356,c_2355,c_1925,c_1863,
% 2.62/0.99                 c_1227,c_1223,c_1078,c_1045,c_971,c_965,c_936,c_279,
% 2.62/0.99                 c_274,c_91,c_90,c_24]) ).
% 2.62/0.99  
% 2.62/0.99  
% 2.62/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.62/0.99  
% 2.62/0.99  ------                               Statistics
% 2.62/0.99  
% 2.62/0.99  ------ General
% 2.62/0.99  
% 2.62/0.99  abstr_ref_over_cycles:                  0
% 2.62/0.99  abstr_ref_under_cycles:                 0
% 2.62/0.99  gc_basic_clause_elim:                   0
% 2.62/0.99  forced_gc_time:                         0
% 2.62/0.99  parsing_time:                           0.01
% 2.62/0.99  unif_index_cands_time:                  0.
% 2.62/0.99  unif_index_add_time:                    0.
% 2.62/0.99  orderings_time:                         0.
% 2.62/0.99  out_proof_time:                         0.01
% 2.62/0.99  total_time:                             0.158
% 2.62/0.99  num_of_symbols:                         56
% 2.62/0.99  num_of_terms:                           4444
% 2.62/0.99  
% 2.62/0.99  ------ Preprocessing
% 2.62/0.99  
% 2.62/0.99  num_of_splits:                          2
% 2.62/0.99  num_of_split_atoms:                     2
% 2.62/0.99  num_of_reused_defs:                     0
% 2.62/0.99  num_eq_ax_congr_red:                    8
% 2.62/0.99  num_of_sem_filtered_clauses:            1
% 2.62/0.99  num_of_subtypes:                        0
% 2.62/0.99  monotx_restored_types:                  0
% 2.62/0.99  sat_num_of_epr_types:                   0
% 2.62/0.99  sat_num_of_non_cyclic_types:            0
% 2.62/0.99  sat_guarded_non_collapsed_types:        0
% 2.62/0.99  num_pure_diseq_elim:                    0
% 2.62/0.99  simp_replaced_by:                       0
% 2.62/0.99  res_preprocessed:                       127
% 2.62/0.99  prep_upred:                             0
% 2.62/0.99  prep_unflattend:                        15
% 2.62/0.99  smt_new_axioms:                         0
% 2.62/0.99  pred_elim_cands:                        2
% 2.62/0.99  pred_elim:                              7
% 2.62/0.99  pred_elim_cl:                           10
% 2.62/0.99  pred_elim_cycles:                       9
% 2.62/0.99  merged_defs:                            0
% 2.62/0.99  merged_defs_ncl:                        0
% 2.62/0.99  bin_hyper_res:                          0
% 2.62/0.99  prep_cycles:                            4
% 2.62/0.99  pred_elim_time:                         0.004
% 2.62/0.99  splitting_time:                         0.
% 2.62/0.99  sem_filter_time:                        0.
% 2.62/0.99  monotx_time:                            0.
% 2.62/0.99  subtype_inf_time:                       0.
% 2.62/0.99  
% 2.62/0.99  ------ Problem properties
% 2.62/0.99  
% 2.62/0.99  clauses:                                23
% 2.62/0.99  conjectures:                            3
% 2.62/0.99  epr:                                    0
% 2.62/0.99  horn:                                   20
% 2.62/0.99  ground:                                 8
% 2.62/0.99  unary:                                  12
% 2.62/0.99  binary:                                 7
% 2.62/0.99  lits:                                   39
% 2.62/0.99  lits_eq:                                22
% 2.62/0.99  fd_pure:                                0
% 2.62/0.99  fd_pseudo:                              0
% 2.62/0.99  fd_cond:                                1
% 2.62/0.99  fd_pseudo_cond:                         0
% 2.62/0.99  ac_symbols:                             0
% 2.62/0.99  
% 2.62/0.99  ------ Propositional Solver
% 2.62/0.99  
% 2.62/0.99  prop_solver_calls:                      27
% 2.62/0.99  prop_fast_solver_calls:                 638
% 2.62/0.99  smt_solver_calls:                       0
% 2.62/0.99  smt_fast_solver_calls:                  0
% 2.62/0.99  prop_num_of_clauses:                    1584
% 2.62/0.99  prop_preprocess_simplified:             5634
% 2.62/0.99  prop_fo_subsumed:                       7
% 2.62/0.99  prop_solver_time:                       0.
% 2.62/0.99  smt_solver_time:                        0.
% 2.62/0.99  smt_fast_solver_time:                   0.
% 2.62/0.99  prop_fast_solver_time:                  0.
% 2.62/0.99  prop_unsat_core_time:                   0.
% 2.62/0.99  
% 2.62/0.99  ------ QBF
% 2.62/0.99  
% 2.62/0.99  qbf_q_res:                              0
% 2.62/0.99  qbf_num_tautologies:                    0
% 2.62/0.99  qbf_prep_cycles:                        0
% 2.62/0.99  
% 2.62/0.99  ------ BMC1
% 2.62/0.99  
% 2.62/0.99  bmc1_current_bound:                     -1
% 2.62/0.99  bmc1_last_solved_bound:                 -1
% 2.62/0.99  bmc1_unsat_core_size:                   -1
% 2.62/0.99  bmc1_unsat_core_parents_size:           -1
% 2.62/0.99  bmc1_merge_next_fun:                    0
% 2.62/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.62/0.99  
% 2.62/0.99  ------ Instantiation
% 2.62/0.99  
% 2.62/0.99  inst_num_of_clauses:                    749
% 2.62/0.99  inst_num_in_passive:                    361
% 2.62/0.99  inst_num_in_active:                     294
% 2.62/0.99  inst_num_in_unprocessed:                94
% 2.62/0.99  inst_num_of_loops:                      320
% 2.62/0.99  inst_num_of_learning_restarts:          0
% 2.62/0.99  inst_num_moves_active_passive:          25
% 2.62/0.99  inst_lit_activity:                      0
% 2.62/0.99  inst_lit_activity_moves:                0
% 2.62/0.99  inst_num_tautologies:                   0
% 2.62/0.99  inst_num_prop_implied:                  0
% 2.62/0.99  inst_num_existing_simplified:           0
% 2.62/0.99  inst_num_eq_res_simplified:             0
% 2.62/0.99  inst_num_child_elim:                    0
% 2.62/0.99  inst_num_of_dismatching_blockings:      104
% 2.62/0.99  inst_num_of_non_proper_insts:           478
% 2.62/0.99  inst_num_of_duplicates:                 0
% 2.62/0.99  inst_inst_num_from_inst_to_res:         0
% 2.62/0.99  inst_dismatching_checking_time:         0.
% 2.62/0.99  
% 2.62/0.99  ------ Resolution
% 2.62/0.99  
% 2.62/0.99  res_num_of_clauses:                     0
% 2.62/0.99  res_num_in_passive:                     0
% 2.62/0.99  res_num_in_active:                      0
% 2.62/0.99  res_num_of_loops:                       131
% 2.62/0.99  res_forward_subset_subsumed:            35
% 2.62/0.99  res_backward_subset_subsumed:           4
% 2.62/0.99  res_forward_subsumed:                   0
% 2.62/0.99  res_backward_subsumed:                  0
% 2.62/0.99  res_forward_subsumption_resolution:     2
% 2.62/0.99  res_backward_subsumption_resolution:    0
% 2.62/0.99  res_clause_to_clause_subsumption:       79
% 2.62/0.99  res_orphan_elimination:                 0
% 2.62/0.99  res_tautology_del:                      29
% 2.62/0.99  res_num_eq_res_simplified:              0
% 2.62/0.99  res_num_sel_changes:                    0
% 2.62/0.99  res_moves_from_active_to_pass:          0
% 2.62/0.99  
% 2.62/0.99  ------ Superposition
% 2.62/0.99  
% 2.62/0.99  sup_time_total:                         0.
% 2.62/0.99  sup_time_generating:                    0.
% 2.62/0.99  sup_time_sim_full:                      0.
% 2.62/0.99  sup_time_sim_immed:                     0.
% 2.62/0.99  
% 2.62/0.99  sup_num_of_clauses:                     69
% 2.62/0.99  sup_num_in_active:                      59
% 2.62/0.99  sup_num_in_passive:                     10
% 2.62/0.99  sup_num_of_loops:                       62
% 2.62/0.99  sup_fw_superposition:                   65
% 2.62/0.99  sup_bw_superposition:                   22
% 2.62/0.99  sup_immediate_simplified:               22
% 2.62/0.99  sup_given_eliminated:                   0
% 2.62/0.99  comparisons_done:                       0
% 2.62/0.99  comparisons_avoided:                    30
% 2.62/0.99  
% 2.62/0.99  ------ Simplifications
% 2.62/0.99  
% 2.62/0.99  
% 2.62/0.99  sim_fw_subset_subsumed:                 9
% 2.62/0.99  sim_bw_subset_subsumed:                 0
% 2.62/0.99  sim_fw_subsumed:                        0
% 2.62/0.99  sim_bw_subsumed:                        1
% 2.62/0.99  sim_fw_subsumption_res:                 1
% 2.62/0.99  sim_bw_subsumption_res:                 0
% 2.62/0.99  sim_tautology_del:                      2
% 2.62/0.99  sim_eq_tautology_del:                   5
% 2.62/0.99  sim_eq_res_simp:                        0
% 2.62/0.99  sim_fw_demodulated:                     8
% 2.62/0.99  sim_bw_demodulated:                     3
% 2.62/0.99  sim_light_normalised:                   12
% 2.62/0.99  sim_joinable_taut:                      0
% 2.62/0.99  sim_joinable_simp:                      0
% 2.62/0.99  sim_ac_normalised:                      0
% 2.62/0.99  sim_smt_subsumption:                    0
% 2.62/0.99  
%------------------------------------------------------------------------------
