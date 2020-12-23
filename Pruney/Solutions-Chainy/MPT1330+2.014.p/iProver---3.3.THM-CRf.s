%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:55 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :  186 (3344 expanded)
%              Number of clauses        :  134 (1119 expanded)
%              Number of leaves         :   19 ( 896 expanded)
%              Depth                    :   24
%              Number of atoms          :  541 (18644 expanded)
%              Number of equality atoms :  310 (7466 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f31,plain,(
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

fof(f30,plain,(
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

fof(f29,plain,
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

fof(f32,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0)
    & ( k1_xboole_0 = k2_struct_0(sK0)
      | k1_xboole_0 != k2_struct_0(sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f31,f30,f29])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
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

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f45])).

fof(f50,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_411,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_412,plain,
    ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_551,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
    | k8_relset_1(X0_50,X1_50,sK2,X2_50) = k10_relat_1(sK2,X2_50) ),
    inference(subtyping,[status(esa)],[c_412])).

cnf(c_13,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_20,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_231,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_232,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_231])).

cnf(c_553,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_232])).

cnf(c_19,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_226,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_227,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_226])).

cnf(c_554,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_227])).

cnf(c_719,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
    | k8_relset_1(X0_50,X1_50,sK2,X2_50) = k10_relat_1(sK2,X2_50) ),
    inference(light_normalisation,[status(thm)],[c_551,c_553,c_554])).

cnf(c_1025,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0_50) = k10_relat_1(sK2,X0_50) ),
    inference(equality_resolution,[status(thm)],[c_719])).

cnf(c_14,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_556,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_680,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_556,c_553,c_554])).

cnf(c_1169,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_1025,c_680])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_239,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | X1 != X2
    | k3_xboole_0(X3,X2) = X3
    | k2_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_2])).

cnf(c_240,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k3_xboole_0(k2_relat_1(X0),X1) = k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_239])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_258,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4
    | k3_xboole_0(k2_relat_1(X3),X4) = k2_relat_1(X3) ),
    inference(resolution_lifted,[status(thm)],[c_240,c_6])).

cnf(c_259,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k3_xboole_0(k2_relat_1(X0),X2) = k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_258])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_263,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k3_xboole_0(k2_relat_1(X0),X2) = k2_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_259,c_5])).

cnf(c_402,plain,
    ( k3_xboole_0(k2_relat_1(X0),X1) = k2_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_263,c_16])).

cnf(c_403,plain,
    ( k3_xboole_0(k2_relat_1(sK2),X0) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_552,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
    | k3_xboole_0(k2_relat_1(sK2),X1_50) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_403])).

cnf(c_709,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
    | k3_xboole_0(k2_relat_1(sK2),X1_50) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_552,c_553,c_554])).

cnf(c_833,plain,
    ( k3_xboole_0(k2_relat_1(sK2),k2_struct_0(sK1)) = k2_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_709])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_420,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_16])).

cnf(c_421,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_487,plain,
    ( k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_421])).

cnf(c_488,plain,
    ( k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0)) = k10_relat_1(sK2,X0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_549,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
    | k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X2_50)) = k10_relat_1(sK2,X2_50) ),
    inference(subtyping,[status(esa)],[c_488])).

cnf(c_557,plain,
    ( k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0_50)) = k10_relat_1(sK2,X0_50)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_549])).

cnf(c_663,plain,
    ( k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0_50)) = k10_relat_1(sK2,X0_50)
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_557])).

cnf(c_559,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_549])).

cnf(c_565,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_758,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_565])).

cnf(c_558,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_549])).

cnf(c_793,plain,
    ( ~ sP1_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_558])).

cnf(c_841,plain,
    ( k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0_50)) = k10_relat_1(sK2,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_663,c_559,c_557,c_758,c_793])).

cnf(c_1147,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_833,c_841])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_478,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_421])).

cnf(c_479,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_550,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
    | k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_479])).

cnf(c_714,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
    | k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_550,c_553,c_554])).

cnf(c_794,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_974,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_714,c_758,c_794])).

cnf(c_1149,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1147,c_974])).

cnf(c_1170,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1169,c_1149])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_17,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_349,plain,
    ( v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK0) != k1_xboole_0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_350,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | u1_struct_0(sK0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_352,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | v1_partfun1(sK2,k1_xboole_0)
    | u1_struct_0(sK0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_350,c_18])).

cnf(c_353,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | u1_struct_0(sK0) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_352])).

cnf(c_444,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | u1_struct_0(sK0) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_353])).

cnf(c_7,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_10,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_279,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_7,c_10])).

cnf(c_283,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_279,c_10,c_7,c_5])).

cnf(c_284,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_283])).

cnf(c_387,plain,
    ( ~ v1_partfun1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | k1_relat_1(X0) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_284,c_16])).

cnf(c_388,plain,
    ( ~ v1_partfun1(sK2,X0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_relat_1(sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_500,plain,
    ( u1_struct_0(sK0) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | k1_relat_1(sK2) = X0
    | sK2 != sK2
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_444,c_388])).

cnf(c_501,plain,
    ( u1_struct_0(sK0) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_548,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_50))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | u1_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_501])).

cnf(c_561,plain,
    ( sP2_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | u1_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_548])).

cnf(c_664,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | u1_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0
    | sP2_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_561])).

cnf(c_724,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))
    | k2_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0
    | sP2_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_664,c_553,c_554])).

cnf(c_560,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_50))
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_548])).

cnf(c_665,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_50))
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_560])).

cnf(c_699,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_50))
    | sP2_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_665,c_553,c_554])).

cnf(c_729,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))
    | k2_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_724,c_699])).

cnf(c_564,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_579,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_592,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
    | u1_struct_0(sK0) != k1_xboole_0
    | k1_relat_1(sK2) = k1_xboole_0
    | sP2_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_561])).

cnf(c_593,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_50))
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_560])).

cnf(c_595,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | sP2_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_593])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_366,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_367,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_369,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_367,c_18,c_16])).

cnf(c_515,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) != X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_relat_1(sK2) = X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_369,c_388])).

cnf(c_516,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_515])).

cnf(c_547,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0_50))
    | u1_struct_0(sK1) = k1_xboole_0
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_516])).

cnf(c_563,plain,
    ( sP3_iProver_split
    | u1_struct_0(sK1) = k1_xboole_0
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_547])).

cnf(c_596,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | k1_relat_1(sK2) = u1_struct_0(sK0)
    | sP3_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_563])).

cnf(c_562,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0_50))
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_547])).

cnf(c_759,plain,
    ( ~ sP3_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_562])).

cnf(c_760,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_759])).

cnf(c_572,plain,
    ( X0_53 != X1_53
    | k1_zfmisc_1(X0_53) = k1_zfmisc_1(X1_53) ),
    theory(equality)).

cnf(c_765,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) != k2_zfmisc_1(X0_50,X1_50)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)) ),
    inference(instantiation,[status(thm)],[c_572])).

cnf(c_766,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_765])).

cnf(c_571,plain,
    ( k2_zfmisc_1(X0_50,X1_50) = k2_zfmisc_1(X2_50,X3_50)
    | X0_50 != X2_50
    | X1_50 != X3_50 ),
    theory(equality)).

cnf(c_783,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = k2_zfmisc_1(X0_50,X1_50)
    | u1_struct_0(sK1) != X1_50
    | u1_struct_0(sK0) != X0_50 ),
    inference(instantiation,[status(thm)],[c_571])).

cnf(c_784,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | u1_struct_0(sK1) != k1_xboole_0
    | u1_struct_0(sK0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_783])).

cnf(c_567,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_767,plain,
    ( u1_struct_0(sK0) != X0_50
    | u1_struct_0(sK0) = k1_xboole_0
    | k1_xboole_0 != X0_50 ),
    inference(instantiation,[status(thm)],[c_567])).

cnf(c_812,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | u1_struct_0(sK0) = k1_xboole_0
    | k1_xboole_0 != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_767])).

cnf(c_835,plain,
    ( k2_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_666,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | k1_relat_1(sK2) = u1_struct_0(sK0)
    | sP3_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_563])).

cnf(c_683,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | sP3_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_666,c_553,c_554])).

cnf(c_733,plain,
    ( sP3_iProver_split
    | k2_struct_0(sK1) = k1_xboole_0
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_683])).

cnf(c_846,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_683,c_733,c_758,c_759])).

cnf(c_847,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(renaming,[status(thm)],[c_846])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_555,negated_conjecture,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_854,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_847,c_555])).

cnf(c_781,plain,
    ( X0_50 != X1_50
    | k2_struct_0(sK0) != X1_50
    | k2_struct_0(sK0) = X0_50 ),
    inference(instantiation,[status(thm)],[c_567])).

cnf(c_834,plain,
    ( X0_50 != k2_struct_0(sK0)
    | k2_struct_0(sK0) = X0_50
    | k2_struct_0(sK0) != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_781])).

cnf(c_881,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK0) = u1_struct_0(sK0)
    | k2_struct_0(sK0) != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_834])).

cnf(c_883,plain,
    ( X0_50 != X1_50
    | X0_50 = k2_struct_0(sK0)
    | k2_struct_0(sK0) != X1_50 ),
    inference(instantiation,[status(thm)],[c_567])).

cnf(c_884,plain,
    ( k2_struct_0(sK0) != k1_xboole_0
    | k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_883])).

cnf(c_895,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = k2_zfmisc_1(X0_50,u1_struct_0(sK1))
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK0) != X0_50 ),
    inference(instantiation,[status(thm)],[c_783])).

cnf(c_897,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_895])).

cnf(c_896,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_967,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) != k2_zfmisc_1(X0_50,u1_struct_0(sK1))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(X0_50,u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_765])).

cnf(c_968,plain,
    ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) != k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_967])).

cnf(c_948,plain,
    ( X0_50 != u1_struct_0(sK0)
    | k2_struct_0(sK0) = X0_50
    | k2_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_781])).

cnf(c_1109,plain,
    ( k2_struct_0(sK0) != u1_struct_0(sK0)
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | k1_relat_1(sK2) != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_948])).

cnf(c_1178,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_729,c_579,c_553,c_592,c_595,c_596,c_758,c_760,c_766,c_784,c_812,c_835,c_854,c_881,c_884,c_897,c_896,c_968,c_1109,c_1170])).

cnf(c_1188,plain,
    ( k2_struct_0(sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1178,c_854])).

cnf(c_1316,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1170,c_1178,c_1188])).

cnf(c_1317,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_1316])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:51:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.69/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/0.98  
% 1.69/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.69/0.98  
% 1.69/0.98  ------  iProver source info
% 1.69/0.98  
% 1.69/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.69/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.69/0.98  git: non_committed_changes: false
% 1.69/0.98  git: last_make_outside_of_git: false
% 1.69/0.98  
% 1.69/0.98  ------ 
% 1.69/0.98  
% 1.69/0.98  ------ Input Options
% 1.69/0.98  
% 1.69/0.98  --out_options                           all
% 1.69/0.98  --tptp_safe_out                         true
% 1.69/0.98  --problem_path                          ""
% 1.69/0.98  --include_path                          ""
% 1.69/0.98  --clausifier                            res/vclausify_rel
% 1.69/0.98  --clausifier_options                    --mode clausify
% 1.69/0.98  --stdin                                 false
% 1.69/0.98  --stats_out                             all
% 1.69/0.98  
% 1.69/0.98  ------ General Options
% 1.69/0.98  
% 1.69/0.98  --fof                                   false
% 1.69/0.98  --time_out_real                         305.
% 1.69/0.98  --time_out_virtual                      -1.
% 1.69/0.98  --symbol_type_check                     false
% 1.69/0.98  --clausify_out                          false
% 1.69/0.98  --sig_cnt_out                           false
% 1.69/0.98  --trig_cnt_out                          false
% 1.69/0.98  --trig_cnt_out_tolerance                1.
% 1.69/0.98  --trig_cnt_out_sk_spl                   false
% 1.69/0.98  --abstr_cl_out                          false
% 1.69/0.98  
% 1.69/0.98  ------ Global Options
% 1.69/0.98  
% 1.69/0.98  --schedule                              default
% 1.69/0.98  --add_important_lit                     false
% 1.69/0.98  --prop_solver_per_cl                    1000
% 1.69/0.98  --min_unsat_core                        false
% 1.69/0.98  --soft_assumptions                      false
% 1.69/0.98  --soft_lemma_size                       3
% 1.69/0.98  --prop_impl_unit_size                   0
% 1.69/0.98  --prop_impl_unit                        []
% 1.69/0.98  --share_sel_clauses                     true
% 1.69/0.98  --reset_solvers                         false
% 1.69/0.98  --bc_imp_inh                            [conj_cone]
% 1.69/0.98  --conj_cone_tolerance                   3.
% 1.69/0.98  --extra_neg_conj                        none
% 1.69/0.98  --large_theory_mode                     true
% 1.69/0.98  --prolific_symb_bound                   200
% 1.69/0.98  --lt_threshold                          2000
% 1.69/0.98  --clause_weak_htbl                      true
% 1.69/0.98  --gc_record_bc_elim                     false
% 1.69/0.98  
% 1.69/0.98  ------ Preprocessing Options
% 1.69/0.98  
% 1.69/0.98  --preprocessing_flag                    true
% 1.69/0.98  --time_out_prep_mult                    0.1
% 1.69/0.98  --splitting_mode                        input
% 1.69/0.98  --splitting_grd                         true
% 1.69/0.98  --splitting_cvd                         false
% 1.69/0.98  --splitting_cvd_svl                     false
% 1.69/0.98  --splitting_nvd                         32
% 1.69/0.98  --sub_typing                            true
% 1.69/0.98  --prep_gs_sim                           true
% 1.69/0.98  --prep_unflatten                        true
% 1.69/0.98  --prep_res_sim                          true
% 1.69/0.98  --prep_upred                            true
% 1.69/0.98  --prep_sem_filter                       exhaustive
% 1.69/0.98  --prep_sem_filter_out                   false
% 1.69/0.98  --pred_elim                             true
% 1.69/0.98  --res_sim_input                         true
% 1.69/0.98  --eq_ax_congr_red                       true
% 1.69/0.98  --pure_diseq_elim                       true
% 1.69/0.98  --brand_transform                       false
% 1.69/0.98  --non_eq_to_eq                          false
% 1.69/0.98  --prep_def_merge                        true
% 1.69/0.98  --prep_def_merge_prop_impl              false
% 1.69/0.98  --prep_def_merge_mbd                    true
% 1.69/0.98  --prep_def_merge_tr_red                 false
% 1.69/0.98  --prep_def_merge_tr_cl                  false
% 1.69/0.98  --smt_preprocessing                     true
% 1.69/0.98  --smt_ac_axioms                         fast
% 1.69/0.98  --preprocessed_out                      false
% 1.69/0.98  --preprocessed_stats                    false
% 1.69/0.98  
% 1.69/0.98  ------ Abstraction refinement Options
% 1.69/0.98  
% 1.69/0.98  --abstr_ref                             []
% 1.69/0.98  --abstr_ref_prep                        false
% 1.69/0.98  --abstr_ref_until_sat                   false
% 1.69/0.98  --abstr_ref_sig_restrict                funpre
% 1.69/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.69/0.98  --abstr_ref_under                       []
% 1.69/0.98  
% 1.69/0.98  ------ SAT Options
% 1.69/0.98  
% 1.69/0.98  --sat_mode                              false
% 1.69/0.98  --sat_fm_restart_options                ""
% 1.69/0.98  --sat_gr_def                            false
% 1.69/0.98  --sat_epr_types                         true
% 1.69/0.98  --sat_non_cyclic_types                  false
% 1.69/0.98  --sat_finite_models                     false
% 1.69/0.98  --sat_fm_lemmas                         false
% 1.69/0.98  --sat_fm_prep                           false
% 1.69/0.98  --sat_fm_uc_incr                        true
% 1.69/0.98  --sat_out_model                         small
% 1.69/0.98  --sat_out_clauses                       false
% 1.69/0.98  
% 1.69/0.98  ------ QBF Options
% 1.69/0.98  
% 1.69/0.98  --qbf_mode                              false
% 1.69/0.98  --qbf_elim_univ                         false
% 1.69/0.98  --qbf_dom_inst                          none
% 1.69/0.98  --qbf_dom_pre_inst                      false
% 1.69/0.98  --qbf_sk_in                             false
% 1.69/0.98  --qbf_pred_elim                         true
% 1.69/0.98  --qbf_split                             512
% 1.69/0.98  
% 1.69/0.98  ------ BMC1 Options
% 1.69/0.98  
% 1.69/0.98  --bmc1_incremental                      false
% 1.69/0.98  --bmc1_axioms                           reachable_all
% 1.69/0.98  --bmc1_min_bound                        0
% 1.69/0.98  --bmc1_max_bound                        -1
% 1.69/0.98  --bmc1_max_bound_default                -1
% 1.69/0.98  --bmc1_symbol_reachability              true
% 1.69/0.98  --bmc1_property_lemmas                  false
% 1.69/0.98  --bmc1_k_induction                      false
% 1.69/0.98  --bmc1_non_equiv_states                 false
% 1.69/0.98  --bmc1_deadlock                         false
% 1.69/0.98  --bmc1_ucm                              false
% 1.69/0.98  --bmc1_add_unsat_core                   none
% 1.69/0.98  --bmc1_unsat_core_children              false
% 1.69/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.69/0.98  --bmc1_out_stat                         full
% 1.69/0.98  --bmc1_ground_init                      false
% 1.69/0.98  --bmc1_pre_inst_next_state              false
% 1.69/0.98  --bmc1_pre_inst_state                   false
% 1.69/0.98  --bmc1_pre_inst_reach_state             false
% 1.69/0.98  --bmc1_out_unsat_core                   false
% 1.69/0.98  --bmc1_aig_witness_out                  false
% 1.69/0.98  --bmc1_verbose                          false
% 1.69/0.98  --bmc1_dump_clauses_tptp                false
% 1.69/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.69/0.98  --bmc1_dump_file                        -
% 1.69/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.69/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.69/0.98  --bmc1_ucm_extend_mode                  1
% 1.69/0.98  --bmc1_ucm_init_mode                    2
% 1.69/0.98  --bmc1_ucm_cone_mode                    none
% 1.69/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.69/0.98  --bmc1_ucm_relax_model                  4
% 1.69/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.69/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.69/0.98  --bmc1_ucm_layered_model                none
% 1.69/0.98  --bmc1_ucm_max_lemma_size               10
% 1.69/0.98  
% 1.69/0.98  ------ AIG Options
% 1.69/0.98  
% 1.69/0.98  --aig_mode                              false
% 1.69/0.98  
% 1.69/0.98  ------ Instantiation Options
% 1.69/0.98  
% 1.69/0.98  --instantiation_flag                    true
% 1.69/0.98  --inst_sos_flag                         false
% 1.69/0.98  --inst_sos_phase                        true
% 1.69/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.69/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.69/0.98  --inst_lit_sel_side                     num_symb
% 1.69/0.98  --inst_solver_per_active                1400
% 1.69/0.98  --inst_solver_calls_frac                1.
% 1.69/0.98  --inst_passive_queue_type               priority_queues
% 1.69/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.69/0.98  --inst_passive_queues_freq              [25;2]
% 1.69/0.98  --inst_dismatching                      true
% 1.69/0.98  --inst_eager_unprocessed_to_passive     true
% 1.69/0.98  --inst_prop_sim_given                   true
% 1.69/0.98  --inst_prop_sim_new                     false
% 1.69/0.98  --inst_subs_new                         false
% 1.69/0.98  --inst_eq_res_simp                      false
% 1.69/0.98  --inst_subs_given                       false
% 1.69/0.98  --inst_orphan_elimination               true
% 1.69/0.98  --inst_learning_loop_flag               true
% 1.69/0.98  --inst_learning_start                   3000
% 1.69/0.98  --inst_learning_factor                  2
% 1.69/0.98  --inst_start_prop_sim_after_learn       3
% 1.69/0.98  --inst_sel_renew                        solver
% 1.69/0.98  --inst_lit_activity_flag                true
% 1.69/0.98  --inst_restr_to_given                   false
% 1.69/0.98  --inst_activity_threshold               500
% 1.69/0.98  --inst_out_proof                        true
% 1.69/0.98  
% 1.69/0.98  ------ Resolution Options
% 1.69/0.98  
% 1.69/0.98  --resolution_flag                       true
% 1.69/0.98  --res_lit_sel                           adaptive
% 1.69/0.98  --res_lit_sel_side                      none
% 1.69/0.98  --res_ordering                          kbo
% 1.69/0.98  --res_to_prop_solver                    active
% 1.69/0.98  --res_prop_simpl_new                    false
% 1.69/0.98  --res_prop_simpl_given                  true
% 1.69/0.98  --res_passive_queue_type                priority_queues
% 1.69/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.69/0.98  --res_passive_queues_freq               [15;5]
% 1.69/0.98  --res_forward_subs                      full
% 1.69/0.98  --res_backward_subs                     full
% 1.69/0.98  --res_forward_subs_resolution           true
% 1.69/0.98  --res_backward_subs_resolution          true
% 1.69/0.98  --res_orphan_elimination                true
% 1.69/0.98  --res_time_limit                        2.
% 1.69/0.98  --res_out_proof                         true
% 1.69/0.98  
% 1.69/0.98  ------ Superposition Options
% 1.69/0.98  
% 1.69/0.98  --superposition_flag                    true
% 1.69/0.98  --sup_passive_queue_type                priority_queues
% 1.69/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.69/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.69/0.98  --demod_completeness_check              fast
% 1.69/0.98  --demod_use_ground                      true
% 1.69/0.98  --sup_to_prop_solver                    passive
% 1.69/0.98  --sup_prop_simpl_new                    true
% 1.69/0.98  --sup_prop_simpl_given                  true
% 1.69/0.98  --sup_fun_splitting                     false
% 1.69/0.98  --sup_smt_interval                      50000
% 1.69/0.98  
% 1.69/0.98  ------ Superposition Simplification Setup
% 1.69/0.98  
% 1.69/0.98  --sup_indices_passive                   []
% 1.69/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.69/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.69/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.69/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.69/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.69/0.98  --sup_full_bw                           [BwDemod]
% 1.69/0.98  --sup_immed_triv                        [TrivRules]
% 1.69/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.69/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.69/0.98  --sup_immed_bw_main                     []
% 1.69/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.69/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.69/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.69/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.69/0.98  
% 1.69/0.98  ------ Combination Options
% 1.69/0.98  
% 1.69/0.98  --comb_res_mult                         3
% 1.69/0.98  --comb_sup_mult                         2
% 1.69/0.98  --comb_inst_mult                        10
% 1.69/0.98  
% 1.69/0.98  ------ Debug Options
% 1.69/0.98  
% 1.69/0.98  --dbg_backtrace                         false
% 1.69/0.98  --dbg_dump_prop_clauses                 false
% 1.69/0.98  --dbg_dump_prop_clauses_file            -
% 1.69/0.98  --dbg_out_stat                          false
% 1.69/0.98  ------ Parsing...
% 1.69/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.69/0.98  
% 1.69/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.69/0.98  
% 1.69/0.98  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.69/0.98  
% 1.69/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 1.69/0.98  ------ Proving...
% 1.69/0.98  ------ Problem Properties 
% 1.69/0.98  
% 1.69/0.98  
% 1.69/0.98  clauses                                 14
% 1.69/0.98  conjectures                             2
% 1.69/0.98  EPR                                     1
% 1.69/0.98  Horn                                    11
% 1.69/0.98  unary                                   3
% 1.69/0.98  binary                                  9
% 1.69/0.98  lits                                    28
% 1.69/0.98  lits eq                                 20
% 1.69/0.98  fd_pure                                 0
% 1.69/0.98  fd_pseudo                               0
% 1.69/0.98  fd_cond                                 0
% 1.69/0.98  fd_pseudo_cond                          0
% 1.69/0.98  AC symbols                              0
% 1.69/0.98  
% 1.69/0.98  ------ Schedule dynamic 5 is on 
% 1.69/0.98  
% 1.69/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.69/0.98  
% 1.69/0.98  
% 1.69/0.98  ------ 
% 1.69/0.98  Current options:
% 1.69/0.98  ------ 
% 1.69/0.98  
% 1.69/0.98  ------ Input Options
% 1.69/0.98  
% 1.69/0.98  --out_options                           all
% 1.69/0.98  --tptp_safe_out                         true
% 1.69/0.98  --problem_path                          ""
% 1.69/0.98  --include_path                          ""
% 1.69/0.98  --clausifier                            res/vclausify_rel
% 1.69/0.98  --clausifier_options                    --mode clausify
% 1.69/0.98  --stdin                                 false
% 1.69/0.98  --stats_out                             all
% 1.69/0.98  
% 1.69/0.98  ------ General Options
% 1.69/0.98  
% 1.69/0.98  --fof                                   false
% 1.69/0.98  --time_out_real                         305.
% 1.69/0.98  --time_out_virtual                      -1.
% 1.69/0.98  --symbol_type_check                     false
% 1.69/0.98  --clausify_out                          false
% 1.69/0.98  --sig_cnt_out                           false
% 1.69/0.98  --trig_cnt_out                          false
% 1.69/0.98  --trig_cnt_out_tolerance                1.
% 1.69/0.98  --trig_cnt_out_sk_spl                   false
% 1.69/0.98  --abstr_cl_out                          false
% 1.69/0.98  
% 1.69/0.98  ------ Global Options
% 1.69/0.98  
% 1.69/0.98  --schedule                              default
% 1.69/0.98  --add_important_lit                     false
% 1.69/0.98  --prop_solver_per_cl                    1000
% 1.69/0.98  --min_unsat_core                        false
% 1.69/0.98  --soft_assumptions                      false
% 1.69/0.98  --soft_lemma_size                       3
% 1.69/0.98  --prop_impl_unit_size                   0
% 1.69/0.98  --prop_impl_unit                        []
% 1.69/0.98  --share_sel_clauses                     true
% 1.69/0.98  --reset_solvers                         false
% 1.69/0.98  --bc_imp_inh                            [conj_cone]
% 1.69/0.98  --conj_cone_tolerance                   3.
% 1.69/0.98  --extra_neg_conj                        none
% 1.69/0.98  --large_theory_mode                     true
% 1.69/0.98  --prolific_symb_bound                   200
% 1.69/0.98  --lt_threshold                          2000
% 1.69/0.98  --clause_weak_htbl                      true
% 1.69/0.98  --gc_record_bc_elim                     false
% 1.69/0.98  
% 1.69/0.98  ------ Preprocessing Options
% 1.69/0.98  
% 1.69/0.98  --preprocessing_flag                    true
% 1.69/0.98  --time_out_prep_mult                    0.1
% 1.69/0.98  --splitting_mode                        input
% 1.69/0.98  --splitting_grd                         true
% 1.69/0.98  --splitting_cvd                         false
% 1.69/0.98  --splitting_cvd_svl                     false
% 1.69/0.98  --splitting_nvd                         32
% 1.69/0.98  --sub_typing                            true
% 1.69/0.98  --prep_gs_sim                           true
% 1.69/0.98  --prep_unflatten                        true
% 1.69/0.98  --prep_res_sim                          true
% 1.69/0.98  --prep_upred                            true
% 1.69/0.98  --prep_sem_filter                       exhaustive
% 1.69/0.98  --prep_sem_filter_out                   false
% 1.69/0.98  --pred_elim                             true
% 1.69/0.98  --res_sim_input                         true
% 1.69/0.98  --eq_ax_congr_red                       true
% 1.69/0.98  --pure_diseq_elim                       true
% 1.69/0.98  --brand_transform                       false
% 1.69/0.98  --non_eq_to_eq                          false
% 1.69/0.98  --prep_def_merge                        true
% 1.69/0.98  --prep_def_merge_prop_impl              false
% 1.69/0.98  --prep_def_merge_mbd                    true
% 1.69/0.98  --prep_def_merge_tr_red                 false
% 1.69/0.98  --prep_def_merge_tr_cl                  false
% 1.69/0.98  --smt_preprocessing                     true
% 1.69/0.98  --smt_ac_axioms                         fast
% 1.69/0.98  --preprocessed_out                      false
% 1.69/0.98  --preprocessed_stats                    false
% 1.69/0.98  
% 1.69/0.98  ------ Abstraction refinement Options
% 1.69/0.98  
% 1.69/0.98  --abstr_ref                             []
% 1.69/0.98  --abstr_ref_prep                        false
% 1.69/0.98  --abstr_ref_until_sat                   false
% 1.69/0.98  --abstr_ref_sig_restrict                funpre
% 1.69/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.69/0.98  --abstr_ref_under                       []
% 1.69/0.98  
% 1.69/0.98  ------ SAT Options
% 1.69/0.98  
% 1.69/0.98  --sat_mode                              false
% 1.69/0.98  --sat_fm_restart_options                ""
% 1.69/0.98  --sat_gr_def                            false
% 1.69/0.98  --sat_epr_types                         true
% 1.69/0.98  --sat_non_cyclic_types                  false
% 1.69/0.98  --sat_finite_models                     false
% 1.69/0.98  --sat_fm_lemmas                         false
% 1.69/0.98  --sat_fm_prep                           false
% 1.69/0.98  --sat_fm_uc_incr                        true
% 1.69/0.98  --sat_out_model                         small
% 1.69/0.98  --sat_out_clauses                       false
% 1.69/0.98  
% 1.69/0.98  ------ QBF Options
% 1.69/0.98  
% 1.69/0.98  --qbf_mode                              false
% 1.69/0.98  --qbf_elim_univ                         false
% 1.69/0.98  --qbf_dom_inst                          none
% 1.69/0.98  --qbf_dom_pre_inst                      false
% 1.69/0.98  --qbf_sk_in                             false
% 1.69/0.98  --qbf_pred_elim                         true
% 1.69/0.98  --qbf_split                             512
% 1.69/0.98  
% 1.69/0.98  ------ BMC1 Options
% 1.69/0.98  
% 1.69/0.98  --bmc1_incremental                      false
% 1.69/0.98  --bmc1_axioms                           reachable_all
% 1.69/0.98  --bmc1_min_bound                        0
% 1.69/0.98  --bmc1_max_bound                        -1
% 1.69/0.98  --bmc1_max_bound_default                -1
% 1.69/0.98  --bmc1_symbol_reachability              true
% 1.69/0.98  --bmc1_property_lemmas                  false
% 1.69/0.98  --bmc1_k_induction                      false
% 1.69/0.98  --bmc1_non_equiv_states                 false
% 1.69/0.98  --bmc1_deadlock                         false
% 1.69/0.98  --bmc1_ucm                              false
% 1.69/0.98  --bmc1_add_unsat_core                   none
% 1.69/0.98  --bmc1_unsat_core_children              false
% 1.69/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.69/0.98  --bmc1_out_stat                         full
% 1.69/0.98  --bmc1_ground_init                      false
% 1.69/0.98  --bmc1_pre_inst_next_state              false
% 1.69/0.98  --bmc1_pre_inst_state                   false
% 1.69/0.98  --bmc1_pre_inst_reach_state             false
% 1.69/0.98  --bmc1_out_unsat_core                   false
% 1.69/0.98  --bmc1_aig_witness_out                  false
% 1.69/0.98  --bmc1_verbose                          false
% 1.69/0.98  --bmc1_dump_clauses_tptp                false
% 1.69/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.69/0.98  --bmc1_dump_file                        -
% 1.69/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.69/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.69/0.98  --bmc1_ucm_extend_mode                  1
% 1.69/0.98  --bmc1_ucm_init_mode                    2
% 1.69/0.98  --bmc1_ucm_cone_mode                    none
% 1.69/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.69/0.98  --bmc1_ucm_relax_model                  4
% 1.69/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.69/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.69/0.98  --bmc1_ucm_layered_model                none
% 1.69/0.98  --bmc1_ucm_max_lemma_size               10
% 1.69/0.98  
% 1.69/0.98  ------ AIG Options
% 1.69/0.98  
% 1.69/0.98  --aig_mode                              false
% 1.69/0.98  
% 1.69/0.98  ------ Instantiation Options
% 1.69/0.98  
% 1.69/0.98  --instantiation_flag                    true
% 1.69/0.98  --inst_sos_flag                         false
% 1.69/0.98  --inst_sos_phase                        true
% 1.69/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.69/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.69/0.98  --inst_lit_sel_side                     none
% 1.69/0.98  --inst_solver_per_active                1400
% 1.69/0.98  --inst_solver_calls_frac                1.
% 1.69/0.98  --inst_passive_queue_type               priority_queues
% 1.69/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.69/0.98  --inst_passive_queues_freq              [25;2]
% 1.69/0.98  --inst_dismatching                      true
% 1.69/0.98  --inst_eager_unprocessed_to_passive     true
% 1.69/0.98  --inst_prop_sim_given                   true
% 1.69/0.98  --inst_prop_sim_new                     false
% 1.69/0.98  --inst_subs_new                         false
% 1.69/0.98  --inst_eq_res_simp                      false
% 1.69/0.98  --inst_subs_given                       false
% 1.69/0.98  --inst_orphan_elimination               true
% 1.69/0.98  --inst_learning_loop_flag               true
% 1.69/0.98  --inst_learning_start                   3000
% 1.69/0.98  --inst_learning_factor                  2
% 1.69/0.98  --inst_start_prop_sim_after_learn       3
% 1.69/0.98  --inst_sel_renew                        solver
% 1.69/0.98  --inst_lit_activity_flag                true
% 1.69/0.98  --inst_restr_to_given                   false
% 1.69/0.98  --inst_activity_threshold               500
% 1.69/0.98  --inst_out_proof                        true
% 1.69/0.98  
% 1.69/0.98  ------ Resolution Options
% 1.69/0.98  
% 1.69/0.98  --resolution_flag                       false
% 1.69/0.98  --res_lit_sel                           adaptive
% 1.69/0.98  --res_lit_sel_side                      none
% 1.69/0.98  --res_ordering                          kbo
% 1.69/0.98  --res_to_prop_solver                    active
% 1.69/0.98  --res_prop_simpl_new                    false
% 1.69/0.98  --res_prop_simpl_given                  true
% 1.69/0.98  --res_passive_queue_type                priority_queues
% 1.69/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.69/0.98  --res_passive_queues_freq               [15;5]
% 1.69/0.98  --res_forward_subs                      full
% 1.69/0.98  --res_backward_subs                     full
% 1.69/0.98  --res_forward_subs_resolution           true
% 1.69/0.98  --res_backward_subs_resolution          true
% 1.69/0.98  --res_orphan_elimination                true
% 1.69/0.98  --res_time_limit                        2.
% 1.69/0.98  --res_out_proof                         true
% 1.69/0.98  
% 1.69/0.98  ------ Superposition Options
% 1.69/0.98  
% 1.69/0.98  --superposition_flag                    true
% 1.69/0.98  --sup_passive_queue_type                priority_queues
% 1.69/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.69/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.69/0.98  --demod_completeness_check              fast
% 1.69/0.98  --demod_use_ground                      true
% 1.69/0.98  --sup_to_prop_solver                    passive
% 1.69/0.98  --sup_prop_simpl_new                    true
% 1.69/0.98  --sup_prop_simpl_given                  true
% 1.69/0.98  --sup_fun_splitting                     false
% 1.69/0.98  --sup_smt_interval                      50000
% 1.69/0.98  
% 1.69/0.98  ------ Superposition Simplification Setup
% 1.69/0.98  
% 1.69/0.98  --sup_indices_passive                   []
% 1.69/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.69/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.69/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.69/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.69/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.69/0.98  --sup_full_bw                           [BwDemod]
% 1.69/0.98  --sup_immed_triv                        [TrivRules]
% 1.69/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.69/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.69/0.98  --sup_immed_bw_main                     []
% 1.69/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.69/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.69/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.69/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.69/0.98  
% 1.69/0.98  ------ Combination Options
% 1.69/0.98  
% 1.69/0.98  --comb_res_mult                         3
% 1.69/0.98  --comb_sup_mult                         2
% 1.69/0.98  --comb_inst_mult                        10
% 1.69/0.98  
% 1.69/0.98  ------ Debug Options
% 1.69/0.98  
% 1.69/0.98  --dbg_backtrace                         false
% 1.69/0.98  --dbg_dump_prop_clauses                 false
% 1.69/0.98  --dbg_dump_prop_clauses_file            -
% 1.69/0.98  --dbg_out_stat                          false
% 1.69/0.98  
% 1.69/0.98  
% 1.69/0.98  
% 1.69/0.98  
% 1.69/0.98  ------ Proving...
% 1.69/0.98  
% 1.69/0.98  
% 1.69/0.98  % SZS status Theorem for theBenchmark.p
% 1.69/0.98  
% 1.69/0.98   Resolution empty clause
% 1.69/0.98  
% 1.69/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.69/0.98  
% 1.69/0.98  fof(f7,axiom,(
% 1.69/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 1.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.98  
% 1.69/0.98  fof(f19,plain,(
% 1.69/0.98    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.98    inference(ennf_transformation,[],[f7])).
% 1.69/0.98  
% 1.69/0.98  fof(f41,plain,(
% 1.69/0.98    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.69/0.98    inference(cnf_transformation,[],[f19])).
% 1.69/0.98  
% 1.69/0.98  fof(f11,conjecture,(
% 1.69/0.98    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 1.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.98  
% 1.69/0.98  fof(f12,negated_conjecture,(
% 1.69/0.98    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 1.69/0.98    inference(negated_conjecture,[],[f11])).
% 1.69/0.98  
% 1.69/0.98  fof(f25,plain,(
% 1.69/0.98    ? [X0] : (? [X1] : (? [X2] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 1.69/0.98    inference(ennf_transformation,[],[f12])).
% 1.69/0.98  
% 1.69/0.98  fof(f26,plain,(
% 1.69/0.98    ? [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 1.69/0.98    inference(flattening,[],[f25])).
% 1.69/0.98  
% 1.69/0.98  fof(f31,plain,(
% 1.69/0.98    ( ! [X0,X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 1.69/0.98    introduced(choice_axiom,[])).
% 1.69/0.98  
% 1.69/0.98  fof(f30,plain,(
% 1.69/0.98    ( ! [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))) )),
% 1.69/0.98    introduced(choice_axiom,[])).
% 1.69/0.98  
% 1.69/0.98  fof(f29,plain,(
% 1.69/0.98    ? [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(sK0) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 1.69/0.98    introduced(choice_axiom,[])).
% 1.69/0.98  
% 1.69/0.98  fof(f32,plain,(
% 1.69/0.98    ((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 1.69/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f31,f30,f29])).
% 1.69/0.98  
% 1.69/0.98  fof(f51,plain,(
% 1.69/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.69/0.98    inference(cnf_transformation,[],[f32])).
% 1.69/0.98  
% 1.69/0.98  fof(f10,axiom,(
% 1.69/0.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.98  
% 1.69/0.98  fof(f24,plain,(
% 1.69/0.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.69/0.98    inference(ennf_transformation,[],[f10])).
% 1.69/0.98  
% 1.69/0.98  fof(f46,plain,(
% 1.69/0.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.69/0.98    inference(cnf_transformation,[],[f24])).
% 1.69/0.98  
% 1.69/0.98  fof(f47,plain,(
% 1.69/0.98    l1_struct_0(sK0)),
% 1.69/0.98    inference(cnf_transformation,[],[f32])).
% 1.69/0.98  
% 1.69/0.98  fof(f48,plain,(
% 1.69/0.98    l1_struct_0(sK1)),
% 1.69/0.98    inference(cnf_transformation,[],[f32])).
% 1.69/0.98  
% 1.69/0.98  fof(f53,plain,(
% 1.69/0.98    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0)),
% 1.69/0.98    inference(cnf_transformation,[],[f32])).
% 1.69/0.98  
% 1.69/0.98  fof(f1,axiom,(
% 1.69/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.98  
% 1.69/0.98  fof(f13,plain,(
% 1.69/0.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.69/0.98    inference(ennf_transformation,[],[f1])).
% 1.69/0.98  
% 1.69/0.98  fof(f33,plain,(
% 1.69/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.69/0.98    inference(cnf_transformation,[],[f13])).
% 1.69/0.98  
% 1.69/0.98  fof(f2,axiom,(
% 1.69/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.98  
% 1.69/0.98  fof(f14,plain,(
% 1.69/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.69/0.98    inference(ennf_transformation,[],[f2])).
% 1.69/0.98  
% 1.69/0.98  fof(f27,plain,(
% 1.69/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.69/0.98    inference(nnf_transformation,[],[f14])).
% 1.69/0.98  
% 1.69/0.98  fof(f34,plain,(
% 1.69/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.69/0.98    inference(cnf_transformation,[],[f27])).
% 1.69/0.98  
% 1.69/0.98  fof(f6,axiom,(
% 1.69/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.98  
% 1.69/0.98  fof(f18,plain,(
% 1.69/0.98    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.98    inference(ennf_transformation,[],[f6])).
% 1.69/0.98  
% 1.69/0.98  fof(f40,plain,(
% 1.69/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.69/0.98    inference(cnf_transformation,[],[f18])).
% 1.69/0.98  
% 1.69/0.98  fof(f5,axiom,(
% 1.69/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.98  
% 1.69/0.98  fof(f17,plain,(
% 1.69/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.98    inference(ennf_transformation,[],[f5])).
% 1.69/0.98  
% 1.69/0.98  fof(f38,plain,(
% 1.69/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.69/0.98    inference(cnf_transformation,[],[f17])).
% 1.69/0.98  
% 1.69/0.98  fof(f3,axiom,(
% 1.69/0.98    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 1.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.98  
% 1.69/0.98  fof(f15,plain,(
% 1.69/0.98    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.69/0.98    inference(ennf_transformation,[],[f3])).
% 1.69/0.98  
% 1.69/0.98  fof(f36,plain,(
% 1.69/0.98    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.69/0.98    inference(cnf_transformation,[],[f15])).
% 1.69/0.98  
% 1.69/0.98  fof(f4,axiom,(
% 1.69/0.98    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.98  
% 1.69/0.98  fof(f16,plain,(
% 1.69/0.98    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.69/0.98    inference(ennf_transformation,[],[f4])).
% 1.69/0.98  
% 1.69/0.98  fof(f37,plain,(
% 1.69/0.98    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.69/0.98    inference(cnf_transformation,[],[f16])).
% 1.69/0.98  
% 1.69/0.98  fof(f9,axiom,(
% 1.69/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.98  
% 1.69/0.98  fof(f22,plain,(
% 1.69/0.98    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.69/0.98    inference(ennf_transformation,[],[f9])).
% 1.69/0.98  
% 1.69/0.98  fof(f23,plain,(
% 1.69/0.98    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.69/0.98    inference(flattening,[],[f22])).
% 1.69/0.98  
% 1.69/0.98  fof(f45,plain,(
% 1.69/0.98    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.69/0.98    inference(cnf_transformation,[],[f23])).
% 1.69/0.98  
% 1.69/0.98  fof(f55,plain,(
% 1.69/0.98    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 1.69/0.98    inference(equality_resolution,[],[f45])).
% 1.69/0.98  
% 1.69/0.98  fof(f50,plain,(
% 1.69/0.98    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.69/0.98    inference(cnf_transformation,[],[f32])).
% 1.69/0.98  
% 1.69/0.98  fof(f49,plain,(
% 1.69/0.98    v1_funct_1(sK2)),
% 1.69/0.98    inference(cnf_transformation,[],[f32])).
% 1.69/0.98  
% 1.69/0.98  fof(f39,plain,(
% 1.69/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.69/0.98    inference(cnf_transformation,[],[f18])).
% 1.69/0.98  
% 1.69/0.98  fof(f8,axiom,(
% 1.69/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.69/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.69/0.98  
% 1.69/0.98  fof(f20,plain,(
% 1.69/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.69/0.98    inference(ennf_transformation,[],[f8])).
% 1.69/0.98  
% 1.69/0.98  fof(f21,plain,(
% 1.69/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.69/0.98    inference(flattening,[],[f20])).
% 1.69/0.98  
% 1.69/0.98  fof(f28,plain,(
% 1.69/0.98    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.69/0.98    inference(nnf_transformation,[],[f21])).
% 1.69/0.98  
% 1.69/0.98  fof(f42,plain,(
% 1.69/0.98    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.69/0.98    inference(cnf_transformation,[],[f28])).
% 1.69/0.98  
% 1.69/0.98  fof(f44,plain,(
% 1.69/0.98    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.69/0.98    inference(cnf_transformation,[],[f23])).
% 1.69/0.98  
% 1.69/0.98  fof(f52,plain,(
% 1.69/0.98    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)),
% 1.69/0.98    inference(cnf_transformation,[],[f32])).
% 1.69/0.98  
% 1.69/0.98  cnf(c_8,plain,
% 1.69/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.69/0.98      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 1.69/0.98      inference(cnf_transformation,[],[f41]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_16,negated_conjecture,
% 1.69/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 1.69/0.98      inference(cnf_transformation,[],[f51]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_411,plain,
% 1.69/0.98      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.69/0.98      | sK2 != X2 ),
% 1.69/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_412,plain,
% 1.69/0.98      ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.69/0.98      inference(unflattening,[status(thm)],[c_411]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_551,plain,
% 1.69/0.98      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
% 1.69/0.98      | k8_relset_1(X0_50,X1_50,sK2,X2_50) = k10_relat_1(sK2,X2_50) ),
% 1.69/0.98      inference(subtyping,[status(esa)],[c_412]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_13,plain,
% 1.69/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.69/0.98      inference(cnf_transformation,[],[f46]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_20,negated_conjecture,
% 1.69/0.98      ( l1_struct_0(sK0) ),
% 1.69/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_231,plain,
% 1.69/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 1.69/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_232,plain,
% 1.69/0.98      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 1.69/0.98      inference(unflattening,[status(thm)],[c_231]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_553,plain,
% 1.69/0.98      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 1.69/0.98      inference(subtyping,[status(esa)],[c_232]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_19,negated_conjecture,
% 1.69/0.98      ( l1_struct_0(sK1) ),
% 1.69/0.98      inference(cnf_transformation,[],[f48]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_226,plain,
% 1.69/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 1.69/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_227,plain,
% 1.69/0.98      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.69/0.98      inference(unflattening,[status(thm)],[c_226]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_554,plain,
% 1.69/0.98      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.69/0.98      inference(subtyping,[status(esa)],[c_227]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_719,plain,
% 1.69/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
% 1.69/0.98      | k8_relset_1(X0_50,X1_50,sK2,X2_50) = k10_relat_1(sK2,X2_50) ),
% 1.69/0.98      inference(light_normalisation,[status(thm)],[c_551,c_553,c_554]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_1025,plain,
% 1.69/0.98      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0_50) = k10_relat_1(sK2,X0_50) ),
% 1.69/0.98      inference(equality_resolution,[status(thm)],[c_719]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_14,negated_conjecture,
% 1.69/0.98      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
% 1.69/0.98      inference(cnf_transformation,[],[f53]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_556,negated_conjecture,
% 1.69/0.98      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
% 1.69/0.98      inference(subtyping,[status(esa)],[c_14]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_680,plain,
% 1.69/0.98      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
% 1.69/0.98      inference(light_normalisation,[status(thm)],[c_556,c_553,c_554]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_1169,plain,
% 1.69/0.98      ( k10_relat_1(sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
% 1.69/0.98      inference(demodulation,[status(thm)],[c_1025,c_680]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_0,plain,
% 1.69/0.98      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 1.69/0.98      inference(cnf_transformation,[],[f33]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_2,plain,
% 1.69/0.98      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 1.69/0.98      inference(cnf_transformation,[],[f34]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_239,plain,
% 1.69/0.98      ( ~ v5_relat_1(X0,X1)
% 1.69/0.98      | ~ v1_relat_1(X0)
% 1.69/0.98      | X1 != X2
% 1.69/0.98      | k3_xboole_0(X3,X2) = X3
% 1.69/0.98      | k2_relat_1(X0) != X3 ),
% 1.69/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_2]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_240,plain,
% 1.69/0.98      ( ~ v5_relat_1(X0,X1)
% 1.69/0.98      | ~ v1_relat_1(X0)
% 1.69/0.98      | k3_xboole_0(k2_relat_1(X0),X1) = k2_relat_1(X0) ),
% 1.69/0.98      inference(unflattening,[status(thm)],[c_239]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_6,plain,
% 1.69/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v5_relat_1(X0,X2) ),
% 1.69/0.98      inference(cnf_transformation,[],[f40]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_258,plain,
% 1.69/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.69/0.98      | ~ v1_relat_1(X3)
% 1.69/0.98      | X0 != X3
% 1.69/0.98      | X2 != X4
% 1.69/0.98      | k3_xboole_0(k2_relat_1(X3),X4) = k2_relat_1(X3) ),
% 1.69/0.98      inference(resolution_lifted,[status(thm)],[c_240,c_6]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_259,plain,
% 1.69/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.69/0.98      | ~ v1_relat_1(X0)
% 1.69/0.98      | k3_xboole_0(k2_relat_1(X0),X2) = k2_relat_1(X0) ),
% 1.69/0.98      inference(unflattening,[status(thm)],[c_258]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_5,plain,
% 1.69/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 1.69/0.98      inference(cnf_transformation,[],[f38]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_263,plain,
% 1.69/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.69/0.98      | k3_xboole_0(k2_relat_1(X0),X2) = k2_relat_1(X0) ),
% 1.69/0.98      inference(global_propositional_subsumption,[status(thm)],[c_259,c_5]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_402,plain,
% 1.69/0.98      ( k3_xboole_0(k2_relat_1(X0),X1) = k2_relat_1(X0)
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
% 1.69/0.98      | sK2 != X0 ),
% 1.69/0.98      inference(resolution_lifted,[status(thm)],[c_263,c_16]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_403,plain,
% 1.69/0.98      ( k3_xboole_0(k2_relat_1(sK2),X0) = k2_relat_1(sK2)
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
% 1.69/0.98      inference(unflattening,[status(thm)],[c_402]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_552,plain,
% 1.69/0.98      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
% 1.69/0.98      | k3_xboole_0(k2_relat_1(sK2),X1_50) = k2_relat_1(sK2) ),
% 1.69/0.98      inference(subtyping,[status(esa)],[c_403]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_709,plain,
% 1.69/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
% 1.69/0.98      | k3_xboole_0(k2_relat_1(sK2),X1_50) = k2_relat_1(sK2) ),
% 1.69/0.98      inference(light_normalisation,[status(thm)],[c_552,c_553,c_554]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_833,plain,
% 1.69/0.98      ( k3_xboole_0(k2_relat_1(sK2),k2_struct_0(sK1)) = k2_relat_1(sK2) ),
% 1.69/0.98      inference(equality_resolution,[status(thm)],[c_709]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_3,plain,
% 1.69/0.98      ( ~ v1_relat_1(X0)
% 1.69/0.98      | k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1) ),
% 1.69/0.98      inference(cnf_transformation,[],[f36]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_420,plain,
% 1.69/0.98      ( v1_relat_1(X0)
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.69/0.98      | sK2 != X0 ),
% 1.69/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_16]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_421,plain,
% 1.69/0.98      ( v1_relat_1(sK2)
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.69/0.98      inference(unflattening,[status(thm)],[c_420]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_487,plain,
% 1.69/0.98      ( k10_relat_1(X0,k3_xboole_0(k2_relat_1(X0),X1)) = k10_relat_1(X0,X1)
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 1.69/0.98      | sK2 != X0 ),
% 1.69/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_421]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_488,plain,
% 1.69/0.98      ( k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0)) = k10_relat_1(sK2,X0)
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 1.69/0.98      inference(unflattening,[status(thm)],[c_487]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_549,plain,
% 1.69/0.98      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
% 1.69/0.98      | k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X2_50)) = k10_relat_1(sK2,X2_50) ),
% 1.69/0.98      inference(subtyping,[status(esa)],[c_488]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_557,plain,
% 1.69/0.98      ( k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0_50)) = k10_relat_1(sK2,X0_50)
% 1.69/0.98      | ~ sP0_iProver_split ),
% 1.69/0.98      inference(splitting,
% 1.69/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.69/0.98                [c_549]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_663,plain,
% 1.69/0.98      ( k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0_50)) = k10_relat_1(sK2,X0_50)
% 1.69/0.98      | sP0_iProver_split != iProver_top ),
% 1.69/0.98      inference(predicate_to_equality,[status(thm)],[c_557]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_559,plain,
% 1.69/0.98      ( sP1_iProver_split | sP0_iProver_split ),
% 1.69/0.98      inference(splitting,
% 1.69/0.98                [splitting(split),new_symbols(definition,[])],
% 1.69/0.98                [c_549]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_565,plain,( X0_52 = X0_52 ),theory(equality) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_758,plain,
% 1.69/0.98      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 1.69/0.98      inference(instantiation,[status(thm)],[c_565]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_558,plain,
% 1.69/0.98      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
% 1.69/0.98      | ~ sP1_iProver_split ),
% 1.69/0.98      inference(splitting,
% 1.69/0.98                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.69/0.98                [c_549]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_793,plain,
% 1.69/0.98      ( ~ sP1_iProver_split
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 1.69/0.98      inference(instantiation,[status(thm)],[c_558]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_841,plain,
% 1.69/0.98      ( k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X0_50)) = k10_relat_1(sK2,X0_50) ),
% 1.69/0.98      inference(global_propositional_subsumption,
% 1.69/0.98                [status(thm)],
% 1.69/0.98                [c_663,c_559,c_557,c_758,c_793]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_1147,plain,
% 1.69/0.98      ( k10_relat_1(sK2,k2_struct_0(sK1)) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
% 1.69/0.98      inference(superposition,[status(thm)],[c_833,c_841]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_4,plain,
% 1.69/0.98      ( ~ v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 1.69/0.98      inference(cnf_transformation,[],[f37]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_478,plain,
% 1.69/0.98      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.69/0.98      | sK2 != X0 ),
% 1.69/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_421]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_479,plain,
% 1.69/0.98      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.69/0.98      inference(unflattening,[status(thm)],[c_478]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_550,plain,
% 1.69/0.98      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
% 1.69/0.98      | k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 1.69/0.98      inference(subtyping,[status(esa)],[c_479]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_714,plain,
% 1.69/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))
% 1.69/0.98      | k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 1.69/0.98      inference(light_normalisation,[status(thm)],[c_550,c_553,c_554]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_794,plain,
% 1.69/0.98      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 1.69/0.98      | k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 1.69/0.98      inference(instantiation,[status(thm)],[c_550]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_974,plain,
% 1.69/0.98      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 1.69/0.98      inference(global_propositional_subsumption,
% 1.69/0.98                [status(thm)],
% 1.69/0.98                [c_714,c_758,c_794]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_1149,plain,
% 1.69/0.98      ( k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2) ),
% 1.69/0.98      inference(light_normalisation,[status(thm)],[c_1147,c_974]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_1170,plain,
% 1.69/0.98      ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 1.69/0.98      inference(light_normalisation,[status(thm)],[c_1169,c_1149]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_11,plain,
% 1.69/0.98      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.69/0.98      | v1_partfun1(X0,k1_xboole_0)
% 1.69/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.69/0.98      | ~ v1_funct_1(X0) ),
% 1.69/0.98      inference(cnf_transformation,[],[f55]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_17,negated_conjecture,
% 1.69/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 1.69/0.98      inference(cnf_transformation,[],[f50]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_349,plain,
% 1.69/0.98      ( v1_partfun1(X0,k1_xboole_0)
% 1.69/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.69/0.98      | ~ v1_funct_1(X0)
% 1.69/0.98      | u1_struct_0(sK1) != X1
% 1.69/0.98      | u1_struct_0(sK0) != k1_xboole_0
% 1.69/0.98      | sK2 != X0 ),
% 1.69/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_350,plain,
% 1.69/0.98      ( v1_partfun1(sK2,k1_xboole_0)
% 1.69/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
% 1.69/0.98      | ~ v1_funct_1(sK2)
% 1.69/0.98      | u1_struct_0(sK0) != k1_xboole_0 ),
% 1.69/0.98      inference(unflattening,[status(thm)],[c_349]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_18,negated_conjecture,
% 1.69/0.98      ( v1_funct_1(sK2) ),
% 1.69/0.98      inference(cnf_transformation,[],[f49]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_352,plain,
% 1.69/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
% 1.69/0.98      | v1_partfun1(sK2,k1_xboole_0)
% 1.69/0.98      | u1_struct_0(sK0) != k1_xboole_0 ),
% 1.69/0.98      inference(global_propositional_subsumption,[status(thm)],[c_350,c_18]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_353,plain,
% 1.69/0.98      ( v1_partfun1(sK2,k1_xboole_0)
% 1.69/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
% 1.69/0.98      | u1_struct_0(sK0) != k1_xboole_0 ),
% 1.69/0.98      inference(renaming,[status(thm)],[c_352]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_444,plain,
% 1.69/0.98      ( v1_partfun1(sK2,k1_xboole_0)
% 1.69/0.98      | u1_struct_0(sK0) != k1_xboole_0
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
% 1.69/0.98      | sK2 != sK2 ),
% 1.69/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_353]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_7,plain,
% 1.69/0.98      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.69/0.98      inference(cnf_transformation,[],[f39]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_10,plain,
% 1.69/0.98      ( ~ v1_partfun1(X0,X1)
% 1.69/0.98      | ~ v4_relat_1(X0,X1)
% 1.69/0.98      | ~ v1_relat_1(X0)
% 1.69/0.98      | k1_relat_1(X0) = X1 ),
% 1.69/0.98      inference(cnf_transformation,[],[f42]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_279,plain,
% 1.69/0.98      ( ~ v1_partfun1(X0,X1)
% 1.69/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.69/0.98      | ~ v1_relat_1(X0)
% 1.69/0.98      | k1_relat_1(X0) = X1 ),
% 1.69/0.98      inference(resolution,[status(thm)],[c_7,c_10]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_283,plain,
% 1.69/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.69/0.98      | ~ v1_partfun1(X0,X1)
% 1.69/0.98      | k1_relat_1(X0) = X1 ),
% 1.69/0.98      inference(global_propositional_subsumption,
% 1.69/0.98                [status(thm)],
% 1.69/0.98                [c_279,c_10,c_7,c_5]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_284,plain,
% 1.69/0.98      ( ~ v1_partfun1(X0,X1)
% 1.69/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.69/0.98      | k1_relat_1(X0) = X1 ),
% 1.69/0.98      inference(renaming,[status(thm)],[c_283]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_387,plain,
% 1.69/0.98      ( ~ v1_partfun1(X0,X1)
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.69/0.98      | k1_relat_1(X0) = X1
% 1.69/0.98      | sK2 != X0 ),
% 1.69/0.98      inference(resolution_lifted,[status(thm)],[c_284,c_16]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_388,plain,
% 1.69/0.98      ( ~ v1_partfun1(sK2,X0)
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.69/0.98      | k1_relat_1(sK2) = X0 ),
% 1.69/0.98      inference(unflattening,[status(thm)],[c_387]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_500,plain,
% 1.69/0.98      ( u1_struct_0(sK0) != k1_xboole_0
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
% 1.69/0.98      | k1_relat_1(sK2) = X0
% 1.69/0.98      | sK2 != sK2
% 1.69/0.98      | k1_xboole_0 != X0 ),
% 1.69/0.98      inference(resolution_lifted,[status(thm)],[c_444,c_388]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_501,plain,
% 1.69/0.98      ( u1_struct_0(sK0) != k1_xboole_0
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
% 1.69/0.98      | k1_relat_1(sK2) = k1_xboole_0 ),
% 1.69/0.98      inference(unflattening,[status(thm)],[c_500]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_548,plain,
% 1.69/0.98      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_50))
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
% 1.69/0.98      | u1_struct_0(sK0) != k1_xboole_0
% 1.69/0.98      | k1_relat_1(sK2) = k1_xboole_0 ),
% 1.69/0.98      inference(subtyping,[status(esa)],[c_501]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_561,plain,
% 1.69/0.98      ( sP2_iProver_split
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
% 1.69/0.98      | u1_struct_0(sK0) != k1_xboole_0
% 1.69/0.98      | k1_relat_1(sK2) = k1_xboole_0 ),
% 1.69/0.98      inference(splitting,
% 1.69/0.98                [splitting(split),new_symbols(definition,[])],
% 1.69/0.98                [c_548]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_664,plain,
% 1.69/0.98      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
% 1.69/0.98      | u1_struct_0(sK0) != k1_xboole_0
% 1.69/0.98      | k1_relat_1(sK2) = k1_xboole_0
% 1.69/0.98      | sP2_iProver_split = iProver_top ),
% 1.69/0.98      inference(predicate_to_equality,[status(thm)],[c_561]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_724,plain,
% 1.69/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))
% 1.69/0.98      | k2_struct_0(sK0) != k1_xboole_0
% 1.69/0.98      | k1_relat_1(sK2) = k1_xboole_0
% 1.69/0.98      | sP2_iProver_split = iProver_top ),
% 1.69/0.98      inference(light_normalisation,[status(thm)],[c_664,c_553,c_554]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_560,plain,
% 1.69/0.98      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_50))
% 1.69/0.98      | ~ sP2_iProver_split ),
% 1.69/0.98      inference(splitting,
% 1.69/0.98                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 1.69/0.98                [c_548]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_665,plain,
% 1.69/0.98      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_50))
% 1.69/0.98      | sP2_iProver_split != iProver_top ),
% 1.69/0.98      inference(predicate_to_equality,[status(thm)],[c_560]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_699,plain,
% 1.69/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_50))
% 1.69/0.98      | sP2_iProver_split != iProver_top ),
% 1.69/0.98      inference(light_normalisation,[status(thm)],[c_665,c_553,c_554]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_729,plain,
% 1.69/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))
% 1.69/0.98      | k2_struct_0(sK0) != k1_xboole_0
% 1.69/0.98      | k1_relat_1(sK2) = k1_xboole_0 ),
% 1.69/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_724,c_699]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_564,plain,( X0_50 = X0_50 ),theory(equality) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_579,plain,
% 1.69/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 1.69/0.98      inference(instantiation,[status(thm)],[c_564]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_592,plain,
% 1.69/0.98      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))
% 1.69/0.98      | u1_struct_0(sK0) != k1_xboole_0
% 1.69/0.98      | k1_relat_1(sK2) = k1_xboole_0
% 1.69/0.98      | sP2_iProver_split = iProver_top ),
% 1.69/0.98      inference(predicate_to_equality,[status(thm)],[c_561]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_593,plain,
% 1.69/0.98      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0_50))
% 1.69/0.98      | sP2_iProver_split != iProver_top ),
% 1.69/0.98      inference(predicate_to_equality,[status(thm)],[c_560]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_595,plain,
% 1.69/0.98      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 1.69/0.98      | sP2_iProver_split != iProver_top ),
% 1.69/0.98      inference(instantiation,[status(thm)],[c_593]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_12,plain,
% 1.69/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 1.69/0.98      | v1_partfun1(X0,X1)
% 1.69/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.69/0.98      | ~ v1_funct_1(X0)
% 1.69/0.98      | k1_xboole_0 = X2 ),
% 1.69/0.98      inference(cnf_transformation,[],[f44]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_366,plain,
% 1.69/0.98      ( v1_partfun1(X0,X1)
% 1.69/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.69/0.98      | ~ v1_funct_1(X0)
% 1.69/0.98      | u1_struct_0(sK1) != X2
% 1.69/0.98      | u1_struct_0(sK0) != X1
% 1.69/0.98      | sK2 != X0
% 1.69/0.98      | k1_xboole_0 = X2 ),
% 1.69/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_367,plain,
% 1.69/0.98      ( v1_partfun1(sK2,u1_struct_0(sK0))
% 1.69/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.69/0.98      | ~ v1_funct_1(sK2)
% 1.69/0.98      | k1_xboole_0 = u1_struct_0(sK1) ),
% 1.69/0.98      inference(unflattening,[status(thm)],[c_366]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_369,plain,
% 1.69/0.98      ( v1_partfun1(sK2,u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK1) ),
% 1.69/0.98      inference(global_propositional_subsumption,
% 1.69/0.98                [status(thm)],
% 1.69/0.98                [c_367,c_18,c_16]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_515,plain,
% 1.69/0.98      ( u1_struct_0(sK1) = k1_xboole_0
% 1.69/0.98      | u1_struct_0(sK0) != X0
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.69/0.98      | k1_relat_1(sK2) = X0
% 1.69/0.98      | sK2 != sK2 ),
% 1.69/0.98      inference(resolution_lifted,[status(thm)],[c_369,c_388]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_516,plain,
% 1.69/0.98      ( u1_struct_0(sK1) = k1_xboole_0
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0))
% 1.69/0.98      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 1.69/0.98      inference(unflattening,[status(thm)],[c_515]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_547,plain,
% 1.69/0.98      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0_50))
% 1.69/0.98      | u1_struct_0(sK1) = k1_xboole_0
% 1.69/0.98      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 1.69/0.98      inference(subtyping,[status(esa)],[c_516]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_563,plain,
% 1.69/0.98      ( sP3_iProver_split
% 1.69/0.98      | u1_struct_0(sK1) = k1_xboole_0
% 1.69/0.98      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 1.69/0.98      inference(splitting,
% 1.69/0.98                [splitting(split),new_symbols(definition,[])],
% 1.69/0.98                [c_547]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_596,plain,
% 1.69/0.98      ( u1_struct_0(sK1) = k1_xboole_0
% 1.69/0.98      | k1_relat_1(sK2) = u1_struct_0(sK0)
% 1.69/0.98      | sP3_iProver_split = iProver_top ),
% 1.69/0.98      inference(predicate_to_equality,[status(thm)],[c_563]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_562,plain,
% 1.69/0.98      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0_50))
% 1.69/0.98      | ~ sP3_iProver_split ),
% 1.69/0.98      inference(splitting,
% 1.69/0.98                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 1.69/0.98                [c_547]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_759,plain,
% 1.69/0.98      ( ~ sP3_iProver_split
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 1.69/0.98      inference(instantiation,[status(thm)],[c_562]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_760,plain,
% 1.69/0.98      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 1.69/0.98      | sP3_iProver_split != iProver_top ),
% 1.69/0.98      inference(predicate_to_equality,[status(thm)],[c_759]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_572,plain,
% 1.69/0.98      ( X0_53 != X1_53 | k1_zfmisc_1(X0_53) = k1_zfmisc_1(X1_53) ),
% 1.69/0.98      theory(equality) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_765,plain,
% 1.69/0.98      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) != k2_zfmisc_1(X0_50,X1_50)
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)) ),
% 1.69/0.98      inference(instantiation,[status(thm)],[c_572]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_766,plain,
% 1.69/0.98      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
% 1.69/0.98      inference(instantiation,[status(thm)],[c_765]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_571,plain,
% 1.69/0.98      ( k2_zfmisc_1(X0_50,X1_50) = k2_zfmisc_1(X2_50,X3_50)
% 1.69/0.98      | X0_50 != X2_50
% 1.69/0.98      | X1_50 != X3_50 ),
% 1.69/0.98      theory(equality) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_783,plain,
% 1.69/0.98      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = k2_zfmisc_1(X0_50,X1_50)
% 1.69/0.98      | u1_struct_0(sK1) != X1_50
% 1.69/0.98      | u1_struct_0(sK0) != X0_50 ),
% 1.69/0.98      inference(instantiation,[status(thm)],[c_571]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_784,plain,
% 1.69/0.98      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 1.69/0.98      | u1_struct_0(sK1) != k1_xboole_0
% 1.69/0.98      | u1_struct_0(sK0) != k1_xboole_0 ),
% 1.69/0.98      inference(instantiation,[status(thm)],[c_783]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_567,plain,
% 1.69/0.98      ( X0_50 != X1_50 | X2_50 != X1_50 | X2_50 = X0_50 ),
% 1.69/0.98      theory(equality) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_767,plain,
% 1.69/0.98      ( u1_struct_0(sK0) != X0_50
% 1.69/0.98      | u1_struct_0(sK0) = k1_xboole_0
% 1.69/0.98      | k1_xboole_0 != X0_50 ),
% 1.69/0.98      inference(instantiation,[status(thm)],[c_567]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_812,plain,
% 1.69/0.98      ( u1_struct_0(sK0) != k2_struct_0(sK0)
% 1.69/0.98      | u1_struct_0(sK0) = k1_xboole_0
% 1.69/0.98      | k1_xboole_0 != k2_struct_0(sK0) ),
% 1.69/0.98      inference(instantiation,[status(thm)],[c_767]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_835,plain,
% 1.69/0.98      ( k2_struct_0(sK0) = k2_struct_0(sK0) ),
% 1.69/0.98      inference(instantiation,[status(thm)],[c_564]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_666,plain,
% 1.69/0.98      ( u1_struct_0(sK1) = k1_xboole_0
% 1.69/0.98      | k1_relat_1(sK2) = u1_struct_0(sK0)
% 1.69/0.98      | sP3_iProver_split = iProver_top ),
% 1.69/0.98      inference(predicate_to_equality,[status(thm)],[c_563]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_683,plain,
% 1.69/0.98      ( k2_struct_0(sK1) = k1_xboole_0
% 1.69/0.98      | k2_struct_0(sK0) = k1_relat_1(sK2)
% 1.69/0.98      | sP3_iProver_split = iProver_top ),
% 1.69/0.98      inference(demodulation,[status(thm)],[c_666,c_553,c_554]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_733,plain,
% 1.69/0.98      ( sP3_iProver_split
% 1.69/0.98      | k2_struct_0(sK1) = k1_xboole_0
% 1.69/0.98      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 1.69/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_683]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_846,plain,
% 1.69/0.98      ( k2_struct_0(sK0) = k1_relat_1(sK2) | k2_struct_0(sK1) = k1_xboole_0 ),
% 1.69/0.98      inference(global_propositional_subsumption,
% 1.69/0.98                [status(thm)],
% 1.69/0.98                [c_683,c_733,c_758,c_759]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_847,plain,
% 1.69/0.98      ( k2_struct_0(sK1) = k1_xboole_0 | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 1.69/0.98      inference(renaming,[status(thm)],[c_846]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_15,negated_conjecture,
% 1.69/0.98      ( k1_xboole_0 != k2_struct_0(sK1) | k1_xboole_0 = k2_struct_0(sK0) ),
% 1.69/0.98      inference(cnf_transformation,[],[f52]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_555,negated_conjecture,
% 1.69/0.98      ( k1_xboole_0 != k2_struct_0(sK1) | k1_xboole_0 = k2_struct_0(sK0) ),
% 1.69/0.98      inference(subtyping,[status(esa)],[c_15]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_854,plain,
% 1.69/0.98      ( k2_struct_0(sK0) = k1_relat_1(sK2) | k2_struct_0(sK0) = k1_xboole_0 ),
% 1.69/0.98      inference(superposition,[status(thm)],[c_847,c_555]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_781,plain,
% 1.69/0.98      ( X0_50 != X1_50 | k2_struct_0(sK0) != X1_50 | k2_struct_0(sK0) = X0_50 ),
% 1.69/0.98      inference(instantiation,[status(thm)],[c_567]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_834,plain,
% 1.69/0.98      ( X0_50 != k2_struct_0(sK0)
% 1.69/0.98      | k2_struct_0(sK0) = X0_50
% 1.69/0.98      | k2_struct_0(sK0) != k2_struct_0(sK0) ),
% 1.69/0.98      inference(instantiation,[status(thm)],[c_781]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_881,plain,
% 1.69/0.98      ( u1_struct_0(sK0) != k2_struct_0(sK0)
% 1.69/0.98      | k2_struct_0(sK0) = u1_struct_0(sK0)
% 1.69/0.98      | k2_struct_0(sK0) != k2_struct_0(sK0) ),
% 1.69/0.98      inference(instantiation,[status(thm)],[c_834]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_883,plain,
% 1.69/0.98      ( X0_50 != X1_50 | X0_50 = k2_struct_0(sK0) | k2_struct_0(sK0) != X1_50 ),
% 1.69/0.98      inference(instantiation,[status(thm)],[c_567]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_884,plain,
% 1.69/0.98      ( k2_struct_0(sK0) != k1_xboole_0
% 1.69/0.98      | k1_xboole_0 = k2_struct_0(sK0)
% 1.69/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 1.69/0.98      inference(instantiation,[status(thm)],[c_883]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_895,plain,
% 1.69/0.98      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = k2_zfmisc_1(X0_50,u1_struct_0(sK1))
% 1.69/0.98      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.69/0.98      | u1_struct_0(sK0) != X0_50 ),
% 1.69/0.98      inference(instantiation,[status(thm)],[c_783]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_897,plain,
% 1.69/0.98      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) = k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))
% 1.69/0.98      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 1.69/0.98      | u1_struct_0(sK0) != k1_xboole_0 ),
% 1.69/0.98      inference(instantiation,[status(thm)],[c_895]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_896,plain,
% 1.69/0.98      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 1.69/0.98      inference(instantiation,[status(thm)],[c_564]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_967,plain,
% 1.69/0.98      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) != k2_zfmisc_1(X0_50,u1_struct_0(sK1))
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(X0_50,u1_struct_0(sK1))) ),
% 1.69/0.98      inference(instantiation,[status(thm)],[c_765]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_968,plain,
% 1.69/0.98      ( k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) != k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))
% 1.69/0.98      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))) ),
% 1.69/0.98      inference(instantiation,[status(thm)],[c_967]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_948,plain,
% 1.69/0.98      ( X0_50 != u1_struct_0(sK0)
% 1.69/0.98      | k2_struct_0(sK0) = X0_50
% 1.69/0.98      | k2_struct_0(sK0) != u1_struct_0(sK0) ),
% 1.69/0.98      inference(instantiation,[status(thm)],[c_781]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_1109,plain,
% 1.69/0.98      ( k2_struct_0(sK0) != u1_struct_0(sK0)
% 1.69/0.98      | k2_struct_0(sK0) = k1_relat_1(sK2)
% 1.69/0.98      | k1_relat_1(sK2) != u1_struct_0(sK0) ),
% 1.69/0.98      inference(instantiation,[status(thm)],[c_948]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_1178,plain,
% 1.69/0.98      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 1.69/0.98      inference(global_propositional_subsumption,
% 1.69/0.98                [status(thm)],
% 1.69/0.98                [c_729,c_579,c_553,c_592,c_595,c_596,c_758,c_760,c_766,
% 1.69/0.98                 c_784,c_812,c_835,c_854,c_881,c_884,c_897,c_896,c_968,
% 1.69/0.98                 c_1109,c_1170]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_1188,plain,
% 1.69/0.98      ( k2_struct_0(sK0) = k1_xboole_0 ),
% 1.69/0.98      inference(demodulation,[status(thm)],[c_1178,c_854]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_1316,plain,
% 1.69/0.98      ( k1_xboole_0 != k1_xboole_0 ),
% 1.69/0.98      inference(light_normalisation,[status(thm)],[c_1170,c_1178,c_1188]) ).
% 1.69/0.98  
% 1.69/0.98  cnf(c_1317,plain,
% 1.69/0.98      ( $false ),
% 1.69/0.98      inference(equality_resolution_simp,[status(thm)],[c_1316]) ).
% 1.69/0.98  
% 1.69/0.98  
% 1.69/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.69/0.98  
% 1.69/0.98  ------                               Statistics
% 1.69/0.98  
% 1.69/0.98  ------ General
% 1.69/0.98  
% 1.69/0.98  abstr_ref_over_cycles:                  0
% 1.69/0.98  abstr_ref_under_cycles:                 0
% 1.69/0.98  gc_basic_clause_elim:                   0
% 1.69/0.98  forced_gc_time:                         0
% 1.69/0.98  parsing_time:                           0.009
% 1.69/0.98  unif_index_cands_time:                  0.
% 1.69/0.98  unif_index_add_time:                    0.
% 1.69/0.98  orderings_time:                         0.
% 1.69/0.98  out_proof_time:                         0.015
% 1.69/0.98  total_time:                             0.08
% 1.69/0.98  num_of_symbols:                         62
% 1.69/0.98  num_of_terms:                           1323
% 1.69/0.98  
% 1.69/0.98  ------ Preprocessing
% 1.69/0.98  
% 1.69/0.98  num_of_splits:                          4
% 1.69/0.98  num_of_split_atoms:                     4
% 1.69/0.98  num_of_reused_defs:                     0
% 1.69/0.98  num_eq_ax_congr_red:                    18
% 1.69/0.98  num_of_sem_filtered_clauses:            0
% 1.69/0.98  num_of_subtypes:                        5
% 1.69/0.98  monotx_restored_types:                  0
% 1.69/0.98  sat_num_of_epr_types:                   0
% 1.69/0.98  sat_num_of_non_cyclic_types:            0
% 1.69/0.98  sat_guarded_non_collapsed_types:        0
% 1.69/0.98  num_pure_diseq_elim:                    0
% 1.69/0.98  simp_replaced_by:                       0
% 1.69/0.98  res_preprocessed:                       55
% 1.69/0.98  prep_upred:                             0
% 1.69/0.98  prep_unflattend:                        23
% 1.69/0.98  smt_new_axioms:                         0
% 1.69/0.98  pred_elim_cands:                        0
% 1.69/0.98  pred_elim:                              9
% 1.69/0.98  pred_elim_cl:                           11
% 1.69/0.98  pred_elim_cycles:                       11
% 1.69/0.98  merged_defs:                            0
% 1.69/0.98  merged_defs_ncl:                        0
% 1.69/0.98  bin_hyper_res:                          0
% 1.69/0.98  prep_cycles:                            3
% 1.69/0.98  pred_elim_time:                         0.006
% 1.69/0.98  splitting_time:                         0.
% 1.69/0.98  sem_filter_time:                        0.
% 1.69/0.98  monotx_time:                            0.
% 1.69/0.98  subtype_inf_time:                       0.
% 1.69/0.98  
% 1.69/0.98  ------ Problem properties
% 1.69/0.98  
% 1.69/0.98  clauses:                                14
% 1.69/0.98  conjectures:                            2
% 1.69/0.98  epr:                                    1
% 1.69/0.98  horn:                                   11
% 1.69/0.98  ground:                                 7
% 1.69/0.98  unary:                                  3
% 1.69/0.98  binary:                                 9
% 1.69/0.98  lits:                                   28
% 1.69/0.98  lits_eq:                                20
% 1.69/0.98  fd_pure:                                0
% 1.69/0.98  fd_pseudo:                              0
% 1.69/0.98  fd_cond:                                0
% 1.69/0.98  fd_pseudo_cond:                         0
% 1.69/0.98  ac_symbols:                             0
% 1.69/0.98  
% 1.69/0.98  ------ Propositional Solver
% 1.69/0.98  
% 1.69/0.98  prop_solver_calls:                      23
% 1.69/0.98  prop_fast_solver_calls:                 348
% 1.69/0.98  smt_solver_calls:                       0
% 1.69/0.98  smt_fast_solver_calls:                  0
% 1.69/0.98  prop_num_of_clauses:                    416
% 1.69/0.98  prop_preprocess_simplified:             1515
% 1.69/0.98  prop_fo_subsumed:                       12
% 1.69/0.98  prop_solver_time:                       0.
% 1.69/0.98  smt_solver_time:                        0.
% 1.69/0.98  smt_fast_solver_time:                   0.
% 1.69/0.98  prop_fast_solver_time:                  0.
% 1.69/0.98  prop_unsat_core_time:                   0.
% 1.69/0.98  
% 1.69/0.98  ------ QBF
% 1.69/0.98  
% 1.69/0.98  qbf_q_res:                              0
% 1.69/0.98  qbf_num_tautologies:                    0
% 1.69/0.98  qbf_prep_cycles:                        0
% 1.69/0.98  
% 1.69/0.98  ------ BMC1
% 1.69/0.98  
% 1.69/0.98  bmc1_current_bound:                     -1
% 1.69/0.98  bmc1_last_solved_bound:                 -1
% 1.69/0.98  bmc1_unsat_core_size:                   -1
% 1.69/0.98  bmc1_unsat_core_parents_size:           -1
% 1.69/0.98  bmc1_merge_next_fun:                    0
% 1.69/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.69/0.98  
% 1.69/0.98  ------ Instantiation
% 1.69/0.98  
% 1.69/0.98  inst_num_of_clauses:                    129
% 1.69/0.98  inst_num_in_passive:                    16
% 1.69/0.98  inst_num_in_active:                     86
% 1.69/0.98  inst_num_in_unprocessed:                27
% 1.69/0.98  inst_num_of_loops:                      130
% 1.69/0.98  inst_num_of_learning_restarts:          0
% 1.69/0.98  inst_num_moves_active_passive:          40
% 1.69/0.98  inst_lit_activity:                      0
% 1.69/0.98  inst_lit_activity_moves:                0
% 1.69/0.98  inst_num_tautologies:                   0
% 1.69/0.98  inst_num_prop_implied:                  0
% 1.69/0.98  inst_num_existing_simplified:           0
% 1.69/0.98  inst_num_eq_res_simplified:             0
% 1.69/0.98  inst_num_child_elim:                    0
% 1.69/0.98  inst_num_of_dismatching_blockings:      30
% 1.69/0.98  inst_num_of_non_proper_insts:           119
% 1.69/0.98  inst_num_of_duplicates:                 0
% 1.69/0.98  inst_inst_num_from_inst_to_res:         0
% 1.69/0.98  inst_dismatching_checking_time:         0.
% 1.69/0.98  
% 1.69/0.98  ------ Resolution
% 1.69/0.98  
% 1.69/0.98  res_num_of_clauses:                     0
% 1.69/0.98  res_num_in_passive:                     0
% 1.69/0.98  res_num_in_active:                      0
% 1.69/0.98  res_num_of_loops:                       58
% 1.69/0.98  res_forward_subset_subsumed:            41
% 1.69/0.98  res_backward_subset_subsumed:           0
% 1.69/0.98  res_forward_subsumed:                   0
% 1.69/0.98  res_backward_subsumed:                  0
% 1.69/0.98  res_forward_subsumption_resolution:     1
% 1.69/0.98  res_backward_subsumption_resolution:    0
% 1.69/0.98  res_clause_to_clause_subsumption:       40
% 1.69/0.98  res_orphan_elimination:                 0
% 1.69/0.98  res_tautology_del:                      17
% 1.69/0.98  res_num_eq_res_simplified:              0
% 1.69/0.98  res_num_sel_changes:                    0
% 1.69/0.98  res_moves_from_active_to_pass:          0
% 1.69/0.98  
% 1.69/0.98  ------ Superposition
% 1.69/0.98  
% 1.69/0.98  sup_time_total:                         0.
% 1.69/0.98  sup_time_generating:                    0.
% 1.69/0.98  sup_time_sim_full:                      0.
% 1.69/0.98  sup_time_sim_immed:                     0.
% 1.69/0.98  
% 1.69/0.98  sup_num_of_clauses:                     23
% 1.69/0.98  sup_num_in_active:                      8
% 1.69/0.98  sup_num_in_passive:                     15
% 1.69/0.98  sup_num_of_loops:                       24
% 1.69/0.98  sup_fw_superposition:                   12
% 1.69/0.98  sup_bw_superposition:                   9
% 1.69/0.98  sup_immediate_simplified:               13
% 1.69/0.98  sup_given_eliminated:                   0
% 1.69/0.98  comparisons_done:                       0
% 1.69/0.98  comparisons_avoided:                    3
% 1.69/0.98  
% 1.69/0.98  ------ Simplifications
% 1.69/0.98  
% 1.69/0.98  
% 1.69/0.98  sim_fw_subset_subsumed:                 10
% 1.69/0.98  sim_bw_subset_subsumed:                 0
% 1.69/0.98  sim_fw_subsumed:                        0
% 1.69/0.98  sim_bw_subsumed:                        1
% 1.69/0.98  sim_fw_subsumption_res:                 1
% 1.69/0.98  sim_bw_subsumption_res:                 0
% 1.69/0.98  sim_tautology_del:                      0
% 1.69/0.98  sim_eq_tautology_del:                   1
% 1.69/0.98  sim_eq_res_simp:                        0
% 1.69/0.98  sim_fw_demodulated:                     1
% 1.69/0.98  sim_bw_demodulated:                     16
% 1.69/0.98  sim_light_normalised:                   11
% 1.69/0.98  sim_joinable_taut:                      0
% 1.69/0.98  sim_joinable_simp:                      0
% 1.69/0.98  sim_ac_normalised:                      0
% 1.69/0.98  sim_smt_subsumption:                    0
% 1.69/0.98  
%------------------------------------------------------------------------------
