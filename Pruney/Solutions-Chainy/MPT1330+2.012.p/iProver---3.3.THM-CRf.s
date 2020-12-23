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
% DateTime   : Thu Dec  3 12:16:55 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  157 (1986 expanded)
%              Number of clauses        :   96 ( 588 expanded)
%              Number of leaves         :   17 ( 552 expanded)
%              Depth                    :   22
%              Number of atoms          :  479 (11326 expanded)
%              Number of equality atoms :  243 (4483 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

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

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f18])).

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
    inference(flattening,[],[f34])).

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f45,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1)
    & ( k1_xboole_0 = k2_struct_0(sK1)
      | k1_xboole_0 != k2_struct_0(sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_struct_0(sK2)
    & l1_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f44,f43,f42])).

fof(f73,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f69,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k1_xboole_0 != k2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f68])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f36])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f78,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f49])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_425,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK2) != X2
    | u1_struct_0(sK1) != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_426,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_428,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1))
    | k1_xboole_0 = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_426,c_28,c_26])).

cnf(c_16,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_20,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_364,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_16,c_20])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_368,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_364,c_20,c_16,c_14])).

cnf(c_369,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_368])).

cnf(c_446,plain,
    ( ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_369,c_26])).

cnf(c_447,plain,
    ( ~ v1_partfun1(sK3,X0)
    | k1_relat_1(sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_562,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | u1_struct_0(sK1) != X0
    | k1_relat_1(sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_428,c_447])).

cnf(c_563,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(sK3) = u1_struct_0(sK1)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0)) ),
    inference(unflattening,[status(thm)],[c_562])).

cnf(c_617,plain,
    ( sP0_iProver_split
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(sK3) = u1_struct_0(sK1) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_563])).

cnf(c_768,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | k1_relat_1(sK3) = u1_struct_0(sK1)
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_617])).

cnf(c_23,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_29,negated_conjecture,
    ( l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_312,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_29])).

cnf(c_313,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_30,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_317,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_318,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_798,plain,
    ( k2_struct_0(sK2) = k1_xboole_0
    | k2_struct_0(sK1) = k1_relat_1(sK3)
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_768,c_313,c_318])).

cnf(c_863,plain,
    ( sP0_iProver_split
    | k2_struct_0(sK2) = k1_xboole_0
    | k2_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_798])).

cnf(c_621,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_880,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_621])).

cnf(c_616,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_563])).

cnf(c_938,plain,
    ( ~ sP0_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_616])).

cnf(c_1003,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | k2_struct_0(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_798,c_863,c_880,c_938])).

cnf(c_1004,plain,
    ( k2_struct_0(sK2) = k1_xboole_0
    | k2_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_1003])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != k2_struct_0(sK2)
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1011,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1004,c_25])).

cnf(c_15,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_6,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_324,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_15,c_6])).

cnf(c_334,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_324,c_14])).

cnf(c_10,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_344,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X2)) = X0 ),
    inference(resolution,[status(thm)],[c_334,c_10])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relat_1(X0,k6_relat_1(X2)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_344,c_14])).

cnf(c_461,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_348,c_26])).

cnf(c_462,plain,
    ( k5_relat_1(sK3,k6_relat_1(X0)) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_831,plain,
    ( k5_relat_1(sK3,k6_relat_1(X0)) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_462,c_313,c_318])).

cnf(c_1268,plain,
    ( k5_relat_1(sK3,k6_relat_1(k2_struct_0(sK2))) = sK3 ),
    inference(equality_resolution,[status(thm)],[c_831])).

cnf(c_13,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_773,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_479,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_480,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_772,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_821,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_772,c_313,c_318])).

cnf(c_882,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_480])).

cnf(c_883,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_882])).

cnf(c_953,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_821,c_880,c_883])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_774,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2526,plain,
    ( k10_relat_1(sK3,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK3,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_953,c_774])).

cnf(c_2786,plain,
    ( k10_relat_1(sK3,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_773,c_2526])).

cnf(c_9,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2795,plain,
    ( k1_relat_1(k5_relat_1(sK3,k6_relat_1(X0))) = k10_relat_1(sK3,X0) ),
    inference(light_normalisation,[status(thm)],[c_2786,c_9])).

cnf(c_3024,plain,
    ( k10_relat_1(sK3,k2_struct_0(sK2)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1268,c_2795])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_470,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_471,plain,
    ( k8_relset_1(X0,X1,sK3,X2) = k10_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_842,plain,
    ( k8_relset_1(X0,X1,sK3,X2) = k10_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_471,c_313,c_318])).

cnf(c_1327,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(equality_resolution,[status(thm)],[c_842])).

cnf(c_24,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_795,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_24,c_313,c_318])).

cnf(c_1777,plain,
    ( k10_relat_1(sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1327,c_795])).

cnf(c_3161,plain,
    ( k2_struct_0(sK1) != k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_3024,c_1777])).

cnf(c_3165,plain,
    ( k2_struct_0(sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1011,c_3161])).

cnf(c_3167,plain,
    ( k1_relat_1(sK3) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3165,c_3161])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_408,plain,
    ( v1_partfun1(X0,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK2) != X1
    | u1_struct_0(sK1) != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_409,plain,
    ( v1_partfun1(sK3,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))))
    | ~ v1_funct_1(sK3)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_411,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))))
    | v1_partfun1(sK3,k1_xboole_0)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_409,c_28])).

cnf(c_412,plain,
    ( v1_partfun1(sK3,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))))
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_411])).

cnf(c_511,plain,
    ( v1_partfun1(sK3,k1_xboole_0)
    | u1_struct_0(sK1) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2)))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_412])).

cnf(c_547,plain,
    ( u1_struct_0(sK1) != k1_xboole_0
    | k1_relat_1(sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2)))
    | sK3 != sK3
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_511,c_447])).

cnf(c_548,plain,
    ( u1_struct_0(sK1) != k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_547])).

cnf(c_619,plain,
    ( sP1_iProver_split
    | u1_struct_0(sK1) != k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_548])).

cnf(c_770,plain,
    ( u1_struct_0(sK1) != k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2)))
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_619])).

cnf(c_847,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK2)))
    | sP1_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_770,c_313,c_318])).

cnf(c_2,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_848,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k1_xboole_0)
    | sP1_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_847,c_2])).

cnf(c_618,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_548])).

cnf(c_771,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_618])).

cnf(c_816,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k1_xboole_0)
    | sP1_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_771,c_2,c_313,c_318])).

cnf(c_853,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k1_xboole_0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_848,c_816])).

cnf(c_1456,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | k2_struct_0(sK1) != k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1004,c_853])).

cnf(c_1,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1461,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | k2_struct_0(sK1) != k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_1456,c_1])).

cnf(c_1462,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | k2_struct_0(sK1) != k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1461])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3167,c_3161,c_1462,c_1011])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.68/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.00  
% 1.68/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.68/1.00  
% 1.68/1.00  ------  iProver source info
% 1.68/1.00  
% 1.68/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.68/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.68/1.00  git: non_committed_changes: false
% 1.68/1.00  git: last_make_outside_of_git: false
% 1.68/1.00  
% 1.68/1.00  ------ 
% 1.68/1.00  
% 1.68/1.00  ------ Input Options
% 1.68/1.00  
% 1.68/1.00  --out_options                           all
% 1.68/1.00  --tptp_safe_out                         true
% 1.68/1.00  --problem_path                          ""
% 1.68/1.00  --include_path                          ""
% 1.68/1.00  --clausifier                            res/vclausify_rel
% 1.68/1.00  --clausifier_options                    --mode clausify
% 1.68/1.00  --stdin                                 false
% 1.68/1.00  --stats_out                             all
% 1.68/1.00  
% 1.68/1.00  ------ General Options
% 1.68/1.00  
% 1.68/1.00  --fof                                   false
% 1.68/1.00  --time_out_real                         305.
% 1.68/1.00  --time_out_virtual                      -1.
% 1.68/1.00  --symbol_type_check                     false
% 1.68/1.00  --clausify_out                          false
% 1.68/1.00  --sig_cnt_out                           false
% 1.68/1.00  --trig_cnt_out                          false
% 1.68/1.00  --trig_cnt_out_tolerance                1.
% 1.68/1.00  --trig_cnt_out_sk_spl                   false
% 1.68/1.00  --abstr_cl_out                          false
% 1.68/1.00  
% 1.68/1.00  ------ Global Options
% 1.68/1.00  
% 1.68/1.00  --schedule                              default
% 1.68/1.00  --add_important_lit                     false
% 1.68/1.00  --prop_solver_per_cl                    1000
% 1.68/1.00  --min_unsat_core                        false
% 1.68/1.00  --soft_assumptions                      false
% 1.68/1.00  --soft_lemma_size                       3
% 1.68/1.00  --prop_impl_unit_size                   0
% 1.68/1.00  --prop_impl_unit                        []
% 1.68/1.00  --share_sel_clauses                     true
% 1.68/1.00  --reset_solvers                         false
% 1.68/1.00  --bc_imp_inh                            [conj_cone]
% 1.68/1.00  --conj_cone_tolerance                   3.
% 1.68/1.00  --extra_neg_conj                        none
% 1.68/1.00  --large_theory_mode                     true
% 1.68/1.00  --prolific_symb_bound                   200
% 1.68/1.00  --lt_threshold                          2000
% 1.68/1.00  --clause_weak_htbl                      true
% 1.68/1.00  --gc_record_bc_elim                     false
% 1.68/1.00  
% 1.68/1.00  ------ Preprocessing Options
% 1.68/1.00  
% 1.68/1.00  --preprocessing_flag                    true
% 1.68/1.00  --time_out_prep_mult                    0.1
% 1.68/1.00  --splitting_mode                        input
% 1.68/1.00  --splitting_grd                         true
% 1.68/1.00  --splitting_cvd                         false
% 1.68/1.00  --splitting_cvd_svl                     false
% 1.68/1.00  --splitting_nvd                         32
% 1.68/1.00  --sub_typing                            true
% 1.68/1.00  --prep_gs_sim                           true
% 1.68/1.00  --prep_unflatten                        true
% 1.68/1.00  --prep_res_sim                          true
% 1.68/1.00  --prep_upred                            true
% 1.68/1.00  --prep_sem_filter                       exhaustive
% 1.68/1.00  --prep_sem_filter_out                   false
% 1.68/1.00  --pred_elim                             true
% 1.68/1.00  --res_sim_input                         true
% 1.68/1.00  --eq_ax_congr_red                       true
% 1.68/1.00  --pure_diseq_elim                       true
% 1.68/1.00  --brand_transform                       false
% 1.68/1.00  --non_eq_to_eq                          false
% 1.68/1.00  --prep_def_merge                        true
% 1.68/1.00  --prep_def_merge_prop_impl              false
% 1.68/1.00  --prep_def_merge_mbd                    true
% 1.68/1.00  --prep_def_merge_tr_red                 false
% 1.68/1.00  --prep_def_merge_tr_cl                  false
% 1.68/1.00  --smt_preprocessing                     true
% 1.68/1.00  --smt_ac_axioms                         fast
% 1.68/1.00  --preprocessed_out                      false
% 1.68/1.00  --preprocessed_stats                    false
% 1.68/1.00  
% 1.68/1.00  ------ Abstraction refinement Options
% 1.68/1.00  
% 1.68/1.00  --abstr_ref                             []
% 1.68/1.00  --abstr_ref_prep                        false
% 1.68/1.00  --abstr_ref_until_sat                   false
% 1.68/1.00  --abstr_ref_sig_restrict                funpre
% 1.68/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.68/1.00  --abstr_ref_under                       []
% 1.68/1.00  
% 1.68/1.00  ------ SAT Options
% 1.68/1.00  
% 1.68/1.00  --sat_mode                              false
% 1.68/1.00  --sat_fm_restart_options                ""
% 1.68/1.00  --sat_gr_def                            false
% 1.68/1.00  --sat_epr_types                         true
% 1.68/1.00  --sat_non_cyclic_types                  false
% 1.68/1.00  --sat_finite_models                     false
% 1.68/1.00  --sat_fm_lemmas                         false
% 1.68/1.00  --sat_fm_prep                           false
% 1.68/1.00  --sat_fm_uc_incr                        true
% 1.68/1.00  --sat_out_model                         small
% 1.68/1.00  --sat_out_clauses                       false
% 1.68/1.00  
% 1.68/1.00  ------ QBF Options
% 1.68/1.00  
% 1.68/1.00  --qbf_mode                              false
% 1.68/1.00  --qbf_elim_univ                         false
% 1.68/1.00  --qbf_dom_inst                          none
% 1.68/1.00  --qbf_dom_pre_inst                      false
% 1.68/1.00  --qbf_sk_in                             false
% 1.68/1.00  --qbf_pred_elim                         true
% 1.68/1.00  --qbf_split                             512
% 1.68/1.00  
% 1.68/1.00  ------ BMC1 Options
% 1.68/1.00  
% 1.68/1.00  --bmc1_incremental                      false
% 1.68/1.00  --bmc1_axioms                           reachable_all
% 1.68/1.00  --bmc1_min_bound                        0
% 1.68/1.00  --bmc1_max_bound                        -1
% 1.68/1.00  --bmc1_max_bound_default                -1
% 1.68/1.00  --bmc1_symbol_reachability              true
% 1.68/1.00  --bmc1_property_lemmas                  false
% 1.68/1.00  --bmc1_k_induction                      false
% 1.68/1.00  --bmc1_non_equiv_states                 false
% 1.68/1.00  --bmc1_deadlock                         false
% 1.68/1.00  --bmc1_ucm                              false
% 1.68/1.00  --bmc1_add_unsat_core                   none
% 1.68/1.00  --bmc1_unsat_core_children              false
% 1.68/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.68/1.00  --bmc1_out_stat                         full
% 1.68/1.00  --bmc1_ground_init                      false
% 1.68/1.00  --bmc1_pre_inst_next_state              false
% 1.68/1.00  --bmc1_pre_inst_state                   false
% 1.68/1.00  --bmc1_pre_inst_reach_state             false
% 1.68/1.00  --bmc1_out_unsat_core                   false
% 1.68/1.00  --bmc1_aig_witness_out                  false
% 1.68/1.00  --bmc1_verbose                          false
% 1.68/1.00  --bmc1_dump_clauses_tptp                false
% 1.68/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.68/1.00  --bmc1_dump_file                        -
% 1.68/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.68/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.68/1.00  --bmc1_ucm_extend_mode                  1
% 1.68/1.00  --bmc1_ucm_init_mode                    2
% 1.68/1.00  --bmc1_ucm_cone_mode                    none
% 1.68/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.68/1.00  --bmc1_ucm_relax_model                  4
% 1.68/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.68/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.68/1.00  --bmc1_ucm_layered_model                none
% 1.68/1.00  --bmc1_ucm_max_lemma_size               10
% 1.68/1.00  
% 1.68/1.00  ------ AIG Options
% 1.68/1.00  
% 1.68/1.00  --aig_mode                              false
% 1.68/1.00  
% 1.68/1.00  ------ Instantiation Options
% 1.68/1.00  
% 1.68/1.00  --instantiation_flag                    true
% 1.68/1.00  --inst_sos_flag                         false
% 1.68/1.00  --inst_sos_phase                        true
% 1.68/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.68/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.68/1.00  --inst_lit_sel_side                     num_symb
% 1.68/1.00  --inst_solver_per_active                1400
% 1.68/1.00  --inst_solver_calls_frac                1.
% 1.68/1.00  --inst_passive_queue_type               priority_queues
% 1.68/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.68/1.00  --inst_passive_queues_freq              [25;2]
% 1.68/1.00  --inst_dismatching                      true
% 1.68/1.00  --inst_eager_unprocessed_to_passive     true
% 1.68/1.00  --inst_prop_sim_given                   true
% 1.68/1.00  --inst_prop_sim_new                     false
% 1.68/1.00  --inst_subs_new                         false
% 1.68/1.00  --inst_eq_res_simp                      false
% 1.68/1.00  --inst_subs_given                       false
% 1.68/1.00  --inst_orphan_elimination               true
% 1.68/1.00  --inst_learning_loop_flag               true
% 1.68/1.00  --inst_learning_start                   3000
% 1.68/1.00  --inst_learning_factor                  2
% 1.68/1.00  --inst_start_prop_sim_after_learn       3
% 1.68/1.00  --inst_sel_renew                        solver
% 1.68/1.00  --inst_lit_activity_flag                true
% 1.68/1.00  --inst_restr_to_given                   false
% 1.68/1.00  --inst_activity_threshold               500
% 1.68/1.00  --inst_out_proof                        true
% 1.68/1.00  
% 1.68/1.00  ------ Resolution Options
% 1.68/1.00  
% 1.68/1.00  --resolution_flag                       true
% 1.68/1.00  --res_lit_sel                           adaptive
% 1.68/1.00  --res_lit_sel_side                      none
% 1.68/1.00  --res_ordering                          kbo
% 1.68/1.00  --res_to_prop_solver                    active
% 1.68/1.00  --res_prop_simpl_new                    false
% 1.68/1.00  --res_prop_simpl_given                  true
% 1.68/1.00  --res_passive_queue_type                priority_queues
% 1.68/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.68/1.00  --res_passive_queues_freq               [15;5]
% 1.68/1.00  --res_forward_subs                      full
% 1.68/1.00  --res_backward_subs                     full
% 1.68/1.00  --res_forward_subs_resolution           true
% 1.68/1.00  --res_backward_subs_resolution          true
% 1.68/1.00  --res_orphan_elimination                true
% 1.68/1.00  --res_time_limit                        2.
% 1.68/1.00  --res_out_proof                         true
% 1.68/1.00  
% 1.68/1.00  ------ Superposition Options
% 1.68/1.00  
% 1.68/1.00  --superposition_flag                    true
% 1.68/1.00  --sup_passive_queue_type                priority_queues
% 1.68/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.68/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.68/1.00  --demod_completeness_check              fast
% 1.68/1.00  --demod_use_ground                      true
% 1.68/1.00  --sup_to_prop_solver                    passive
% 1.68/1.00  --sup_prop_simpl_new                    true
% 1.68/1.00  --sup_prop_simpl_given                  true
% 1.68/1.00  --sup_fun_splitting                     false
% 1.68/1.00  --sup_smt_interval                      50000
% 1.68/1.00  
% 1.68/1.00  ------ Superposition Simplification Setup
% 1.68/1.00  
% 1.68/1.00  --sup_indices_passive                   []
% 1.68/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.68/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/1.00  --sup_full_bw                           [BwDemod]
% 1.68/1.00  --sup_immed_triv                        [TrivRules]
% 1.68/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.68/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/1.00  --sup_immed_bw_main                     []
% 1.68/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.68/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.68/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.68/1.00  
% 1.68/1.00  ------ Combination Options
% 1.68/1.00  
% 1.68/1.00  --comb_res_mult                         3
% 1.68/1.00  --comb_sup_mult                         2
% 1.68/1.00  --comb_inst_mult                        10
% 1.68/1.00  
% 1.68/1.00  ------ Debug Options
% 1.68/1.00  
% 1.68/1.00  --dbg_backtrace                         false
% 1.68/1.00  --dbg_dump_prop_clauses                 false
% 1.68/1.00  --dbg_dump_prop_clauses_file            -
% 1.68/1.00  --dbg_out_stat                          false
% 1.68/1.00  ------ Parsing...
% 1.68/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.68/1.00  
% 1.68/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 10 0s  sf_e  pe_s  pe_e 
% 1.68/1.00  
% 1.68/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.68/1.00  
% 1.68/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.68/1.00  ------ Proving...
% 1.68/1.00  ------ Problem Properties 
% 1.68/1.00  
% 1.68/1.00  
% 1.68/1.00  clauses                                 20
% 1.68/1.00  conjectures                             2
% 1.68/1.00  EPR                                     0
% 1.68/1.00  Horn                                    17
% 1.68/1.00  unary                                   9
% 1.68/1.00  binary                                  7
% 1.68/1.00  lits                                    36
% 1.68/1.00  lits eq                                 28
% 1.68/1.00  fd_pure                                 0
% 1.68/1.00  fd_pseudo                               0
% 1.68/1.00  fd_cond                                 1
% 1.68/1.00  fd_pseudo_cond                          0
% 1.68/1.00  AC symbols                              0
% 1.68/1.00  
% 1.68/1.00  ------ Schedule dynamic 5 is on 
% 1.68/1.00  
% 1.68/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.68/1.00  
% 1.68/1.00  
% 1.68/1.00  ------ 
% 1.68/1.00  Current options:
% 1.68/1.00  ------ 
% 1.68/1.00  
% 1.68/1.00  ------ Input Options
% 1.68/1.00  
% 1.68/1.00  --out_options                           all
% 1.68/1.00  --tptp_safe_out                         true
% 1.68/1.00  --problem_path                          ""
% 1.68/1.00  --include_path                          ""
% 1.68/1.00  --clausifier                            res/vclausify_rel
% 1.68/1.00  --clausifier_options                    --mode clausify
% 1.68/1.00  --stdin                                 false
% 1.68/1.00  --stats_out                             all
% 1.68/1.00  
% 1.68/1.00  ------ General Options
% 1.68/1.00  
% 1.68/1.00  --fof                                   false
% 1.68/1.00  --time_out_real                         305.
% 1.68/1.00  --time_out_virtual                      -1.
% 1.68/1.00  --symbol_type_check                     false
% 1.68/1.00  --clausify_out                          false
% 1.68/1.00  --sig_cnt_out                           false
% 1.68/1.00  --trig_cnt_out                          false
% 1.68/1.00  --trig_cnt_out_tolerance                1.
% 1.68/1.00  --trig_cnt_out_sk_spl                   false
% 1.68/1.00  --abstr_cl_out                          false
% 1.68/1.00  
% 1.68/1.00  ------ Global Options
% 1.68/1.00  
% 1.68/1.00  --schedule                              default
% 1.68/1.00  --add_important_lit                     false
% 1.68/1.00  --prop_solver_per_cl                    1000
% 1.68/1.00  --min_unsat_core                        false
% 1.68/1.00  --soft_assumptions                      false
% 1.68/1.00  --soft_lemma_size                       3
% 1.68/1.00  --prop_impl_unit_size                   0
% 1.68/1.00  --prop_impl_unit                        []
% 1.68/1.00  --share_sel_clauses                     true
% 1.68/1.00  --reset_solvers                         false
% 1.68/1.00  --bc_imp_inh                            [conj_cone]
% 1.68/1.00  --conj_cone_tolerance                   3.
% 1.68/1.00  --extra_neg_conj                        none
% 1.68/1.00  --large_theory_mode                     true
% 1.68/1.00  --prolific_symb_bound                   200
% 1.68/1.00  --lt_threshold                          2000
% 1.68/1.00  --clause_weak_htbl                      true
% 1.68/1.00  --gc_record_bc_elim                     false
% 1.68/1.00  
% 1.68/1.00  ------ Preprocessing Options
% 1.68/1.00  
% 1.68/1.00  --preprocessing_flag                    true
% 1.68/1.00  --time_out_prep_mult                    0.1
% 1.68/1.00  --splitting_mode                        input
% 1.68/1.00  --splitting_grd                         true
% 1.68/1.00  --splitting_cvd                         false
% 1.68/1.00  --splitting_cvd_svl                     false
% 1.68/1.00  --splitting_nvd                         32
% 1.68/1.00  --sub_typing                            true
% 1.68/1.00  --prep_gs_sim                           true
% 1.68/1.00  --prep_unflatten                        true
% 1.68/1.00  --prep_res_sim                          true
% 1.68/1.00  --prep_upred                            true
% 1.68/1.00  --prep_sem_filter                       exhaustive
% 1.68/1.00  --prep_sem_filter_out                   false
% 1.68/1.00  --pred_elim                             true
% 1.68/1.00  --res_sim_input                         true
% 1.68/1.00  --eq_ax_congr_red                       true
% 1.68/1.00  --pure_diseq_elim                       true
% 1.68/1.00  --brand_transform                       false
% 1.68/1.00  --non_eq_to_eq                          false
% 1.68/1.00  --prep_def_merge                        true
% 1.68/1.00  --prep_def_merge_prop_impl              false
% 1.68/1.00  --prep_def_merge_mbd                    true
% 1.68/1.00  --prep_def_merge_tr_red                 false
% 1.68/1.00  --prep_def_merge_tr_cl                  false
% 1.68/1.00  --smt_preprocessing                     true
% 1.68/1.00  --smt_ac_axioms                         fast
% 1.68/1.00  --preprocessed_out                      false
% 1.68/1.00  --preprocessed_stats                    false
% 1.68/1.00  
% 1.68/1.00  ------ Abstraction refinement Options
% 1.68/1.00  
% 1.68/1.00  --abstr_ref                             []
% 1.68/1.00  --abstr_ref_prep                        false
% 1.68/1.00  --abstr_ref_until_sat                   false
% 1.68/1.00  --abstr_ref_sig_restrict                funpre
% 1.68/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.68/1.00  --abstr_ref_under                       []
% 1.68/1.00  
% 1.68/1.00  ------ SAT Options
% 1.68/1.00  
% 1.68/1.00  --sat_mode                              false
% 1.68/1.00  --sat_fm_restart_options                ""
% 1.68/1.00  --sat_gr_def                            false
% 1.68/1.00  --sat_epr_types                         true
% 1.68/1.00  --sat_non_cyclic_types                  false
% 1.68/1.00  --sat_finite_models                     false
% 1.68/1.00  --sat_fm_lemmas                         false
% 1.68/1.00  --sat_fm_prep                           false
% 1.68/1.00  --sat_fm_uc_incr                        true
% 1.68/1.00  --sat_out_model                         small
% 1.68/1.00  --sat_out_clauses                       false
% 1.68/1.00  
% 1.68/1.00  ------ QBF Options
% 1.68/1.00  
% 1.68/1.00  --qbf_mode                              false
% 1.68/1.00  --qbf_elim_univ                         false
% 1.68/1.00  --qbf_dom_inst                          none
% 1.68/1.00  --qbf_dom_pre_inst                      false
% 1.68/1.00  --qbf_sk_in                             false
% 1.68/1.00  --qbf_pred_elim                         true
% 1.68/1.00  --qbf_split                             512
% 1.68/1.00  
% 1.68/1.00  ------ BMC1 Options
% 1.68/1.00  
% 1.68/1.00  --bmc1_incremental                      false
% 1.68/1.00  --bmc1_axioms                           reachable_all
% 1.68/1.00  --bmc1_min_bound                        0
% 1.68/1.00  --bmc1_max_bound                        -1
% 1.68/1.00  --bmc1_max_bound_default                -1
% 1.68/1.00  --bmc1_symbol_reachability              true
% 1.68/1.00  --bmc1_property_lemmas                  false
% 1.68/1.00  --bmc1_k_induction                      false
% 1.68/1.00  --bmc1_non_equiv_states                 false
% 1.68/1.00  --bmc1_deadlock                         false
% 1.68/1.00  --bmc1_ucm                              false
% 1.68/1.00  --bmc1_add_unsat_core                   none
% 1.68/1.00  --bmc1_unsat_core_children              false
% 1.68/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.68/1.00  --bmc1_out_stat                         full
% 1.68/1.00  --bmc1_ground_init                      false
% 1.68/1.00  --bmc1_pre_inst_next_state              false
% 1.68/1.00  --bmc1_pre_inst_state                   false
% 1.68/1.00  --bmc1_pre_inst_reach_state             false
% 1.68/1.00  --bmc1_out_unsat_core                   false
% 1.68/1.00  --bmc1_aig_witness_out                  false
% 1.68/1.00  --bmc1_verbose                          false
% 1.68/1.00  --bmc1_dump_clauses_tptp                false
% 1.68/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.68/1.00  --bmc1_dump_file                        -
% 1.68/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.68/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.68/1.00  --bmc1_ucm_extend_mode                  1
% 1.68/1.00  --bmc1_ucm_init_mode                    2
% 1.68/1.00  --bmc1_ucm_cone_mode                    none
% 1.68/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.68/1.00  --bmc1_ucm_relax_model                  4
% 1.68/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.68/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.68/1.00  --bmc1_ucm_layered_model                none
% 1.68/1.00  --bmc1_ucm_max_lemma_size               10
% 1.68/1.00  
% 1.68/1.00  ------ AIG Options
% 1.68/1.00  
% 1.68/1.00  --aig_mode                              false
% 1.68/1.00  
% 1.68/1.00  ------ Instantiation Options
% 1.68/1.00  
% 1.68/1.00  --instantiation_flag                    true
% 1.68/1.00  --inst_sos_flag                         false
% 1.68/1.00  --inst_sos_phase                        true
% 1.68/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.68/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.68/1.00  --inst_lit_sel_side                     none
% 1.68/1.00  --inst_solver_per_active                1400
% 1.68/1.00  --inst_solver_calls_frac                1.
% 1.68/1.00  --inst_passive_queue_type               priority_queues
% 1.68/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.68/1.00  --inst_passive_queues_freq              [25;2]
% 1.68/1.00  --inst_dismatching                      true
% 1.68/1.00  --inst_eager_unprocessed_to_passive     true
% 1.68/1.00  --inst_prop_sim_given                   true
% 1.68/1.00  --inst_prop_sim_new                     false
% 1.68/1.00  --inst_subs_new                         false
% 1.68/1.00  --inst_eq_res_simp                      false
% 1.68/1.00  --inst_subs_given                       false
% 1.68/1.00  --inst_orphan_elimination               true
% 1.68/1.00  --inst_learning_loop_flag               true
% 1.68/1.00  --inst_learning_start                   3000
% 1.68/1.00  --inst_learning_factor                  2
% 1.68/1.00  --inst_start_prop_sim_after_learn       3
% 1.68/1.00  --inst_sel_renew                        solver
% 1.68/1.00  --inst_lit_activity_flag                true
% 1.68/1.00  --inst_restr_to_given                   false
% 1.68/1.00  --inst_activity_threshold               500
% 1.68/1.00  --inst_out_proof                        true
% 1.68/1.00  
% 1.68/1.00  ------ Resolution Options
% 1.68/1.00  
% 1.68/1.00  --resolution_flag                       false
% 1.68/1.00  --res_lit_sel                           adaptive
% 1.68/1.00  --res_lit_sel_side                      none
% 1.68/1.00  --res_ordering                          kbo
% 1.68/1.00  --res_to_prop_solver                    active
% 1.68/1.00  --res_prop_simpl_new                    false
% 1.68/1.00  --res_prop_simpl_given                  true
% 1.68/1.00  --res_passive_queue_type                priority_queues
% 1.68/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.68/1.00  --res_passive_queues_freq               [15;5]
% 1.68/1.00  --res_forward_subs                      full
% 1.68/1.00  --res_backward_subs                     full
% 1.68/1.00  --res_forward_subs_resolution           true
% 1.68/1.00  --res_backward_subs_resolution          true
% 1.68/1.00  --res_orphan_elimination                true
% 1.68/1.00  --res_time_limit                        2.
% 1.68/1.00  --res_out_proof                         true
% 1.68/1.00  
% 1.68/1.00  ------ Superposition Options
% 1.68/1.00  
% 1.68/1.00  --superposition_flag                    true
% 1.68/1.00  --sup_passive_queue_type                priority_queues
% 1.68/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.68/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.68/1.00  --demod_completeness_check              fast
% 1.68/1.00  --demod_use_ground                      true
% 1.68/1.00  --sup_to_prop_solver                    passive
% 1.68/1.00  --sup_prop_simpl_new                    true
% 1.68/1.00  --sup_prop_simpl_given                  true
% 1.68/1.00  --sup_fun_splitting                     false
% 1.68/1.00  --sup_smt_interval                      50000
% 1.68/1.00  
% 1.68/1.00  ------ Superposition Simplification Setup
% 1.68/1.00  
% 1.68/1.00  --sup_indices_passive                   []
% 1.68/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.68/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.68/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/1.00  --sup_full_bw                           [BwDemod]
% 1.68/1.00  --sup_immed_triv                        [TrivRules]
% 1.68/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.68/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/1.00  --sup_immed_bw_main                     []
% 1.68/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.68/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.68/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.68/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.68/1.00  
% 1.68/1.00  ------ Combination Options
% 1.68/1.00  
% 1.68/1.00  --comb_res_mult                         3
% 1.68/1.00  --comb_sup_mult                         2
% 1.68/1.00  --comb_inst_mult                        10
% 1.68/1.00  
% 1.68/1.00  ------ Debug Options
% 1.68/1.00  
% 1.68/1.00  --dbg_backtrace                         false
% 1.68/1.00  --dbg_dump_prop_clauses                 false
% 1.68/1.00  --dbg_dump_prop_clauses_file            -
% 1.68/1.00  --dbg_out_stat                          false
% 1.68/1.00  
% 1.68/1.00  
% 1.68/1.00  
% 1.68/1.00  
% 1.68/1.00  ------ Proving...
% 1.68/1.00  
% 1.68/1.00  
% 1.68/1.00  % SZS status Theorem for theBenchmark.p
% 1.68/1.00  
% 1.68/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.68/1.00  
% 1.68/1.00  fof(f15,axiom,(
% 1.68/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/1.00  
% 1.68/1.00  fof(f31,plain,(
% 1.68/1.00    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.68/1.00    inference(ennf_transformation,[],[f15])).
% 1.68/1.00  
% 1.68/1.00  fof(f32,plain,(
% 1.68/1.00    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.68/1.00    inference(flattening,[],[f31])).
% 1.68/1.00  
% 1.68/1.00  fof(f67,plain,(
% 1.68/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.68/1.00    inference(cnf_transformation,[],[f32])).
% 1.68/1.00  
% 1.68/1.00  fof(f17,conjecture,(
% 1.68/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 1.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/1.00  
% 1.68/1.00  fof(f18,negated_conjecture,(
% 1.68/1.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 1.68/1.00    inference(negated_conjecture,[],[f17])).
% 1.68/1.00  
% 1.68/1.00  fof(f34,plain,(
% 1.68/1.00    ? [X0] : (? [X1] : (? [X2] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 1.68/1.00    inference(ennf_transformation,[],[f18])).
% 1.68/1.00  
% 1.68/1.00  fof(f35,plain,(
% 1.68/1.00    ? [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 1.68/1.00    inference(flattening,[],[f34])).
% 1.68/1.00  
% 1.68/1.00  fof(f44,plain,(
% 1.68/1.00    ( ! [X0,X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 1.68/1.00    introduced(choice_axiom,[])).
% 1.68/1.00  
% 1.68/1.00  fof(f43,plain,(
% 1.68/1.00    ( ! [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2,k2_struct_0(sK2)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(sK2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_struct_0(sK2))) )),
% 1.68/1.00    introduced(choice_axiom,[])).
% 1.68/1.00  
% 1.68/1.00  fof(f42,plain,(
% 1.68/1.00    ? [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(sK1) & (k1_xboole_0 = k2_struct_0(sK1) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK1))),
% 1.68/1.00    introduced(choice_axiom,[])).
% 1.68/1.00  
% 1.68/1.00  fof(f45,plain,(
% 1.68/1.00    ((k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) & (k1_xboole_0 = k2_struct_0(sK1) | k1_xboole_0 != k2_struct_0(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_struct_0(sK2)) & l1_struct_0(sK1)),
% 1.68/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f44,f43,f42])).
% 1.68/1.00  
% 1.68/1.00  fof(f73,plain,(
% 1.68/1.00    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 1.68/1.00    inference(cnf_transformation,[],[f45])).
% 1.68/1.00  
% 1.68/1.00  fof(f72,plain,(
% 1.68/1.00    v1_funct_1(sK3)),
% 1.68/1.00    inference(cnf_transformation,[],[f45])).
% 1.68/1.00  
% 1.68/1.00  fof(f74,plain,(
% 1.68/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 1.68/1.00    inference(cnf_transformation,[],[f45])).
% 1.68/1.00  
% 1.68/1.00  fof(f11,axiom,(
% 1.68/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/1.00  
% 1.68/1.00  fof(f26,plain,(
% 1.68/1.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.68/1.00    inference(ennf_transformation,[],[f11])).
% 1.68/1.00  
% 1.68/1.00  fof(f61,plain,(
% 1.68/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.68/1.00    inference(cnf_transformation,[],[f26])).
% 1.68/1.00  
% 1.68/1.00  fof(f14,axiom,(
% 1.68/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/1.00  
% 1.68/1.00  fof(f29,plain,(
% 1.68/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.68/1.00    inference(ennf_transformation,[],[f14])).
% 1.68/1.00  
% 1.68/1.00  fof(f30,plain,(
% 1.68/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.68/1.00    inference(flattening,[],[f29])).
% 1.68/1.00  
% 1.68/1.00  fof(f41,plain,(
% 1.68/1.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.68/1.00    inference(nnf_transformation,[],[f30])).
% 1.68/1.00  
% 1.68/1.00  fof(f65,plain,(
% 1.68/1.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.68/1.00    inference(cnf_transformation,[],[f41])).
% 1.68/1.00  
% 1.68/1.00  fof(f10,axiom,(
% 1.68/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/1.00  
% 1.68/1.00  fof(f25,plain,(
% 1.68/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.68/1.00    inference(ennf_transformation,[],[f10])).
% 1.68/1.00  
% 1.68/1.00  fof(f60,plain,(
% 1.68/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.68/1.00    inference(cnf_transformation,[],[f25])).
% 1.68/1.00  
% 1.68/1.00  fof(f16,axiom,(
% 1.68/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/1.00  
% 1.68/1.00  fof(f33,plain,(
% 1.68/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.68/1.00    inference(ennf_transformation,[],[f16])).
% 1.68/1.00  
% 1.68/1.00  fof(f69,plain,(
% 1.68/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.68/1.00    inference(cnf_transformation,[],[f33])).
% 1.68/1.00  
% 1.68/1.00  fof(f71,plain,(
% 1.68/1.00    l1_struct_0(sK2)),
% 1.68/1.00    inference(cnf_transformation,[],[f45])).
% 1.68/1.00  
% 1.68/1.00  fof(f70,plain,(
% 1.68/1.00    l1_struct_0(sK1)),
% 1.68/1.00    inference(cnf_transformation,[],[f45])).
% 1.68/1.00  
% 1.68/1.00  fof(f75,plain,(
% 1.68/1.00    k1_xboole_0 = k2_struct_0(sK1) | k1_xboole_0 != k2_struct_0(sK2)),
% 1.68/1.00    inference(cnf_transformation,[],[f45])).
% 1.68/1.00  
% 1.68/1.00  fof(f62,plain,(
% 1.68/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.68/1.00    inference(cnf_transformation,[],[f26])).
% 1.68/1.00  
% 1.68/1.00  fof(f4,axiom,(
% 1.68/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/1.00  
% 1.68/1.00  fof(f21,plain,(
% 1.68/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.68/1.00    inference(ennf_transformation,[],[f4])).
% 1.68/1.00  
% 1.68/1.00  fof(f38,plain,(
% 1.68/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.68/1.00    inference(nnf_transformation,[],[f21])).
% 1.68/1.00  
% 1.68/1.00  fof(f51,plain,(
% 1.68/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.68/1.00    inference(cnf_transformation,[],[f38])).
% 1.68/1.00  
% 1.68/1.00  fof(f7,axiom,(
% 1.68/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/1.00  
% 1.68/1.00  fof(f23,plain,(
% 1.68/1.00    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.68/1.00    inference(ennf_transformation,[],[f7])).
% 1.68/1.00  
% 1.68/1.00  fof(f24,plain,(
% 1.68/1.00    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.68/1.00    inference(flattening,[],[f23])).
% 1.68/1.00  
% 1.68/1.00  fof(f56,plain,(
% 1.68/1.00    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.68/1.00    inference(cnf_transformation,[],[f24])).
% 1.68/1.00  
% 1.68/1.00  fof(f9,axiom,(
% 1.68/1.00    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/1.00  
% 1.68/1.00  fof(f58,plain,(
% 1.68/1.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.68/1.00    inference(cnf_transformation,[],[f9])).
% 1.68/1.00  
% 1.68/1.00  fof(f5,axiom,(
% 1.68/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/1.00  
% 1.68/1.00  fof(f22,plain,(
% 1.68/1.00    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.68/1.00    inference(ennf_transformation,[],[f5])).
% 1.68/1.00  
% 1.68/1.00  fof(f53,plain,(
% 1.68/1.00    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.68/1.00    inference(cnf_transformation,[],[f22])).
% 1.68/1.00  
% 1.68/1.00  fof(f6,axiom,(
% 1.68/1.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/1.00  
% 1.68/1.00  fof(f54,plain,(
% 1.68/1.00    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.68/1.00    inference(cnf_transformation,[],[f6])).
% 1.68/1.00  
% 1.68/1.00  fof(f12,axiom,(
% 1.68/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 1.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/1.00  
% 1.68/1.00  fof(f27,plain,(
% 1.68/1.00    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.68/1.00    inference(ennf_transformation,[],[f12])).
% 1.68/1.00  
% 1.68/1.00  fof(f63,plain,(
% 1.68/1.00    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.68/1.00    inference(cnf_transformation,[],[f27])).
% 1.68/1.00  
% 1.68/1.00  fof(f76,plain,(
% 1.68/1.00    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1)),
% 1.68/1.00    inference(cnf_transformation,[],[f45])).
% 1.68/1.00  
% 1.68/1.00  fof(f68,plain,(
% 1.68/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.68/1.00    inference(cnf_transformation,[],[f32])).
% 1.68/1.00  
% 1.68/1.00  fof(f80,plain,(
% 1.68/1.00    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 1.68/1.00    inference(equality_resolution,[],[f68])).
% 1.68/1.00  
% 1.68/1.00  fof(f2,axiom,(
% 1.68/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.68/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.68/1.00  
% 1.68/1.00  fof(f36,plain,(
% 1.68/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.68/1.00    inference(nnf_transformation,[],[f2])).
% 1.68/1.00  
% 1.68/1.00  fof(f37,plain,(
% 1.68/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.68/1.00    inference(flattening,[],[f36])).
% 1.68/1.00  
% 1.68/1.00  fof(f48,plain,(
% 1.68/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.68/1.00    inference(cnf_transformation,[],[f37])).
% 1.68/1.00  
% 1.68/1.00  fof(f78,plain,(
% 1.68/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.68/1.00    inference(equality_resolution,[],[f48])).
% 1.68/1.00  
% 1.68/1.00  fof(f49,plain,(
% 1.68/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.68/1.00    inference(cnf_transformation,[],[f37])).
% 1.68/1.00  
% 1.68/1.00  fof(f77,plain,(
% 1.68/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.68/1.00    inference(equality_resolution,[],[f49])).
% 1.68/1.00  
% 1.68/1.00  cnf(c_22,plain,
% 1.68/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.68/1.00      | v1_partfun1(X0,X1)
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.68/1.00      | ~ v1_funct_1(X0)
% 1.68/1.00      | k1_xboole_0 = X2 ),
% 1.68/1.00      inference(cnf_transformation,[],[f67]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_27,negated_conjecture,
% 1.68/1.00      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 1.68/1.00      inference(cnf_transformation,[],[f73]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_425,plain,
% 1.68/1.00      ( v1_partfun1(X0,X1)
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.68/1.00      | ~ v1_funct_1(X0)
% 1.68/1.00      | u1_struct_0(sK2) != X2
% 1.68/1.00      | u1_struct_0(sK1) != X1
% 1.68/1.00      | sK3 != X0
% 1.68/1.00      | k1_xboole_0 = X2 ),
% 1.68/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_426,plain,
% 1.68/1.00      ( v1_partfun1(sK3,u1_struct_0(sK1))
% 1.68/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 1.68/1.00      | ~ v1_funct_1(sK3)
% 1.68/1.00      | k1_xboole_0 = u1_struct_0(sK2) ),
% 1.68/1.00      inference(unflattening,[status(thm)],[c_425]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_28,negated_conjecture,
% 1.68/1.00      ( v1_funct_1(sK3) ),
% 1.68/1.00      inference(cnf_transformation,[],[f72]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_26,negated_conjecture,
% 1.68/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 1.68/1.00      inference(cnf_transformation,[],[f74]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_428,plain,
% 1.68/1.00      ( v1_partfun1(sK3,u1_struct_0(sK1))
% 1.68/1.00      | k1_xboole_0 = u1_struct_0(sK2) ),
% 1.68/1.00      inference(global_propositional_subsumption,
% 1.68/1.00                [status(thm)],
% 1.68/1.00                [c_426,c_28,c_26]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_16,plain,
% 1.68/1.00      ( v4_relat_1(X0,X1)
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.68/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_20,plain,
% 1.68/1.00      ( ~ v1_partfun1(X0,X1)
% 1.68/1.00      | ~ v4_relat_1(X0,X1)
% 1.68/1.00      | ~ v1_relat_1(X0)
% 1.68/1.00      | k1_relat_1(X0) = X1 ),
% 1.68/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_364,plain,
% 1.68/1.00      ( ~ v1_partfun1(X0,X1)
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.68/1.00      | ~ v1_relat_1(X0)
% 1.68/1.00      | k1_relat_1(X0) = X1 ),
% 1.68/1.00      inference(resolution,[status(thm)],[c_16,c_20]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_14,plain,
% 1.68/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.68/1.00      | v1_relat_1(X0) ),
% 1.68/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_368,plain,
% 1.68/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.68/1.00      | ~ v1_partfun1(X0,X1)
% 1.68/1.00      | k1_relat_1(X0) = X1 ),
% 1.68/1.00      inference(global_propositional_subsumption,
% 1.68/1.00                [status(thm)],
% 1.68/1.00                [c_364,c_20,c_16,c_14]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_369,plain,
% 1.68/1.00      ( ~ v1_partfun1(X0,X1)
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.68/1.00      | k1_relat_1(X0) = X1 ),
% 1.68/1.00      inference(renaming,[status(thm)],[c_368]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_446,plain,
% 1.68/1.00      ( ~ v1_partfun1(X0,X1)
% 1.68/1.00      | k1_relat_1(X0) = X1
% 1.68/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.68/1.00      | sK3 != X0 ),
% 1.68/1.00      inference(resolution_lifted,[status(thm)],[c_369,c_26]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_447,plain,
% 1.68/1.00      ( ~ v1_partfun1(sK3,X0)
% 1.68/1.00      | k1_relat_1(sK3) = X0
% 1.68/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.68/1.00      inference(unflattening,[status(thm)],[c_446]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_562,plain,
% 1.68/1.00      ( u1_struct_0(sK2) = k1_xboole_0
% 1.68/1.00      | u1_struct_0(sK1) != X0
% 1.68/1.00      | k1_relat_1(sK3) = X0
% 1.68/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.68/1.00      | sK3 != sK3 ),
% 1.68/1.00      inference(resolution_lifted,[status(thm)],[c_428,c_447]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_563,plain,
% 1.68/1.00      ( u1_struct_0(sK2) = k1_xboole_0
% 1.68/1.00      | k1_relat_1(sK3) = u1_struct_0(sK1)
% 1.68/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0)) ),
% 1.68/1.00      inference(unflattening,[status(thm)],[c_562]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_617,plain,
% 1.68/1.00      ( sP0_iProver_split
% 1.68/1.00      | u1_struct_0(sK2) = k1_xboole_0
% 1.68/1.00      | k1_relat_1(sK3) = u1_struct_0(sK1) ),
% 1.68/1.00      inference(splitting,
% 1.68/1.00                [splitting(split),new_symbols(definition,[])],
% 1.68/1.00                [c_563]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_768,plain,
% 1.68/1.00      ( u1_struct_0(sK2) = k1_xboole_0
% 1.68/1.00      | k1_relat_1(sK3) = u1_struct_0(sK1)
% 1.68/1.00      | sP0_iProver_split = iProver_top ),
% 1.68/1.00      inference(predicate_to_equality,[status(thm)],[c_617]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_23,plain,
% 1.68/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.68/1.00      inference(cnf_transformation,[],[f69]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_29,negated_conjecture,
% 1.68/1.00      ( l1_struct_0(sK2) ),
% 1.68/1.00      inference(cnf_transformation,[],[f71]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_312,plain,
% 1.68/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK2 != X0 ),
% 1.68/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_29]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_313,plain,
% 1.68/1.00      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 1.68/1.00      inference(unflattening,[status(thm)],[c_312]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_30,negated_conjecture,
% 1.68/1.00      ( l1_struct_0(sK1) ),
% 1.68/1.00      inference(cnf_transformation,[],[f70]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_317,plain,
% 1.68/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 1.68/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_318,plain,
% 1.68/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.68/1.00      inference(unflattening,[status(thm)],[c_317]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_798,plain,
% 1.68/1.00      ( k2_struct_0(sK2) = k1_xboole_0
% 1.68/1.00      | k2_struct_0(sK1) = k1_relat_1(sK3)
% 1.68/1.00      | sP0_iProver_split = iProver_top ),
% 1.68/1.00      inference(demodulation,[status(thm)],[c_768,c_313,c_318]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_863,plain,
% 1.68/1.00      ( sP0_iProver_split
% 1.68/1.00      | k2_struct_0(sK2) = k1_xboole_0
% 1.68/1.00      | k2_struct_0(sK1) = k1_relat_1(sK3) ),
% 1.68/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_798]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_621,plain,( X0 = X0 ),theory(equality) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_880,plain,
% 1.68/1.00      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
% 1.68/1.00      inference(instantiation,[status(thm)],[c_621]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_616,plain,
% 1.68/1.00      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X0))
% 1.68/1.00      | ~ sP0_iProver_split ),
% 1.68/1.00      inference(splitting,
% 1.68/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.68/1.00                [c_563]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_938,plain,
% 1.68/1.00      ( ~ sP0_iProver_split
% 1.68/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
% 1.68/1.00      inference(instantiation,[status(thm)],[c_616]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1003,plain,
% 1.68/1.00      ( k2_struct_0(sK1) = k1_relat_1(sK3)
% 1.68/1.00      | k2_struct_0(sK2) = k1_xboole_0 ),
% 1.68/1.00      inference(global_propositional_subsumption,
% 1.68/1.00                [status(thm)],
% 1.68/1.00                [c_798,c_863,c_880,c_938]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1004,plain,
% 1.68/1.00      ( k2_struct_0(sK2) = k1_xboole_0
% 1.68/1.00      | k2_struct_0(sK1) = k1_relat_1(sK3) ),
% 1.68/1.00      inference(renaming,[status(thm)],[c_1003]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_25,negated_conjecture,
% 1.68/1.00      ( k1_xboole_0 != k2_struct_0(sK2)
% 1.68/1.00      | k1_xboole_0 = k2_struct_0(sK1) ),
% 1.68/1.00      inference(cnf_transformation,[],[f75]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1011,plain,
% 1.68/1.00      ( k2_struct_0(sK1) = k1_relat_1(sK3)
% 1.68/1.00      | k2_struct_0(sK1) = k1_xboole_0 ),
% 1.68/1.00      inference(superposition,[status(thm)],[c_1004,c_25]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_15,plain,
% 1.68/1.00      ( v5_relat_1(X0,X1)
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 1.68/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_6,plain,
% 1.68/1.00      ( r1_tarski(k2_relat_1(X0),X1)
% 1.68/1.00      | ~ v5_relat_1(X0,X1)
% 1.68/1.00      | ~ v1_relat_1(X0) ),
% 1.68/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_324,plain,
% 1.68/1.00      ( r1_tarski(k2_relat_1(X0),X1)
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 1.68/1.00      | ~ v1_relat_1(X0) ),
% 1.68/1.00      inference(resolution,[status(thm)],[c_15,c_6]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_334,plain,
% 1.68/1.00      ( r1_tarski(k2_relat_1(X0),X1)
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 1.68/1.00      inference(forward_subsumption_resolution,
% 1.68/1.00                [status(thm)],
% 1.68/1.00                [c_324,c_14]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_10,plain,
% 1.68/1.00      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 1.68/1.00      | ~ v1_relat_1(X0)
% 1.68/1.00      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 1.68/1.00      inference(cnf_transformation,[],[f56]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_344,plain,
% 1.68/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.68/1.00      | ~ v1_relat_1(X0)
% 1.68/1.00      | k5_relat_1(X0,k6_relat_1(X2)) = X0 ),
% 1.68/1.00      inference(resolution,[status(thm)],[c_334,c_10]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_348,plain,
% 1.68/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.68/1.00      | k5_relat_1(X0,k6_relat_1(X2)) = X0 ),
% 1.68/1.00      inference(global_propositional_subsumption,
% 1.68/1.00                [status(thm)],
% 1.68/1.00                [c_344,c_14]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_461,plain,
% 1.68/1.00      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 1.68/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
% 1.68/1.00      | sK3 != X0 ),
% 1.68/1.00      inference(resolution_lifted,[status(thm)],[c_348,c_26]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_462,plain,
% 1.68/1.00      ( k5_relat_1(sK3,k6_relat_1(X0)) = sK3
% 1.68/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
% 1.68/1.00      inference(unflattening,[status(thm)],[c_461]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_831,plain,
% 1.68/1.00      ( k5_relat_1(sK3,k6_relat_1(X0)) = sK3
% 1.68/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X0)) ),
% 1.68/1.00      inference(light_normalisation,[status(thm)],[c_462,c_313,c_318]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1268,plain,
% 1.68/1.00      ( k5_relat_1(sK3,k6_relat_1(k2_struct_0(sK2))) = sK3 ),
% 1.68/1.00      inference(equality_resolution,[status(thm)],[c_831]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_13,plain,
% 1.68/1.00      ( v1_relat_1(k6_relat_1(X0)) ),
% 1.68/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_773,plain,
% 1.68/1.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 1.68/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_479,plain,
% 1.68/1.00      ( v1_relat_1(X0)
% 1.68/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.68/1.00      | sK3 != X0 ),
% 1.68/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_480,plain,
% 1.68/1.00      ( v1_relat_1(sK3)
% 1.68/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.68/1.00      inference(unflattening,[status(thm)],[c_479]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_772,plain,
% 1.68/1.00      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.68/1.00      | v1_relat_1(sK3) = iProver_top ),
% 1.68/1.00      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_821,plain,
% 1.68/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.68/1.00      | v1_relat_1(sK3) = iProver_top ),
% 1.68/1.00      inference(light_normalisation,[status(thm)],[c_772,c_313,c_318]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_882,plain,
% 1.68/1.00      ( v1_relat_1(sK3)
% 1.68/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
% 1.68/1.00      inference(instantiation,[status(thm)],[c_480]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_883,plain,
% 1.68/1.00      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
% 1.68/1.00      | v1_relat_1(sK3) = iProver_top ),
% 1.68/1.00      inference(predicate_to_equality,[status(thm)],[c_882]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_953,plain,
% 1.68/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 1.68/1.00      inference(global_propositional_subsumption,
% 1.68/1.00                [status(thm)],
% 1.68/1.00                [c_821,c_880,c_883]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_7,plain,
% 1.68/1.00      ( ~ v1_relat_1(X0)
% 1.68/1.00      | ~ v1_relat_1(X1)
% 1.68/1.00      | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
% 1.68/1.00      inference(cnf_transformation,[],[f53]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_774,plain,
% 1.68/1.00      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 1.68/1.00      | v1_relat_1(X1) != iProver_top
% 1.68/1.00      | v1_relat_1(X0) != iProver_top ),
% 1.68/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2526,plain,
% 1.68/1.00      ( k10_relat_1(sK3,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK3,X0))
% 1.68/1.00      | v1_relat_1(X0) != iProver_top ),
% 1.68/1.00      inference(superposition,[status(thm)],[c_953,c_774]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2786,plain,
% 1.68/1.00      ( k10_relat_1(sK3,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(X0))) ),
% 1.68/1.00      inference(superposition,[status(thm)],[c_773,c_2526]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_9,plain,
% 1.68/1.00      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 1.68/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2795,plain,
% 1.68/1.00      ( k1_relat_1(k5_relat_1(sK3,k6_relat_1(X0))) = k10_relat_1(sK3,X0) ),
% 1.68/1.00      inference(light_normalisation,[status(thm)],[c_2786,c_9]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_3024,plain,
% 1.68/1.00      ( k10_relat_1(sK3,k2_struct_0(sK2)) = k1_relat_1(sK3) ),
% 1.68/1.00      inference(superposition,[status(thm)],[c_1268,c_2795]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_17,plain,
% 1.68/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.68/1.00      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 1.68/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_470,plain,
% 1.68/1.00      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 1.68/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.68/1.00      | sK3 != X2 ),
% 1.68/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_471,plain,
% 1.68/1.00      ( k8_relset_1(X0,X1,sK3,X2) = k10_relat_1(sK3,X2)
% 1.68/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.68/1.00      inference(unflattening,[status(thm)],[c_470]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_842,plain,
% 1.68/1.00      ( k8_relset_1(X0,X1,sK3,X2) = k10_relat_1(sK3,X2)
% 1.68/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.68/1.00      inference(light_normalisation,[status(thm)],[c_471,c_313,c_318]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1327,plain,
% 1.68/1.00      ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,X0) = k10_relat_1(sK3,X0) ),
% 1.68/1.00      inference(equality_resolution,[status(thm)],[c_842]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_24,negated_conjecture,
% 1.68/1.00      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
% 1.68/1.00      inference(cnf_transformation,[],[f76]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_795,plain,
% 1.68/1.00      ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
% 1.68/1.00      inference(light_normalisation,[status(thm)],[c_24,c_313,c_318]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1777,plain,
% 1.68/1.00      ( k10_relat_1(sK3,k2_struct_0(sK2)) != k2_struct_0(sK1) ),
% 1.68/1.00      inference(demodulation,[status(thm)],[c_1327,c_795]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_3161,plain,
% 1.68/1.00      ( k2_struct_0(sK1) != k1_relat_1(sK3) ),
% 1.68/1.00      inference(demodulation,[status(thm)],[c_3024,c_1777]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_3165,plain,
% 1.68/1.00      ( k2_struct_0(sK1) = k1_xboole_0 ),
% 1.68/1.00      inference(superposition,[status(thm)],[c_1011,c_3161]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_3167,plain,
% 1.68/1.00      ( k1_relat_1(sK3) != k1_xboole_0 ),
% 1.68/1.00      inference(demodulation,[status(thm)],[c_3165,c_3161]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_21,plain,
% 1.68/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 1.68/1.00      | v1_partfun1(X0,k1_xboole_0)
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.68/1.00      | ~ v1_funct_1(X0) ),
% 1.68/1.00      inference(cnf_transformation,[],[f80]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_408,plain,
% 1.68/1.00      ( v1_partfun1(X0,k1_xboole_0)
% 1.68/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.68/1.00      | ~ v1_funct_1(X0)
% 1.68/1.00      | u1_struct_0(sK2) != X1
% 1.68/1.00      | u1_struct_0(sK1) != k1_xboole_0
% 1.68/1.00      | sK3 != X0 ),
% 1.68/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_409,plain,
% 1.68/1.00      ( v1_partfun1(sK3,k1_xboole_0)
% 1.68/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))))
% 1.68/1.00      | ~ v1_funct_1(sK3)
% 1.68/1.00      | u1_struct_0(sK1) != k1_xboole_0 ),
% 1.68/1.00      inference(unflattening,[status(thm)],[c_408]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_411,plain,
% 1.68/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))))
% 1.68/1.00      | v1_partfun1(sK3,k1_xboole_0)
% 1.68/1.00      | u1_struct_0(sK1) != k1_xboole_0 ),
% 1.68/1.00      inference(global_propositional_subsumption,
% 1.68/1.00                [status(thm)],
% 1.68/1.00                [c_409,c_28]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_412,plain,
% 1.68/1.00      ( v1_partfun1(sK3,k1_xboole_0)
% 1.68/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))))
% 1.68/1.00      | u1_struct_0(sK1) != k1_xboole_0 ),
% 1.68/1.00      inference(renaming,[status(thm)],[c_411]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_511,plain,
% 1.68/1.00      ( v1_partfun1(sK3,k1_xboole_0)
% 1.68/1.00      | u1_struct_0(sK1) != k1_xboole_0
% 1.68/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2)))
% 1.68/1.00      | sK3 != sK3 ),
% 1.68/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_412]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_547,plain,
% 1.68/1.00      ( u1_struct_0(sK1) != k1_xboole_0
% 1.68/1.00      | k1_relat_1(sK3) = X0
% 1.68/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.68/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2)))
% 1.68/1.00      | sK3 != sK3
% 1.68/1.00      | k1_xboole_0 != X0 ),
% 1.68/1.00      inference(resolution_lifted,[status(thm)],[c_511,c_447]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_548,plain,
% 1.68/1.00      ( u1_struct_0(sK1) != k1_xboole_0
% 1.68/1.00      | k1_relat_1(sK3) = k1_xboole_0
% 1.68/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
% 1.68/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))) ),
% 1.68/1.00      inference(unflattening,[status(thm)],[c_547]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_619,plain,
% 1.68/1.00      ( sP1_iProver_split
% 1.68/1.00      | u1_struct_0(sK1) != k1_xboole_0
% 1.68/1.00      | k1_relat_1(sK3) = k1_xboole_0
% 1.68/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2))) ),
% 1.68/1.00      inference(splitting,
% 1.68/1.00                [splitting(split),new_symbols(definition,[])],
% 1.68/1.00                [c_548]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_770,plain,
% 1.68/1.00      ( u1_struct_0(sK1) != k1_xboole_0
% 1.68/1.00      | k1_relat_1(sK3) = k1_xboole_0
% 1.68/1.00      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK2)))
% 1.68/1.00      | sP1_iProver_split = iProver_top ),
% 1.68/1.00      inference(predicate_to_equality,[status(thm)],[c_619]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_847,plain,
% 1.68/1.00      ( k2_struct_0(sK1) != k1_xboole_0
% 1.68/1.00      | k1_relat_1(sK3) = k1_xboole_0
% 1.68/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK2)))
% 1.68/1.00      | sP1_iProver_split = iProver_top ),
% 1.68/1.00      inference(light_normalisation,[status(thm)],[c_770,c_313,c_318]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_2,plain,
% 1.68/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.68/1.00      inference(cnf_transformation,[],[f78]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_848,plain,
% 1.68/1.00      ( k2_struct_0(sK1) != k1_xboole_0
% 1.68/1.00      | k1_relat_1(sK3) = k1_xboole_0
% 1.68/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k1_xboole_0)
% 1.68/1.00      | sP1_iProver_split = iProver_top ),
% 1.68/1.00      inference(demodulation,[status(thm)],[c_847,c_2]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_618,plain,
% 1.68/1.00      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
% 1.68/1.00      | ~ sP1_iProver_split ),
% 1.68/1.00      inference(splitting,
% 1.68/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.68/1.00                [c_548]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_771,plain,
% 1.68/1.00      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))
% 1.68/1.00      | sP1_iProver_split != iProver_top ),
% 1.68/1.00      inference(predicate_to_equality,[status(thm)],[c_618]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_816,plain,
% 1.68/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k1_xboole_0)
% 1.68/1.00      | sP1_iProver_split != iProver_top ),
% 1.68/1.00      inference(light_normalisation,
% 1.68/1.00                [status(thm)],
% 1.68/1.00                [c_771,c_2,c_313,c_318]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_853,plain,
% 1.68/1.00      ( k2_struct_0(sK1) != k1_xboole_0
% 1.68/1.00      | k1_relat_1(sK3) = k1_xboole_0
% 1.68/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))) != k1_zfmisc_1(k1_xboole_0) ),
% 1.68/1.00      inference(forward_subsumption_resolution,
% 1.68/1.00                [status(thm)],
% 1.68/1.00                [c_848,c_816]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1456,plain,
% 1.68/1.00      ( k2_struct_0(sK1) = k1_relat_1(sK3)
% 1.68/1.00      | k2_struct_0(sK1) != k1_xboole_0
% 1.68/1.00      | k1_relat_1(sK3) = k1_xboole_0
% 1.68/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0) ),
% 1.68/1.00      inference(superposition,[status(thm)],[c_1004,c_853]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1,plain,
% 1.68/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 1.68/1.00      inference(cnf_transformation,[],[f77]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1461,plain,
% 1.68/1.00      ( k2_struct_0(sK1) = k1_relat_1(sK3)
% 1.68/1.00      | k2_struct_0(sK1) != k1_xboole_0
% 1.68/1.00      | k1_relat_1(sK3) = k1_xboole_0
% 1.68/1.00      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
% 1.68/1.00      inference(demodulation,[status(thm)],[c_1456,c_1]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(c_1462,plain,
% 1.68/1.00      ( k2_struct_0(sK1) = k1_relat_1(sK3)
% 1.68/1.00      | k2_struct_0(sK1) != k1_xboole_0
% 1.68/1.00      | k1_relat_1(sK3) = k1_xboole_0 ),
% 1.68/1.00      inference(equality_resolution_simp,[status(thm)],[c_1461]) ).
% 1.68/1.00  
% 1.68/1.00  cnf(contradiction,plain,
% 1.68/1.00      ( $false ),
% 1.68/1.00      inference(minisat,[status(thm)],[c_3167,c_3161,c_1462,c_1011]) ).
% 1.68/1.00  
% 1.68/1.00  
% 1.68/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.68/1.00  
% 1.68/1.00  ------                               Statistics
% 1.68/1.00  
% 1.68/1.00  ------ General
% 1.68/1.00  
% 1.68/1.00  abstr_ref_over_cycles:                  0
% 1.68/1.00  abstr_ref_under_cycles:                 0
% 1.68/1.00  gc_basic_clause_elim:                   0
% 1.68/1.00  forced_gc_time:                         0
% 1.68/1.00  parsing_time:                           0.014
% 1.68/1.00  unif_index_cands_time:                  0.
% 1.68/1.00  unif_index_add_time:                    0.
% 1.68/1.00  orderings_time:                         0.
% 1.68/1.00  out_proof_time:                         0.012
% 1.68/1.00  total_time:                             0.149
% 1.68/1.00  num_of_symbols:                         59
% 1.68/1.00  num_of_terms:                           3343
% 1.68/1.00  
% 1.68/1.00  ------ Preprocessing
% 1.68/1.00  
% 1.68/1.00  num_of_splits:                          2
% 1.68/1.00  num_of_split_atoms:                     2
% 1.68/1.00  num_of_reused_defs:                     0
% 1.68/1.00  num_eq_ax_congr_red:                    9
% 1.68/1.00  num_of_sem_filtered_clauses:            1
% 1.68/1.00  num_of_subtypes:                        0
% 1.68/1.00  monotx_restored_types:                  0
% 1.68/1.00  sat_num_of_epr_types:                   0
% 1.68/1.00  sat_num_of_non_cyclic_types:            0
% 1.68/1.00  sat_guarded_non_collapsed_types:        0
% 1.68/1.00  num_pure_diseq_elim:                    0
% 1.68/1.00  simp_replaced_by:                       0
% 1.68/1.00  res_preprocessed:                       116
% 1.68/1.00  prep_upred:                             0
% 1.68/1.00  prep_unflattend:                        21
% 1.68/1.00  smt_new_axioms:                         0
% 1.68/1.00  pred_elim_cands:                        1
% 1.68/1.00  pred_elim:                              10
% 1.68/1.00  pred_elim_cl:                           13
% 1.68/1.00  pred_elim_cycles:                       12
% 1.68/1.00  merged_defs:                            0
% 1.68/1.00  merged_defs_ncl:                        0
% 1.68/1.00  bin_hyper_res:                          0
% 1.68/1.00  prep_cycles:                            4
% 1.68/1.00  pred_elim_time:                         0.007
% 1.68/1.00  splitting_time:                         0.
% 1.68/1.00  sem_filter_time:                        0.
% 1.68/1.00  monotx_time:                            0.001
% 1.68/1.00  subtype_inf_time:                       0.
% 1.68/1.00  
% 1.68/1.00  ------ Problem properties
% 1.68/1.00  
% 1.68/1.00  clauses:                                20
% 1.68/1.00  conjectures:                            2
% 1.68/1.00  epr:                                    0
% 1.68/1.00  horn:                                   17
% 1.68/1.00  ground:                                 8
% 1.68/1.00  unary:                                  9
% 1.68/1.00  binary:                                 7
% 1.68/1.00  lits:                                   36
% 1.68/1.00  lits_eq:                                28
% 1.68/1.00  fd_pure:                                0
% 1.68/1.00  fd_pseudo:                              0
% 1.68/1.00  fd_cond:                                1
% 1.68/1.00  fd_pseudo_cond:                         0
% 1.68/1.00  ac_symbols:                             0
% 1.68/1.00  
% 1.68/1.00  ------ Propositional Solver
% 1.68/1.00  
% 1.68/1.00  prop_solver_calls:                      27
% 1.68/1.00  prop_fast_solver_calls:                 647
% 1.68/1.00  smt_solver_calls:                       0
% 1.68/1.00  smt_fast_solver_calls:                  0
% 1.68/1.00  prop_num_of_clauses:                    1222
% 1.68/1.00  prop_preprocess_simplified:             3841
% 1.68/1.00  prop_fo_subsumed:                       9
% 1.68/1.00  prop_solver_time:                       0.
% 1.68/1.00  smt_solver_time:                        0.
% 1.68/1.00  smt_fast_solver_time:                   0.
% 1.68/1.00  prop_fast_solver_time:                  0.
% 1.68/1.00  prop_unsat_core_time:                   0.
% 1.68/1.00  
% 1.68/1.00  ------ QBF
% 1.68/1.00  
% 1.68/1.00  qbf_q_res:                              0
% 1.68/1.00  qbf_num_tautologies:                    0
% 1.68/1.00  qbf_prep_cycles:                        0
% 1.68/1.00  
% 1.68/1.00  ------ BMC1
% 1.68/1.00  
% 1.68/1.00  bmc1_current_bound:                     -1
% 1.68/1.00  bmc1_last_solved_bound:                 -1
% 1.68/1.00  bmc1_unsat_core_size:                   -1
% 1.68/1.00  bmc1_unsat_core_parents_size:           -1
% 1.68/1.00  bmc1_merge_next_fun:                    0
% 1.68/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.68/1.00  
% 1.68/1.00  ------ Instantiation
% 1.68/1.00  
% 1.68/1.00  inst_num_of_clauses:                    655
% 1.68/1.00  inst_num_in_passive:                    56
% 1.68/1.00  inst_num_in_active:                     280
% 1.68/1.00  inst_num_in_unprocessed:                319
% 1.68/1.00  inst_num_of_loops:                      290
% 1.68/1.00  inst_num_of_learning_restarts:          0
% 1.68/1.00  inst_num_moves_active_passive:          8
% 1.68/1.00  inst_lit_activity:                      0
% 1.68/1.00  inst_lit_activity_moves:                0
% 1.68/1.00  inst_num_tautologies:                   0
% 1.68/1.00  inst_num_prop_implied:                  0
% 1.68/1.00  inst_num_existing_simplified:           0
% 1.68/1.00  inst_num_eq_res_simplified:             0
% 1.68/1.00  inst_num_child_elim:                    0
% 1.68/1.00  inst_num_of_dismatching_blockings:      120
% 1.68/1.00  inst_num_of_non_proper_insts:           566
% 1.68/1.00  inst_num_of_duplicates:                 0
% 1.68/1.00  inst_inst_num_from_inst_to_res:         0
% 1.68/1.00  inst_dismatching_checking_time:         0.
% 1.68/1.00  
% 1.68/1.00  ------ Resolution
% 1.68/1.00  
% 1.68/1.00  res_num_of_clauses:                     0
% 1.68/1.00  res_num_in_passive:                     0
% 1.68/1.00  res_num_in_active:                      0
% 1.68/1.00  res_num_of_loops:                       120
% 1.68/1.00  res_forward_subset_subsumed:            66
% 1.68/1.00  res_backward_subset_subsumed:           4
% 1.68/1.00  res_forward_subsumed:                   0
% 1.68/1.00  res_backward_subsumed:                  0
% 1.68/1.00  res_forward_subsumption_resolution:     2
% 1.68/1.00  res_backward_subsumption_resolution:    0
% 1.68/1.00  res_clause_to_clause_subsumption:       85
% 1.68/1.00  res_orphan_elimination:                 0
% 1.68/1.00  res_tautology_del:                      38
% 1.68/1.00  res_num_eq_res_simplified:              0
% 1.68/1.00  res_num_sel_changes:                    0
% 1.68/1.00  res_moves_from_active_to_pass:          0
% 1.68/1.00  
% 1.68/1.00  ------ Superposition
% 1.68/1.00  
% 1.68/1.00  sup_time_total:                         0.
% 1.68/1.00  sup_time_generating:                    0.
% 1.68/1.00  sup_time_sim_full:                      0.
% 1.68/1.00  sup_time_sim_immed:                     0.
% 1.68/1.00  
% 1.68/1.00  sup_num_of_clauses:                     63
% 1.68/1.00  sup_num_in_active:                      54
% 1.68/1.00  sup_num_in_passive:                     9
% 1.68/1.00  sup_num_of_loops:                       57
% 1.68/1.00  sup_fw_superposition:                   67
% 1.68/1.00  sup_bw_superposition:                   21
% 1.68/1.00  sup_immediate_simplified:               35
% 1.68/1.00  sup_given_eliminated:                   1
% 1.68/1.00  comparisons_done:                       0
% 1.68/1.00  comparisons_avoided:                    24
% 1.68/1.00  
% 1.68/1.00  ------ Simplifications
% 1.68/1.00  
% 1.68/1.00  
% 1.68/1.00  sim_fw_subset_subsumed:                 22
% 1.68/1.00  sim_bw_subset_subsumed:                 3
% 1.68/1.00  sim_fw_subsumed:                        3
% 1.68/1.00  sim_bw_subsumed:                        0
% 1.68/1.00  sim_fw_subsumption_res:                 1
% 1.68/1.00  sim_bw_subsumption_res:                 0
% 1.68/1.00  sim_tautology_del:                      1
% 1.68/1.00  sim_eq_tautology_del:                   1
% 1.68/1.00  sim_eq_res_simp:                        6
% 1.68/1.00  sim_fw_demodulated:                     11
% 1.68/1.00  sim_bw_demodulated:                     3
% 1.68/1.00  sim_light_normalised:                   11
% 1.68/1.00  sim_joinable_taut:                      0
% 1.68/1.00  sim_joinable_simp:                      0
% 1.68/1.00  sim_ac_normalised:                      0
% 1.68/1.00  sim_smt_subsumption:                    0
% 1.68/1.00  
%------------------------------------------------------------------------------
