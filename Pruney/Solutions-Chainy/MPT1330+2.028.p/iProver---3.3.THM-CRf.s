%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:58 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :  168 (7538 expanded)
%              Number of clauses        :  113 (2153 expanded)
%              Number of leaves         :   20 (2250 expanded)
%              Depth                    :   28
%              Number of atoms          :  423 (44130 expanded)
%              Number of equality atoms :  314 (19245 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f24])).

fof(f30,plain,(
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

fof(f29,plain,(
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

fof(f28,plain,
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

fof(f31,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0)
    & ( k1_xboole_0 = k2_struct_0(sK0)
      | k1_xboole_0 != k2_struct_0(sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f30,f29,f28])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f49,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f26])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f34])).

fof(f55,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f33])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_295,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_296,plain,
    ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_17,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_23,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_204,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_205,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_204])).

cnf(c_24,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_209,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_210,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_209])).

cnf(c_441,plain,
    ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_296,c_205,c_210])).

cnf(c_541,plain,
    ( k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(equality_resolution,[status(thm)],[c_441])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_277,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_278,plain,
    ( k7_relset_1(X0,X1,sK2,X0) = k2_relset_1(X0,X1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_277])).

cnf(c_457,plain,
    ( k7_relset_1(X0,X1,sK2,X0) = k2_relset_1(X0,X1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_278,c_205,c_210])).

cnf(c_714,plain,
    ( k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK0)) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(equality_resolution,[status(thm)],[c_457])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_304,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_305,plain,
    ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_304])).

cnf(c_436,plain,
    ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_305,c_205,c_210])).

cnf(c_538,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_436])).

cnf(c_1155,plain,
    ( k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK0)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_714,c_538])).

cnf(c_1157,plain,
    ( k9_relat_1(sK2,k2_struct_0(sK0)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_541,c_1155])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_233,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = X1
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_21])).

cnf(c_234,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0))) = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_233])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_236,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0))) = u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_234,c_22,c_20])).

cnf(c_446,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK0))) = k2_struct_0(sK0)
    | u1_struct_0(sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_236,c_205,c_210])).

cnf(c_447,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK0))) = k2_struct_0(sK0)
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_446,c_205])).

cnf(c_903,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k9_relat_1(sK2,k2_struct_0(sK0))) = k2_struct_0(sK0)
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_541,c_447])).

cnf(c_1811,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_relat_1(sK2)) = k2_struct_0(sK0)
    | k2_struct_0(sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1157,c_903])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_268,plain,
    ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = k1_relset_1(X0,X1,X2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_269,plain,
    ( k8_relset_1(X0,X1,sK2,k7_relset_1(X0,X1,sK2,X0)) = k1_relset_1(X0,X1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_268])).

cnf(c_462,plain,
    ( k8_relset_1(X0,X1,sK2,k7_relset_1(X0,X1,sK2,X0)) = k1_relset_1(X0,X1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_269,c_205,c_210])).

cnf(c_725,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK0))) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(equality_resolution,[status(thm)],[c_462])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_313,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_314,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_431,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_314,c_205,c_210])).

cnf(c_513,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_431])).

cnf(c_1469,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_725,c_513,c_1155])).

cnf(c_1812,plain,
    ( k2_struct_0(sK1) = k1_xboole_0
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1811,c_1469])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_286,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_287,plain,
    ( k8_relset_1(X0,X1,sK2,X1) = k1_relset_1(X0,X1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_452,plain,
    ( k8_relset_1(X0,X1,sK2,X1) = k1_relset_1(X0,X1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_287,c_205,c_210])).

cnf(c_675,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(equality_resolution,[status(thm)],[c_452])).

cnf(c_1073,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_675,c_513])).

cnf(c_18,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_417,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_18,c_205,c_210])).

cnf(c_1075,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1073,c_417])).

cnf(c_1993,plain,
    ( k2_struct_0(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1812,c_1075])).

cnf(c_0,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_674,plain,
    ( k8_relset_1(X0,k1_xboole_0,sK2,k1_xboole_0) = k1_relset_1(X0,k1_xboole_0,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_0,c_452])).

cnf(c_2006,plain,
    ( k8_relset_1(X0,k1_xboole_0,sK2,k1_xboole_0) = k1_relset_1(X0,k1_xboole_0,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_1993,c_674])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2028,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1993,c_19])).

cnf(c_2029,plain,
    ( k2_struct_0(sK0) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2028])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_250,plain,
    ( k9_relat_1(k6_relat_1(X0),X1) = X1
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_251,plain,
    ( k9_relat_1(k6_relat_1(X0),sK2) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_250])).

cnf(c_426,plain,
    ( k9_relat_1(k6_relat_1(X0),sK2) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_251,c_205,c_210])).

cnf(c_510,plain,
    ( k9_relat_1(k6_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))),sK2) = sK2 ),
    inference(equality_resolution,[status(thm)],[c_426])).

cnf(c_2016,plain,
    ( k9_relat_1(k6_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)),sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_1993,c_510])).

cnf(c_2088,plain,
    ( k9_relat_1(k6_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2016,c_2029])).

cnf(c_1,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_6,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2090,plain,
    ( sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2088,c_1,c_3,c_6])).

cnf(c_656,plain,
    ( k1_relset_1(X0,k1_xboole_0,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_0,c_431])).

cnf(c_2010,plain,
    ( k1_relset_1(X0,k1_xboole_0,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_1993,c_656])).

cnf(c_2167,plain,
    ( k1_relset_1(X0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2010,c_2029,c_2090])).

cnf(c_5,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2170,plain,
    ( k1_relset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2167,c_5])).

cnf(c_2171,plain,
    ( k1_relset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2170,c_1])).

cnf(c_2172,plain,
    ( k1_relset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2171])).

cnf(c_2194,plain,
    ( k8_relset_1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2006,c_2029,c_2090,c_2172])).

cnf(c_2197,plain,
    ( k8_relset_1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2194,c_1])).

cnf(c_2198,plain,
    ( k8_relset_1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2197])).

cnf(c_2245,plain,
    ( k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2198])).

cnf(c_371,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_516,plain,
    ( X0 != X1
    | k2_struct_0(sK0) != X1
    | k2_struct_0(sK0) = X0 ),
    inference(instantiation,[status(thm)],[c_371])).

cnf(c_1436,plain,
    ( k8_relset_1(X0,X1,X2,X3) != X4
    | k2_struct_0(sK0) != X4
    | k2_struct_0(sK0) = k8_relset_1(X0,X1,X2,X3) ),
    inference(instantiation,[status(thm)],[c_516])).

cnf(c_1439,plain,
    ( k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k2_struct_0(sK0) = k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k2_struct_0(sK0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1436])).

cnf(c_381,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k8_relset_1(X0,X2,X4,X6) = k8_relset_1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_1320,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k8_relset_1(X0,X1,X2,X3)
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK0) != X0
    | k2_struct_0(sK1) != X3
    | sK2 != X2 ),
    inference(instantiation,[status(thm)],[c_381])).

cnf(c_1322,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | u1_struct_0(sK1) != k1_xboole_0
    | u1_struct_0(sK0) != k1_xboole_0
    | k2_struct_0(sK1) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1320])).

cnf(c_500,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != X0
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k2_struct_0(sK0)
    | k2_struct_0(sK0) != X0 ),
    inference(instantiation,[status(thm)],[c_371])).

cnf(c_1319,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k8_relset_1(X0,X1,X2,X3)
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k2_struct_0(sK0)
    | k2_struct_0(sK0) != k8_relset_1(X0,X1,X2,X3) ),
    inference(instantiation,[status(thm)],[c_500])).

cnf(c_1321,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k2_struct_0(sK0)
    | k2_struct_0(sK0) != k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1319])).

cnf(c_634,plain,
    ( X0 != X1
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_371])).

cnf(c_1150,plain,
    ( X0 != k2_struct_0(sK1)
    | u1_struct_0(sK1) = X0
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_634])).

cnf(c_1151,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | u1_struct_0(sK1) = k1_xboole_0
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1150])).

cnf(c_596,plain,
    ( X0 != k2_struct_0(sK0)
    | k2_struct_0(sK0) = X0
    | k2_struct_0(sK0) != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_516])).

cnf(c_598,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK0) = k1_xboole_0
    | k1_xboole_0 != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_596])).

cnf(c_370,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_574,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_382,plain,
    ( X0 != X1
    | k2_struct_0(X0) = k2_struct_0(X1) ),
    theory(equality)).

cnf(c_518,plain,
    ( k2_struct_0(sK0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_382])).

cnf(c_573,plain,
    ( k2_struct_0(sK0) = k2_struct_0(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_518])).

cnf(c_504,plain,
    ( u1_struct_0(sK0) != X0
    | u1_struct_0(sK0) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_371])).

cnf(c_563,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | u1_struct_0(sK0) = k1_xboole_0
    | k1_xboole_0 != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_504])).

cnf(c_502,plain,
    ( k2_struct_0(sK1) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_371])).

cnf(c_503,plain,
    ( k2_struct_0(sK1) != k1_xboole_0
    | k1_xboole_0 = k2_struct_0(sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_502])).

cnf(c_65,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_64,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2245,c_2090,c_1812,c_1439,c_1322,c_1321,c_1151,c_1075,c_598,c_574,c_573,c_563,c_503,c_210,c_205,c_65,c_64,c_18,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:47:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.40/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.02  
% 2.40/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.40/1.02  
% 2.40/1.02  ------  iProver source info
% 2.40/1.02  
% 2.40/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.40/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.40/1.02  git: non_committed_changes: false
% 2.40/1.02  git: last_make_outside_of_git: false
% 2.40/1.02  
% 2.40/1.02  ------ 
% 2.40/1.02  
% 2.40/1.02  ------ Input Options
% 2.40/1.02  
% 2.40/1.02  --out_options                           all
% 2.40/1.02  --tptp_safe_out                         true
% 2.40/1.02  --problem_path                          ""
% 2.40/1.02  --include_path                          ""
% 2.40/1.02  --clausifier                            res/vclausify_rel
% 2.40/1.02  --clausifier_options                    --mode clausify
% 2.40/1.02  --stdin                                 false
% 2.40/1.02  --stats_out                             all
% 2.40/1.02  
% 2.40/1.02  ------ General Options
% 2.40/1.02  
% 2.40/1.02  --fof                                   false
% 2.40/1.02  --time_out_real                         305.
% 2.40/1.02  --time_out_virtual                      -1.
% 2.40/1.02  --symbol_type_check                     false
% 2.40/1.02  --clausify_out                          false
% 2.40/1.02  --sig_cnt_out                           false
% 2.40/1.02  --trig_cnt_out                          false
% 2.40/1.02  --trig_cnt_out_tolerance                1.
% 2.40/1.02  --trig_cnt_out_sk_spl                   false
% 2.40/1.02  --abstr_cl_out                          false
% 2.40/1.02  
% 2.40/1.02  ------ Global Options
% 2.40/1.02  
% 2.40/1.02  --schedule                              default
% 2.40/1.02  --add_important_lit                     false
% 2.40/1.02  --prop_solver_per_cl                    1000
% 2.40/1.02  --min_unsat_core                        false
% 2.40/1.02  --soft_assumptions                      false
% 2.40/1.02  --soft_lemma_size                       3
% 2.40/1.02  --prop_impl_unit_size                   0
% 2.40/1.02  --prop_impl_unit                        []
% 2.40/1.02  --share_sel_clauses                     true
% 2.40/1.02  --reset_solvers                         false
% 2.40/1.02  --bc_imp_inh                            [conj_cone]
% 2.40/1.02  --conj_cone_tolerance                   3.
% 2.40/1.02  --extra_neg_conj                        none
% 2.40/1.02  --large_theory_mode                     true
% 2.40/1.02  --prolific_symb_bound                   200
% 2.40/1.02  --lt_threshold                          2000
% 2.40/1.02  --clause_weak_htbl                      true
% 2.40/1.02  --gc_record_bc_elim                     false
% 2.40/1.02  
% 2.40/1.02  ------ Preprocessing Options
% 2.40/1.02  
% 2.40/1.02  --preprocessing_flag                    true
% 2.40/1.02  --time_out_prep_mult                    0.1
% 2.40/1.02  --splitting_mode                        input
% 2.40/1.02  --splitting_grd                         true
% 2.40/1.02  --splitting_cvd                         false
% 2.40/1.02  --splitting_cvd_svl                     false
% 2.40/1.02  --splitting_nvd                         32
% 2.40/1.02  --sub_typing                            true
% 2.40/1.02  --prep_gs_sim                           true
% 2.40/1.02  --prep_unflatten                        true
% 2.40/1.02  --prep_res_sim                          true
% 2.40/1.02  --prep_upred                            true
% 2.40/1.02  --prep_sem_filter                       exhaustive
% 2.40/1.02  --prep_sem_filter_out                   false
% 2.40/1.02  --pred_elim                             true
% 2.40/1.02  --res_sim_input                         true
% 2.40/1.02  --eq_ax_congr_red                       true
% 2.40/1.02  --pure_diseq_elim                       true
% 2.40/1.02  --brand_transform                       false
% 2.40/1.02  --non_eq_to_eq                          false
% 2.40/1.02  --prep_def_merge                        true
% 2.40/1.02  --prep_def_merge_prop_impl              false
% 2.40/1.02  --prep_def_merge_mbd                    true
% 2.40/1.02  --prep_def_merge_tr_red                 false
% 2.40/1.02  --prep_def_merge_tr_cl                  false
% 2.40/1.02  --smt_preprocessing                     true
% 2.40/1.02  --smt_ac_axioms                         fast
% 2.40/1.02  --preprocessed_out                      false
% 2.40/1.02  --preprocessed_stats                    false
% 2.40/1.02  
% 2.40/1.02  ------ Abstraction refinement Options
% 2.40/1.02  
% 2.40/1.02  --abstr_ref                             []
% 2.40/1.02  --abstr_ref_prep                        false
% 2.40/1.02  --abstr_ref_until_sat                   false
% 2.40/1.02  --abstr_ref_sig_restrict                funpre
% 2.40/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/1.02  --abstr_ref_under                       []
% 2.40/1.02  
% 2.40/1.02  ------ SAT Options
% 2.40/1.02  
% 2.40/1.02  --sat_mode                              false
% 2.40/1.02  --sat_fm_restart_options                ""
% 2.40/1.02  --sat_gr_def                            false
% 2.40/1.02  --sat_epr_types                         true
% 2.40/1.02  --sat_non_cyclic_types                  false
% 2.40/1.02  --sat_finite_models                     false
% 2.40/1.02  --sat_fm_lemmas                         false
% 2.40/1.02  --sat_fm_prep                           false
% 2.40/1.02  --sat_fm_uc_incr                        true
% 2.40/1.02  --sat_out_model                         small
% 2.40/1.02  --sat_out_clauses                       false
% 2.40/1.02  
% 2.40/1.02  ------ QBF Options
% 2.40/1.02  
% 2.40/1.02  --qbf_mode                              false
% 2.40/1.02  --qbf_elim_univ                         false
% 2.40/1.02  --qbf_dom_inst                          none
% 2.40/1.02  --qbf_dom_pre_inst                      false
% 2.40/1.02  --qbf_sk_in                             false
% 2.40/1.02  --qbf_pred_elim                         true
% 2.40/1.02  --qbf_split                             512
% 2.40/1.02  
% 2.40/1.02  ------ BMC1 Options
% 2.40/1.02  
% 2.40/1.02  --bmc1_incremental                      false
% 2.40/1.02  --bmc1_axioms                           reachable_all
% 2.40/1.02  --bmc1_min_bound                        0
% 2.40/1.02  --bmc1_max_bound                        -1
% 2.40/1.02  --bmc1_max_bound_default                -1
% 2.40/1.02  --bmc1_symbol_reachability              true
% 2.40/1.02  --bmc1_property_lemmas                  false
% 2.40/1.02  --bmc1_k_induction                      false
% 2.40/1.02  --bmc1_non_equiv_states                 false
% 2.40/1.02  --bmc1_deadlock                         false
% 2.40/1.02  --bmc1_ucm                              false
% 2.40/1.02  --bmc1_add_unsat_core                   none
% 2.40/1.02  --bmc1_unsat_core_children              false
% 2.40/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/1.02  --bmc1_out_stat                         full
% 2.40/1.02  --bmc1_ground_init                      false
% 2.40/1.02  --bmc1_pre_inst_next_state              false
% 2.40/1.02  --bmc1_pre_inst_state                   false
% 2.40/1.02  --bmc1_pre_inst_reach_state             false
% 2.40/1.02  --bmc1_out_unsat_core                   false
% 2.40/1.02  --bmc1_aig_witness_out                  false
% 2.40/1.02  --bmc1_verbose                          false
% 2.40/1.02  --bmc1_dump_clauses_tptp                false
% 2.40/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.40/1.02  --bmc1_dump_file                        -
% 2.40/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.40/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.40/1.02  --bmc1_ucm_extend_mode                  1
% 2.40/1.02  --bmc1_ucm_init_mode                    2
% 2.40/1.02  --bmc1_ucm_cone_mode                    none
% 2.40/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.40/1.02  --bmc1_ucm_relax_model                  4
% 2.40/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.40/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/1.02  --bmc1_ucm_layered_model                none
% 2.40/1.02  --bmc1_ucm_max_lemma_size               10
% 2.40/1.02  
% 2.40/1.02  ------ AIG Options
% 2.40/1.02  
% 2.40/1.02  --aig_mode                              false
% 2.40/1.02  
% 2.40/1.02  ------ Instantiation Options
% 2.40/1.02  
% 2.40/1.02  --instantiation_flag                    true
% 2.40/1.02  --inst_sos_flag                         false
% 2.40/1.02  --inst_sos_phase                        true
% 2.40/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/1.02  --inst_lit_sel_side                     num_symb
% 2.40/1.02  --inst_solver_per_active                1400
% 2.40/1.02  --inst_solver_calls_frac                1.
% 2.40/1.02  --inst_passive_queue_type               priority_queues
% 2.40/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/1.02  --inst_passive_queues_freq              [25;2]
% 2.40/1.02  --inst_dismatching                      true
% 2.40/1.02  --inst_eager_unprocessed_to_passive     true
% 2.40/1.02  --inst_prop_sim_given                   true
% 2.40/1.02  --inst_prop_sim_new                     false
% 2.40/1.02  --inst_subs_new                         false
% 2.40/1.02  --inst_eq_res_simp                      false
% 2.40/1.02  --inst_subs_given                       false
% 2.40/1.02  --inst_orphan_elimination               true
% 2.40/1.02  --inst_learning_loop_flag               true
% 2.40/1.02  --inst_learning_start                   3000
% 2.40/1.02  --inst_learning_factor                  2
% 2.40/1.02  --inst_start_prop_sim_after_learn       3
% 2.40/1.02  --inst_sel_renew                        solver
% 2.40/1.02  --inst_lit_activity_flag                true
% 2.40/1.02  --inst_restr_to_given                   false
% 2.40/1.02  --inst_activity_threshold               500
% 2.40/1.02  --inst_out_proof                        true
% 2.40/1.02  
% 2.40/1.02  ------ Resolution Options
% 2.40/1.02  
% 2.40/1.02  --resolution_flag                       true
% 2.40/1.02  --res_lit_sel                           adaptive
% 2.40/1.02  --res_lit_sel_side                      none
% 2.40/1.02  --res_ordering                          kbo
% 2.40/1.02  --res_to_prop_solver                    active
% 2.40/1.02  --res_prop_simpl_new                    false
% 2.40/1.02  --res_prop_simpl_given                  true
% 2.40/1.02  --res_passive_queue_type                priority_queues
% 2.40/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/1.02  --res_passive_queues_freq               [15;5]
% 2.40/1.02  --res_forward_subs                      full
% 2.40/1.02  --res_backward_subs                     full
% 2.40/1.02  --res_forward_subs_resolution           true
% 2.40/1.02  --res_backward_subs_resolution          true
% 2.40/1.02  --res_orphan_elimination                true
% 2.40/1.02  --res_time_limit                        2.
% 2.40/1.02  --res_out_proof                         true
% 2.40/1.02  
% 2.40/1.02  ------ Superposition Options
% 2.40/1.02  
% 2.40/1.02  --superposition_flag                    true
% 2.40/1.02  --sup_passive_queue_type                priority_queues
% 2.40/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.40/1.02  --demod_completeness_check              fast
% 2.40/1.02  --demod_use_ground                      true
% 2.40/1.02  --sup_to_prop_solver                    passive
% 2.40/1.02  --sup_prop_simpl_new                    true
% 2.40/1.02  --sup_prop_simpl_given                  true
% 2.40/1.02  --sup_fun_splitting                     false
% 2.40/1.02  --sup_smt_interval                      50000
% 2.40/1.02  
% 2.40/1.02  ------ Superposition Simplification Setup
% 2.40/1.02  
% 2.40/1.02  --sup_indices_passive                   []
% 2.40/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.02  --sup_full_bw                           [BwDemod]
% 2.40/1.02  --sup_immed_triv                        [TrivRules]
% 2.40/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.02  --sup_immed_bw_main                     []
% 2.40/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/1.02  
% 2.40/1.02  ------ Combination Options
% 2.40/1.02  
% 2.40/1.02  --comb_res_mult                         3
% 2.40/1.02  --comb_sup_mult                         2
% 2.40/1.02  --comb_inst_mult                        10
% 2.40/1.02  
% 2.40/1.02  ------ Debug Options
% 2.40/1.02  
% 2.40/1.02  --dbg_backtrace                         false
% 2.40/1.02  --dbg_dump_prop_clauses                 false
% 2.40/1.02  --dbg_dump_prop_clauses_file            -
% 2.40/1.02  --dbg_out_stat                          false
% 2.40/1.02  ------ Parsing...
% 2.40/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.40/1.02  
% 2.40/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.40/1.02  
% 2.40/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.40/1.02  
% 2.40/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.40/1.02  ------ Proving...
% 2.40/1.02  ------ Problem Properties 
% 2.40/1.02  
% 2.40/1.02  
% 2.40/1.02  clauses                                 21
% 2.40/1.02  conjectures                             2
% 2.40/1.02  EPR                                     0
% 2.40/1.02  Horn                                    19
% 2.40/1.02  unary                                   9
% 2.40/1.02  binary                                  10
% 2.40/1.02  lits                                    35
% 2.40/1.02  lits eq                                 35
% 2.40/1.02  fd_pure                                 0
% 2.40/1.02  fd_pseudo                               0
% 2.40/1.02  fd_cond                                 1
% 2.40/1.02  fd_pseudo_cond                          0
% 2.40/1.02  AC symbols                              0
% 2.40/1.02  
% 2.40/1.02  ------ Schedule dynamic 5 is on 
% 2.40/1.02  
% 2.40/1.02  ------ pure equality problem: resolution off 
% 2.40/1.02  
% 2.40/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.40/1.02  
% 2.40/1.02  
% 2.40/1.02  ------ 
% 2.40/1.02  Current options:
% 2.40/1.02  ------ 
% 2.40/1.02  
% 2.40/1.02  ------ Input Options
% 2.40/1.02  
% 2.40/1.02  --out_options                           all
% 2.40/1.02  --tptp_safe_out                         true
% 2.40/1.02  --problem_path                          ""
% 2.40/1.02  --include_path                          ""
% 2.40/1.02  --clausifier                            res/vclausify_rel
% 2.40/1.02  --clausifier_options                    --mode clausify
% 2.40/1.02  --stdin                                 false
% 2.40/1.02  --stats_out                             all
% 2.40/1.02  
% 2.40/1.02  ------ General Options
% 2.40/1.02  
% 2.40/1.02  --fof                                   false
% 2.40/1.02  --time_out_real                         305.
% 2.40/1.02  --time_out_virtual                      -1.
% 2.40/1.02  --symbol_type_check                     false
% 2.40/1.02  --clausify_out                          false
% 2.40/1.02  --sig_cnt_out                           false
% 2.40/1.02  --trig_cnt_out                          false
% 2.40/1.02  --trig_cnt_out_tolerance                1.
% 2.40/1.02  --trig_cnt_out_sk_spl                   false
% 2.40/1.02  --abstr_cl_out                          false
% 2.40/1.02  
% 2.40/1.02  ------ Global Options
% 2.40/1.02  
% 2.40/1.02  --schedule                              default
% 2.40/1.02  --add_important_lit                     false
% 2.40/1.02  --prop_solver_per_cl                    1000
% 2.40/1.02  --min_unsat_core                        false
% 2.40/1.02  --soft_assumptions                      false
% 2.40/1.02  --soft_lemma_size                       3
% 2.40/1.02  --prop_impl_unit_size                   0
% 2.40/1.02  --prop_impl_unit                        []
% 2.40/1.02  --share_sel_clauses                     true
% 2.40/1.02  --reset_solvers                         false
% 2.40/1.02  --bc_imp_inh                            [conj_cone]
% 2.40/1.02  --conj_cone_tolerance                   3.
% 2.40/1.02  --extra_neg_conj                        none
% 2.40/1.02  --large_theory_mode                     true
% 2.40/1.02  --prolific_symb_bound                   200
% 2.40/1.02  --lt_threshold                          2000
% 2.40/1.02  --clause_weak_htbl                      true
% 2.40/1.02  --gc_record_bc_elim                     false
% 2.40/1.02  
% 2.40/1.02  ------ Preprocessing Options
% 2.40/1.02  
% 2.40/1.02  --preprocessing_flag                    true
% 2.40/1.02  --time_out_prep_mult                    0.1
% 2.40/1.02  --splitting_mode                        input
% 2.40/1.02  --splitting_grd                         true
% 2.40/1.02  --splitting_cvd                         false
% 2.40/1.02  --splitting_cvd_svl                     false
% 2.40/1.02  --splitting_nvd                         32
% 2.40/1.02  --sub_typing                            true
% 2.40/1.02  --prep_gs_sim                           true
% 2.40/1.02  --prep_unflatten                        true
% 2.40/1.02  --prep_res_sim                          true
% 2.40/1.02  --prep_upred                            true
% 2.40/1.02  --prep_sem_filter                       exhaustive
% 2.40/1.02  --prep_sem_filter_out                   false
% 2.40/1.02  --pred_elim                             true
% 2.40/1.02  --res_sim_input                         true
% 2.40/1.02  --eq_ax_congr_red                       true
% 2.40/1.02  --pure_diseq_elim                       true
% 2.40/1.02  --brand_transform                       false
% 2.40/1.02  --non_eq_to_eq                          false
% 2.40/1.02  --prep_def_merge                        true
% 2.40/1.02  --prep_def_merge_prop_impl              false
% 2.40/1.02  --prep_def_merge_mbd                    true
% 2.40/1.02  --prep_def_merge_tr_red                 false
% 2.40/1.02  --prep_def_merge_tr_cl                  false
% 2.40/1.02  --smt_preprocessing                     true
% 2.40/1.02  --smt_ac_axioms                         fast
% 2.40/1.02  --preprocessed_out                      false
% 2.40/1.02  --preprocessed_stats                    false
% 2.40/1.02  
% 2.40/1.02  ------ Abstraction refinement Options
% 2.40/1.02  
% 2.40/1.02  --abstr_ref                             []
% 2.40/1.02  --abstr_ref_prep                        false
% 2.40/1.02  --abstr_ref_until_sat                   false
% 2.40/1.02  --abstr_ref_sig_restrict                funpre
% 2.40/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/1.02  --abstr_ref_under                       []
% 2.40/1.02  
% 2.40/1.02  ------ SAT Options
% 2.40/1.02  
% 2.40/1.02  --sat_mode                              false
% 2.40/1.02  --sat_fm_restart_options                ""
% 2.40/1.02  --sat_gr_def                            false
% 2.40/1.02  --sat_epr_types                         true
% 2.40/1.02  --sat_non_cyclic_types                  false
% 2.40/1.02  --sat_finite_models                     false
% 2.40/1.02  --sat_fm_lemmas                         false
% 2.40/1.02  --sat_fm_prep                           false
% 2.40/1.02  --sat_fm_uc_incr                        true
% 2.40/1.02  --sat_out_model                         small
% 2.40/1.02  --sat_out_clauses                       false
% 2.40/1.02  
% 2.40/1.02  ------ QBF Options
% 2.40/1.02  
% 2.40/1.02  --qbf_mode                              false
% 2.40/1.02  --qbf_elim_univ                         false
% 2.40/1.02  --qbf_dom_inst                          none
% 2.40/1.02  --qbf_dom_pre_inst                      false
% 2.40/1.02  --qbf_sk_in                             false
% 2.40/1.02  --qbf_pred_elim                         true
% 2.40/1.02  --qbf_split                             512
% 2.40/1.02  
% 2.40/1.02  ------ BMC1 Options
% 2.40/1.02  
% 2.40/1.02  --bmc1_incremental                      false
% 2.40/1.02  --bmc1_axioms                           reachable_all
% 2.40/1.02  --bmc1_min_bound                        0
% 2.40/1.02  --bmc1_max_bound                        -1
% 2.40/1.02  --bmc1_max_bound_default                -1
% 2.40/1.02  --bmc1_symbol_reachability              true
% 2.40/1.02  --bmc1_property_lemmas                  false
% 2.40/1.02  --bmc1_k_induction                      false
% 2.40/1.02  --bmc1_non_equiv_states                 false
% 2.40/1.02  --bmc1_deadlock                         false
% 2.40/1.02  --bmc1_ucm                              false
% 2.40/1.02  --bmc1_add_unsat_core                   none
% 2.40/1.02  --bmc1_unsat_core_children              false
% 2.40/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/1.02  --bmc1_out_stat                         full
% 2.40/1.02  --bmc1_ground_init                      false
% 2.40/1.02  --bmc1_pre_inst_next_state              false
% 2.40/1.02  --bmc1_pre_inst_state                   false
% 2.40/1.02  --bmc1_pre_inst_reach_state             false
% 2.40/1.02  --bmc1_out_unsat_core                   false
% 2.40/1.02  --bmc1_aig_witness_out                  false
% 2.40/1.02  --bmc1_verbose                          false
% 2.40/1.02  --bmc1_dump_clauses_tptp                false
% 2.40/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.40/1.02  --bmc1_dump_file                        -
% 2.40/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.40/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.40/1.02  --bmc1_ucm_extend_mode                  1
% 2.40/1.02  --bmc1_ucm_init_mode                    2
% 2.40/1.02  --bmc1_ucm_cone_mode                    none
% 2.40/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.40/1.02  --bmc1_ucm_relax_model                  4
% 2.40/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.40/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/1.02  --bmc1_ucm_layered_model                none
% 2.40/1.02  --bmc1_ucm_max_lemma_size               10
% 2.40/1.02  
% 2.40/1.02  ------ AIG Options
% 2.40/1.02  
% 2.40/1.02  --aig_mode                              false
% 2.40/1.02  
% 2.40/1.02  ------ Instantiation Options
% 2.40/1.02  
% 2.40/1.02  --instantiation_flag                    true
% 2.40/1.02  --inst_sos_flag                         false
% 2.40/1.02  --inst_sos_phase                        true
% 2.40/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/1.02  --inst_lit_sel_side                     none
% 2.40/1.02  --inst_solver_per_active                1400
% 2.40/1.02  --inst_solver_calls_frac                1.
% 2.40/1.02  --inst_passive_queue_type               priority_queues
% 2.40/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/1.02  --inst_passive_queues_freq              [25;2]
% 2.40/1.02  --inst_dismatching                      true
% 2.40/1.02  --inst_eager_unprocessed_to_passive     true
% 2.40/1.02  --inst_prop_sim_given                   true
% 2.40/1.02  --inst_prop_sim_new                     false
% 2.40/1.02  --inst_subs_new                         false
% 2.40/1.02  --inst_eq_res_simp                      false
% 2.40/1.02  --inst_subs_given                       false
% 2.40/1.02  --inst_orphan_elimination               true
% 2.40/1.02  --inst_learning_loop_flag               true
% 2.40/1.02  --inst_learning_start                   3000
% 2.40/1.02  --inst_learning_factor                  2
% 2.40/1.02  --inst_start_prop_sim_after_learn       3
% 2.40/1.02  --inst_sel_renew                        solver
% 2.40/1.02  --inst_lit_activity_flag                true
% 2.40/1.02  --inst_restr_to_given                   false
% 2.40/1.02  --inst_activity_threshold               500
% 2.40/1.02  --inst_out_proof                        true
% 2.40/1.02  
% 2.40/1.02  ------ Resolution Options
% 2.40/1.02  
% 2.40/1.02  --resolution_flag                       false
% 2.40/1.02  --res_lit_sel                           adaptive
% 2.40/1.02  --res_lit_sel_side                      none
% 2.40/1.02  --res_ordering                          kbo
% 2.40/1.02  --res_to_prop_solver                    active
% 2.40/1.02  --res_prop_simpl_new                    false
% 2.40/1.02  --res_prop_simpl_given                  true
% 2.40/1.02  --res_passive_queue_type                priority_queues
% 2.40/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/1.02  --res_passive_queues_freq               [15;5]
% 2.40/1.02  --res_forward_subs                      full
% 2.40/1.02  --res_backward_subs                     full
% 2.40/1.02  --res_forward_subs_resolution           true
% 2.40/1.02  --res_backward_subs_resolution          true
% 2.40/1.02  --res_orphan_elimination                true
% 2.40/1.02  --res_time_limit                        2.
% 2.40/1.02  --res_out_proof                         true
% 2.40/1.02  
% 2.40/1.02  ------ Superposition Options
% 2.40/1.02  
% 2.40/1.02  --superposition_flag                    true
% 2.40/1.02  --sup_passive_queue_type                priority_queues
% 2.40/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.40/1.02  --demod_completeness_check              fast
% 2.40/1.02  --demod_use_ground                      true
% 2.40/1.02  --sup_to_prop_solver                    passive
% 2.40/1.02  --sup_prop_simpl_new                    true
% 2.40/1.02  --sup_prop_simpl_given                  true
% 2.40/1.02  --sup_fun_splitting                     false
% 2.40/1.02  --sup_smt_interval                      50000
% 2.40/1.02  
% 2.40/1.02  ------ Superposition Simplification Setup
% 2.40/1.02  
% 2.40/1.02  --sup_indices_passive                   []
% 2.40/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.02  --sup_full_bw                           [BwDemod]
% 2.40/1.02  --sup_immed_triv                        [TrivRules]
% 2.40/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.02  --sup_immed_bw_main                     []
% 2.40/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/1.02  
% 2.40/1.02  ------ Combination Options
% 2.40/1.02  
% 2.40/1.02  --comb_res_mult                         3
% 2.40/1.02  --comb_sup_mult                         2
% 2.40/1.02  --comb_inst_mult                        10
% 2.40/1.02  
% 2.40/1.02  ------ Debug Options
% 2.40/1.02  
% 2.40/1.02  --dbg_backtrace                         false
% 2.40/1.02  --dbg_dump_prop_clauses                 false
% 2.40/1.02  --dbg_dump_prop_clauses_file            -
% 2.40/1.02  --dbg_out_stat                          false
% 2.40/1.02  
% 2.40/1.02  
% 2.40/1.02  
% 2.40/1.02  
% 2.40/1.02  ------ Proving...
% 2.40/1.02  
% 2.40/1.02  
% 2.40/1.02  % SZS status Theorem for theBenchmark.p
% 2.40/1.02  
% 2.40/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.40/1.02  
% 2.40/1.02  fof(f8,axiom,(
% 2.40/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.40/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.02  
% 2.40/1.02  fof(f18,plain,(
% 2.40/1.02    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.40/1.02    inference(ennf_transformation,[],[f8])).
% 2.40/1.02  
% 2.40/1.02  fof(f42,plain,(
% 2.40/1.02    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.40/1.02    inference(cnf_transformation,[],[f18])).
% 2.40/1.02  
% 2.40/1.02  fof(f13,conjecture,(
% 2.40/1.02    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 2.40/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.02  
% 2.40/1.02  fof(f14,negated_conjecture,(
% 2.40/1.02    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) = k2_struct_0(X0)))))),
% 2.40/1.02    inference(negated_conjecture,[],[f13])).
% 2.40/1.02  
% 2.40/1.02  fof(f24,plain,(
% 2.40/1.02    ? [X0] : (? [X1] : (? [X2] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 2.40/1.02    inference(ennf_transformation,[],[f14])).
% 2.40/1.02  
% 2.40/1.02  fof(f25,plain,(
% 2.40/1.02    ? [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 2.40/1.02    inference(flattening,[],[f24])).
% 2.40/1.02  
% 2.40/1.02  fof(f30,plain,(
% 2.40/1.02    ( ! [X0,X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.40/1.02    introduced(choice_axiom,[])).
% 2.40/1.02  
% 2.40/1.02  fof(f29,plain,(
% 2.40/1.02    ( ! [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))) )),
% 2.40/1.02    introduced(choice_axiom,[])).
% 2.40/1.02  
% 2.40/1.02  fof(f28,plain,(
% 2.40/1.02    ? [X0] : (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(X0) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) != k2_struct_0(sK0) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 2.40/1.02    introduced(choice_axiom,[])).
% 2.40/1.02  
% 2.40/1.02  fof(f31,plain,(
% 2.40/1.02    ((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.40/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f30,f29,f28])).
% 2.40/1.02  
% 2.40/1.02  fof(f54,plain,(
% 2.40/1.02    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.40/1.02    inference(cnf_transformation,[],[f31])).
% 2.40/1.02  
% 2.40/1.02  fof(f12,axiom,(
% 2.40/1.02    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.40/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.02  
% 2.40/1.02  fof(f23,plain,(
% 2.40/1.02    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.40/1.02    inference(ennf_transformation,[],[f12])).
% 2.40/1.02  
% 2.40/1.02  fof(f49,plain,(
% 2.40/1.02    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.40/1.02    inference(cnf_transformation,[],[f23])).
% 2.40/1.02  
% 2.40/1.02  fof(f51,plain,(
% 2.40/1.02    l1_struct_0(sK1)),
% 2.40/1.02    inference(cnf_transformation,[],[f31])).
% 2.40/1.02  
% 2.40/1.02  fof(f50,plain,(
% 2.40/1.02    l1_struct_0(sK0)),
% 2.40/1.02    inference(cnf_transformation,[],[f31])).
% 2.40/1.02  
% 2.40/1.02  fof(f9,axiom,(
% 2.40/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 2.40/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.02  
% 2.40/1.02  fof(f19,plain,(
% 2.40/1.02    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.40/1.02    inference(ennf_transformation,[],[f9])).
% 2.40/1.02  
% 2.40/1.02  fof(f43,plain,(
% 2.40/1.02    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.40/1.02    inference(cnf_transformation,[],[f19])).
% 2.40/1.02  
% 2.40/1.02  fof(f7,axiom,(
% 2.40/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.40/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.02  
% 2.40/1.02  fof(f17,plain,(
% 2.40/1.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.40/1.02    inference(ennf_transformation,[],[f7])).
% 2.40/1.02  
% 2.40/1.02  fof(f41,plain,(
% 2.40/1.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.40/1.02    inference(cnf_transformation,[],[f17])).
% 2.40/1.02  
% 2.40/1.02  fof(f11,axiom,(
% 2.40/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0))),
% 2.40/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.02  
% 2.40/1.02  fof(f21,plain,(
% 2.40/1.02    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.40/1.02    inference(ennf_transformation,[],[f11])).
% 2.40/1.02  
% 2.40/1.02  fof(f22,plain,(
% 2.40/1.02    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.40/1.02    inference(flattening,[],[f21])).
% 2.40/1.02  
% 2.40/1.02  fof(f47,plain,(
% 2.40/1.02    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.40/1.02    inference(cnf_transformation,[],[f22])).
% 2.40/1.02  
% 2.40/1.02  fof(f53,plain,(
% 2.40/1.02    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.40/1.02    inference(cnf_transformation,[],[f31])).
% 2.40/1.02  
% 2.40/1.02  fof(f52,plain,(
% 2.40/1.02    v1_funct_1(sK2)),
% 2.40/1.02    inference(cnf_transformation,[],[f31])).
% 2.40/1.02  
% 2.40/1.02  fof(f10,axiom,(
% 2.40/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 2.40/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.02  
% 2.40/1.02  fof(f20,plain,(
% 2.40/1.02    ! [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.40/1.02    inference(ennf_transformation,[],[f10])).
% 2.40/1.02  
% 2.40/1.02  fof(f46,plain,(
% 2.40/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 2.40/1.02    inference(cnf_transformation,[],[f20])).
% 2.40/1.02  
% 2.40/1.02  fof(f6,axiom,(
% 2.40/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.40/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.02  
% 2.40/1.02  fof(f16,plain,(
% 2.40/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.40/1.02    inference(ennf_transformation,[],[f6])).
% 2.40/1.02  
% 2.40/1.02  fof(f40,plain,(
% 2.40/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.40/1.02    inference(cnf_transformation,[],[f16])).
% 2.40/1.02  
% 2.40/1.02  fof(f44,plain,(
% 2.40/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.40/1.02    inference(cnf_transformation,[],[f19])).
% 2.40/1.02  
% 2.40/1.02  fof(f56,plain,(
% 2.40/1.02    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0)),
% 2.40/1.02    inference(cnf_transformation,[],[f31])).
% 2.40/1.02  
% 2.40/1.02  fof(f1,axiom,(
% 2.40/1.02    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.40/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.02  
% 2.40/1.02  fof(f26,plain,(
% 2.40/1.02    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.40/1.02    inference(nnf_transformation,[],[f1])).
% 2.40/1.02  
% 2.40/1.02  fof(f27,plain,(
% 2.40/1.02    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 2.40/1.02    inference(flattening,[],[f26])).
% 2.40/1.02  
% 2.40/1.02  fof(f34,plain,(
% 2.40/1.02    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 2.40/1.02    inference(cnf_transformation,[],[f27])).
% 2.40/1.02  
% 2.40/1.02  fof(f57,plain,(
% 2.40/1.02    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.40/1.02    inference(equality_resolution,[],[f34])).
% 2.40/1.02  
% 2.40/1.02  fof(f55,plain,(
% 2.40/1.02    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)),
% 2.40/1.02    inference(cnf_transformation,[],[f31])).
% 2.40/1.02  
% 2.40/1.02  fof(f5,axiom,(
% 2.40/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 2.40/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.02  
% 2.40/1.02  fof(f15,plain,(
% 2.40/1.02    ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.40/1.02    inference(ennf_transformation,[],[f5])).
% 2.40/1.02  
% 2.40/1.02  fof(f39,plain,(
% 2.40/1.02    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.40/1.02    inference(cnf_transformation,[],[f15])).
% 2.40/1.02  
% 2.40/1.02  fof(f33,plain,(
% 2.40/1.02    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 2.40/1.02    inference(cnf_transformation,[],[f27])).
% 2.40/1.02  
% 2.40/1.02  fof(f58,plain,(
% 2.40/1.02    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 2.40/1.02    inference(equality_resolution,[],[f33])).
% 2.40/1.02  
% 2.40/1.02  fof(f2,axiom,(
% 2.40/1.02    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 2.40/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.02  
% 2.40/1.02  fof(f35,plain,(
% 2.40/1.02    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 2.40/1.02    inference(cnf_transformation,[],[f2])).
% 2.40/1.02  
% 2.40/1.02  fof(f4,axiom,(
% 2.40/1.02    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.40/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.02  
% 2.40/1.02  fof(f38,plain,(
% 2.40/1.02    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.40/1.02    inference(cnf_transformation,[],[f4])).
% 2.40/1.02  
% 2.40/1.02  fof(f3,axiom,(
% 2.40/1.02    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.40/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.02  
% 2.40/1.02  fof(f36,plain,(
% 2.40/1.02    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.40/1.02    inference(cnf_transformation,[],[f3])).
% 2.40/1.02  
% 2.40/1.02  fof(f32,plain,(
% 2.40/1.02    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 2.40/1.02    inference(cnf_transformation,[],[f27])).
% 2.40/1.02  
% 2.40/1.02  cnf(c_10,plain,
% 2.40/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/1.02      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.40/1.02      inference(cnf_transformation,[],[f42]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_20,negated_conjecture,
% 2.40/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.40/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_295,plain,
% 2.40/1.02      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.40/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.40/1.02      | sK2 != X2 ),
% 2.40/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_296,plain,
% 2.40/1.02      ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
% 2.40/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.40/1.02      inference(unflattening,[status(thm)],[c_295]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_17,plain,
% 2.40/1.02      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.40/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_23,negated_conjecture,
% 2.40/1.02      ( l1_struct_0(sK1) ),
% 2.40/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_204,plain,
% 2.40/1.02      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.40/1.02      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_205,plain,
% 2.40/1.02      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.40/1.02      inference(unflattening,[status(thm)],[c_204]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_24,negated_conjecture,
% 2.40/1.02      ( l1_struct_0(sK0) ),
% 2.40/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_209,plain,
% 2.40/1.02      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.40/1.02      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_210,plain,
% 2.40/1.02      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.40/1.02      inference(unflattening,[status(thm)],[c_209]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_441,plain,
% 2.40/1.02      ( k7_relset_1(X0,X1,sK2,X2) = k9_relat_1(sK2,X2)
% 2.40/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.40/1.02      inference(light_normalisation,[status(thm)],[c_296,c_205,c_210]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_541,plain,
% 2.40/1.02      ( k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k9_relat_1(sK2,X0) ),
% 2.40/1.02      inference(equality_resolution,[status(thm)],[c_441]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_12,plain,
% 2.40/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/1.02      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 2.40/1.02      inference(cnf_transformation,[],[f43]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_277,plain,
% 2.40/1.02      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 2.40/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.40/1.02      | sK2 != X2 ),
% 2.40/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_278,plain,
% 2.40/1.02      ( k7_relset_1(X0,X1,sK2,X0) = k2_relset_1(X0,X1,sK2)
% 2.40/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.40/1.02      inference(unflattening,[status(thm)],[c_277]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_457,plain,
% 2.40/1.02      ( k7_relset_1(X0,X1,sK2,X0) = k2_relset_1(X0,X1,sK2)
% 2.40/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.40/1.02      inference(light_normalisation,[status(thm)],[c_278,c_205,c_210]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_714,plain,
% 2.40/1.02      ( k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK0)) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
% 2.40/1.02      inference(equality_resolution,[status(thm)],[c_457]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_9,plain,
% 2.40/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.40/1.02      inference(cnf_transformation,[],[f41]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_304,plain,
% 2.40/1.02      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.40/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.40/1.02      | sK2 != X2 ),
% 2.40/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_305,plain,
% 2.40/1.02      ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
% 2.40/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.40/1.02      inference(unflattening,[status(thm)],[c_304]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_436,plain,
% 2.40/1.02      ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
% 2.40/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.40/1.02      inference(light_normalisation,[status(thm)],[c_305,c_205,c_210]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_538,plain,
% 2.40/1.02      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.40/1.02      inference(equality_resolution,[status(thm)],[c_436]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_1155,plain,
% 2.40/1.02      ( k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK0)) = k2_relat_1(sK2) ),
% 2.40/1.02      inference(light_normalisation,[status(thm)],[c_714,c_538]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_1157,plain,
% 2.40/1.02      ( k9_relat_1(sK2,k2_struct_0(sK0)) = k2_relat_1(sK2) ),
% 2.40/1.02      inference(superposition,[status(thm)],[c_541,c_1155]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_16,plain,
% 2.40/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.40/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/1.02      | ~ v1_funct_1(X0)
% 2.40/1.02      | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = X1
% 2.40/1.02      | k1_xboole_0 = X2 ),
% 2.40/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_21,negated_conjecture,
% 2.40/1.02      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.40/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_233,plain,
% 2.40/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/1.02      | ~ v1_funct_1(X0)
% 2.40/1.02      | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = X1
% 2.40/1.02      | u1_struct_0(sK1) != X2
% 2.40/1.02      | u1_struct_0(sK0) != X1
% 2.40/1.02      | sK2 != X0
% 2.40/1.02      | k1_xboole_0 = X2 ),
% 2.40/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_21]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_234,plain,
% 2.40/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.40/1.02      | ~ v1_funct_1(sK2)
% 2.40/1.02      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0))) = u1_struct_0(sK0)
% 2.40/1.02      | k1_xboole_0 = u1_struct_0(sK1) ),
% 2.40/1.02      inference(unflattening,[status(thm)],[c_233]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_22,negated_conjecture,
% 2.40/1.02      ( v1_funct_1(sK2) ),
% 2.40/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_236,plain,
% 2.40/1.02      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK0))) = u1_struct_0(sK0)
% 2.40/1.02      | k1_xboole_0 = u1_struct_0(sK1) ),
% 2.40/1.02      inference(global_propositional_subsumption,
% 2.40/1.02                [status(thm)],
% 2.40/1.02                [c_234,c_22,c_20]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_446,plain,
% 2.40/1.02      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK0))) = k2_struct_0(sK0)
% 2.40/1.02      | u1_struct_0(sK1) = k1_xboole_0 ),
% 2.40/1.02      inference(light_normalisation,[status(thm)],[c_236,c_205,c_210]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_447,plain,
% 2.40/1.02      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK0))) = k2_struct_0(sK0)
% 2.40/1.02      | k2_struct_0(sK1) = k1_xboole_0 ),
% 2.40/1.02      inference(demodulation,[status(thm)],[c_446,c_205]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_903,plain,
% 2.40/1.02      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k9_relat_1(sK2,k2_struct_0(sK0))) = k2_struct_0(sK0)
% 2.40/1.02      | k2_struct_0(sK1) = k1_xboole_0 ),
% 2.40/1.02      inference(demodulation,[status(thm)],[c_541,c_447]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_1811,plain,
% 2.40/1.02      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_relat_1(sK2)) = k2_struct_0(sK0)
% 2.40/1.02      | k2_struct_0(sK1) = k1_xboole_0 ),
% 2.40/1.02      inference(demodulation,[status(thm)],[c_1157,c_903]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_13,plain,
% 2.40/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/1.02      | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = k1_relset_1(X1,X2,X0) ),
% 2.40/1.02      inference(cnf_transformation,[],[f46]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_268,plain,
% 2.40/1.02      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = k1_relset_1(X0,X1,X2)
% 2.40/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.40/1.02      | sK2 != X2 ),
% 2.40/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_269,plain,
% 2.40/1.02      ( k8_relset_1(X0,X1,sK2,k7_relset_1(X0,X1,sK2,X0)) = k1_relset_1(X0,X1,sK2)
% 2.40/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.40/1.02      inference(unflattening,[status(thm)],[c_268]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_462,plain,
% 2.40/1.02      ( k8_relset_1(X0,X1,sK2,k7_relset_1(X0,X1,sK2,X0)) = k1_relset_1(X0,X1,sK2)
% 2.40/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.40/1.02      inference(light_normalisation,[status(thm)],[c_269,c_205,c_210]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_725,plain,
% 2.40/1.02      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK0))) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
% 2.40/1.02      inference(equality_resolution,[status(thm)],[c_462]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_8,plain,
% 2.40/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.40/1.02      inference(cnf_transformation,[],[f40]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_313,plain,
% 2.40/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.40/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.40/1.02      | sK2 != X2 ),
% 2.40/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_314,plain,
% 2.40/1.02      ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
% 2.40/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.40/1.02      inference(unflattening,[status(thm)],[c_313]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_431,plain,
% 2.40/1.02      ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
% 2.40/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.40/1.02      inference(light_normalisation,[status(thm)],[c_314,c_205,c_210]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_513,plain,
% 2.40/1.02      ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
% 2.40/1.02      inference(equality_resolution,[status(thm)],[c_431]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_1469,plain,
% 2.40/1.02      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.40/1.02      inference(light_normalisation,[status(thm)],[c_725,c_513,c_1155]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_1812,plain,
% 2.40/1.02      ( k2_struct_0(sK1) = k1_xboole_0
% 2.40/1.02      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.40/1.02      inference(light_normalisation,[status(thm)],[c_1811,c_1469]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_11,plain,
% 2.40/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.40/1.02      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 2.40/1.02      inference(cnf_transformation,[],[f44]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_286,plain,
% 2.40/1.02      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 2.40/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.40/1.02      | sK2 != X2 ),
% 2.40/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_287,plain,
% 2.40/1.02      ( k8_relset_1(X0,X1,sK2,X1) = k1_relset_1(X0,X1,sK2)
% 2.40/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.40/1.02      inference(unflattening,[status(thm)],[c_286]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_452,plain,
% 2.40/1.02      ( k8_relset_1(X0,X1,sK2,X1) = k1_relset_1(X0,X1,sK2)
% 2.40/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.40/1.02      inference(light_normalisation,[status(thm)],[c_287,c_205,c_210]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_675,plain,
% 2.40/1.02      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
% 2.40/1.02      inference(equality_resolution,[status(thm)],[c_452]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_1073,plain,
% 2.40/1.02      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relat_1(sK2) ),
% 2.40/1.02      inference(light_normalisation,[status(thm)],[c_675,c_513]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_18,negated_conjecture,
% 2.40/1.02      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
% 2.40/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_417,plain,
% 2.40/1.02      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) != k2_struct_0(sK0) ),
% 2.40/1.02      inference(light_normalisation,[status(thm)],[c_18,c_205,c_210]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_1075,plain,
% 2.40/1.02      ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 2.40/1.02      inference(demodulation,[status(thm)],[c_1073,c_417]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_1993,plain,
% 2.40/1.02      ( k2_struct_0(sK1) = k1_xboole_0 ),
% 2.40/1.02      inference(global_propositional_subsumption,
% 2.40/1.02                [status(thm)],
% 2.40/1.02                [c_1812,c_1075]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_0,plain,
% 2.40/1.02      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.40/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_674,plain,
% 2.40/1.02      ( k8_relset_1(X0,k1_xboole_0,sK2,k1_xboole_0) = k1_relset_1(X0,k1_xboole_0,sK2)
% 2.40/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k1_xboole_0) ),
% 2.40/1.02      inference(superposition,[status(thm)],[c_0,c_452]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_2006,plain,
% 2.40/1.02      ( k8_relset_1(X0,k1_xboole_0,sK2,k1_xboole_0) = k1_relset_1(X0,k1_xboole_0,sK2)
% 2.40/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0) ),
% 2.40/1.02      inference(demodulation,[status(thm)],[c_1993,c_674]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_19,negated_conjecture,
% 2.40/1.02      ( k1_xboole_0 != k2_struct_0(sK1)
% 2.40/1.02      | k1_xboole_0 = k2_struct_0(sK0) ),
% 2.40/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_2028,plain,
% 2.40/1.02      ( k2_struct_0(sK0) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.40/1.02      inference(demodulation,[status(thm)],[c_1993,c_19]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_2029,plain,
% 2.40/1.02      ( k2_struct_0(sK0) = k1_xboole_0 ),
% 2.40/1.02      inference(equality_resolution_simp,[status(thm)],[c_2028]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_7,plain,
% 2.40/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.40/1.02      | k9_relat_1(k6_relat_1(X1),X0) = X0 ),
% 2.40/1.02      inference(cnf_transformation,[],[f39]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_250,plain,
% 2.40/1.02      ( k9_relat_1(k6_relat_1(X0),X1) = X1
% 2.40/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0)
% 2.40/1.02      | sK2 != X1 ),
% 2.40/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_20]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_251,plain,
% 2.40/1.02      ( k9_relat_1(k6_relat_1(X0),sK2) = sK2
% 2.40/1.02      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != k1_zfmisc_1(X0) ),
% 2.40/1.02      inference(unflattening,[status(thm)],[c_250]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_426,plain,
% 2.40/1.02      ( k9_relat_1(k6_relat_1(X0),sK2) = sK2
% 2.40/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(X0) ),
% 2.40/1.02      inference(light_normalisation,[status(thm)],[c_251,c_205,c_210]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_510,plain,
% 2.40/1.02      ( k9_relat_1(k6_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))),sK2) = sK2 ),
% 2.40/1.02      inference(equality_resolution,[status(thm)],[c_426]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_2016,plain,
% 2.40/1.02      ( k9_relat_1(k6_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)),sK2) = sK2 ),
% 2.40/1.02      inference(demodulation,[status(thm)],[c_1993,c_510]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_2088,plain,
% 2.40/1.02      ( k9_relat_1(k6_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),sK2) = sK2 ),
% 2.40/1.02      inference(light_normalisation,[status(thm)],[c_2016,c_2029]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_1,plain,
% 2.40/1.02      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.40/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.40/1.02  
% 2.40/1.02  cnf(c_3,plain,
% 2.40/1.02      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.40/1.02      inference(cnf_transformation,[],[f35]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_6,plain,
% 2.40/1.03      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.40/1.03      inference(cnf_transformation,[],[f38]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_2090,plain,
% 2.40/1.03      ( sK2 = k1_xboole_0 ),
% 2.40/1.03      inference(demodulation,[status(thm)],[c_2088,c_1,c_3,c_6]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_656,plain,
% 2.40/1.03      ( k1_relset_1(X0,k1_xboole_0,sK2) = k1_relat_1(sK2)
% 2.40/1.03      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) != k1_zfmisc_1(k1_xboole_0) ),
% 2.40/1.03      inference(superposition,[status(thm)],[c_0,c_431]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_2010,plain,
% 2.40/1.03      ( k1_relset_1(X0,k1_xboole_0,sK2) = k1_relat_1(sK2)
% 2.40/1.03      | k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0) ),
% 2.40/1.03      inference(demodulation,[status(thm)],[c_1993,c_656]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_2167,plain,
% 2.40/1.03      ( k1_relset_1(X0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
% 2.40/1.03      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0) ),
% 2.40/1.03      inference(light_normalisation,[status(thm)],[c_2010,c_2029,c_2090]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_5,plain,
% 2.40/1.03      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.40/1.03      inference(cnf_transformation,[],[f36]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_2170,plain,
% 2.40/1.03      ( k1_relset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 2.40/1.03      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0) ),
% 2.40/1.03      inference(light_normalisation,[status(thm)],[c_2167,c_5]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_2171,plain,
% 2.40/1.03      ( k1_relset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 2.40/1.03      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
% 2.40/1.03      inference(demodulation,[status(thm)],[c_2170,c_1]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_2172,plain,
% 2.40/1.03      ( k1_relset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.40/1.03      inference(equality_resolution_simp,[status(thm)],[c_2171]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_2194,plain,
% 2.40/1.03      ( k8_relset_1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 2.40/1.03      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k1_xboole_0) ),
% 2.40/1.03      inference(light_normalisation,
% 2.40/1.03                [status(thm)],
% 2.40/1.03                [c_2006,c_2029,c_2090,c_2172]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_2197,plain,
% 2.40/1.03      ( k8_relset_1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 2.40/1.03      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) ),
% 2.40/1.03      inference(demodulation,[status(thm)],[c_2194,c_1]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_2198,plain,
% 2.40/1.03      ( k8_relset_1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.40/1.03      inference(equality_resolution_simp,[status(thm)],[c_2197]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_2245,plain,
% 2.40/1.03      ( k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.40/1.03      inference(instantiation,[status(thm)],[c_2198]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_371,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_516,plain,
% 2.40/1.03      ( X0 != X1 | k2_struct_0(sK0) != X1 | k2_struct_0(sK0) = X0 ),
% 2.40/1.03      inference(instantiation,[status(thm)],[c_371]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_1436,plain,
% 2.40/1.03      ( k8_relset_1(X0,X1,X2,X3) != X4
% 2.40/1.03      | k2_struct_0(sK0) != X4
% 2.40/1.03      | k2_struct_0(sK0) = k8_relset_1(X0,X1,X2,X3) ),
% 2.40/1.03      inference(instantiation,[status(thm)],[c_516]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_1439,plain,
% 2.40/1.03      ( k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.40/1.03      | k2_struct_0(sK0) = k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 2.40/1.03      | k2_struct_0(sK0) != k1_xboole_0 ),
% 2.40/1.03      inference(instantiation,[status(thm)],[c_1436]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_381,plain,
% 2.40/1.03      ( X0 != X1
% 2.40/1.03      | X2 != X3
% 2.40/1.03      | X4 != X5
% 2.40/1.03      | X6 != X7
% 2.40/1.03      | k8_relset_1(X0,X2,X4,X6) = k8_relset_1(X1,X3,X5,X7) ),
% 2.40/1.03      theory(equality) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_1320,plain,
% 2.40/1.03      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k8_relset_1(X0,X1,X2,X3)
% 2.40/1.03      | u1_struct_0(sK1) != X1
% 2.40/1.03      | u1_struct_0(sK0) != X0
% 2.40/1.03      | k2_struct_0(sK1) != X3
% 2.40/1.03      | sK2 != X2 ),
% 2.40/1.03      inference(instantiation,[status(thm)],[c_381]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_1322,plain,
% 2.40/1.03      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 2.40/1.03      | u1_struct_0(sK1) != k1_xboole_0
% 2.40/1.03      | u1_struct_0(sK0) != k1_xboole_0
% 2.40/1.03      | k2_struct_0(sK1) != k1_xboole_0
% 2.40/1.03      | sK2 != k1_xboole_0 ),
% 2.40/1.03      inference(instantiation,[status(thm)],[c_1320]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_500,plain,
% 2.40/1.03      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != X0
% 2.40/1.03      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k2_struct_0(sK0)
% 2.40/1.03      | k2_struct_0(sK0) != X0 ),
% 2.40/1.03      inference(instantiation,[status(thm)],[c_371]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_1319,plain,
% 2.40/1.03      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k8_relset_1(X0,X1,X2,X3)
% 2.40/1.03      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k2_struct_0(sK0)
% 2.40/1.03      | k2_struct_0(sK0) != k8_relset_1(X0,X1,X2,X3) ),
% 2.40/1.03      inference(instantiation,[status(thm)],[c_500]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_1321,plain,
% 2.40/1.03      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) != k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 2.40/1.03      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k2_struct_0(sK0)
% 2.40/1.03      | k2_struct_0(sK0) != k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 2.40/1.03      inference(instantiation,[status(thm)],[c_1319]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_634,plain,
% 2.40/1.03      ( X0 != X1 | u1_struct_0(sK1) != X1 | u1_struct_0(sK1) = X0 ),
% 2.40/1.03      inference(instantiation,[status(thm)],[c_371]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_1150,plain,
% 2.40/1.03      ( X0 != k2_struct_0(sK1)
% 2.40/1.03      | u1_struct_0(sK1) = X0
% 2.40/1.03      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 2.40/1.03      inference(instantiation,[status(thm)],[c_634]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_1151,plain,
% 2.40/1.03      ( u1_struct_0(sK1) != k2_struct_0(sK1)
% 2.40/1.03      | u1_struct_0(sK1) = k1_xboole_0
% 2.40/1.03      | k1_xboole_0 != k2_struct_0(sK1) ),
% 2.40/1.03      inference(instantiation,[status(thm)],[c_1150]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_596,plain,
% 2.40/1.03      ( X0 != k2_struct_0(sK0)
% 2.40/1.03      | k2_struct_0(sK0) = X0
% 2.40/1.03      | k2_struct_0(sK0) != k2_struct_0(sK0) ),
% 2.40/1.03      inference(instantiation,[status(thm)],[c_516]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_598,plain,
% 2.40/1.03      ( k2_struct_0(sK0) != k2_struct_0(sK0)
% 2.40/1.03      | k2_struct_0(sK0) = k1_xboole_0
% 2.40/1.03      | k1_xboole_0 != k2_struct_0(sK0) ),
% 2.40/1.03      inference(instantiation,[status(thm)],[c_596]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_370,plain,( X0 = X0 ),theory(equality) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_574,plain,
% 2.40/1.03      ( sK0 = sK0 ),
% 2.40/1.03      inference(instantiation,[status(thm)],[c_370]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_382,plain,
% 2.40/1.03      ( X0 != X1 | k2_struct_0(X0) = k2_struct_0(X1) ),
% 2.40/1.03      theory(equality) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_518,plain,
% 2.40/1.03      ( k2_struct_0(sK0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.40/1.03      inference(instantiation,[status(thm)],[c_382]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_573,plain,
% 2.40/1.03      ( k2_struct_0(sK0) = k2_struct_0(sK0) | sK0 != sK0 ),
% 2.40/1.03      inference(instantiation,[status(thm)],[c_518]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_504,plain,
% 2.40/1.03      ( u1_struct_0(sK0) != X0
% 2.40/1.03      | u1_struct_0(sK0) = k1_xboole_0
% 2.40/1.03      | k1_xboole_0 != X0 ),
% 2.40/1.03      inference(instantiation,[status(thm)],[c_371]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_563,plain,
% 2.40/1.03      ( u1_struct_0(sK0) != k2_struct_0(sK0)
% 2.40/1.03      | u1_struct_0(sK0) = k1_xboole_0
% 2.40/1.03      | k1_xboole_0 != k2_struct_0(sK0) ),
% 2.40/1.03      inference(instantiation,[status(thm)],[c_504]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_502,plain,
% 2.40/1.03      ( k2_struct_0(sK1) != X0
% 2.40/1.03      | k1_xboole_0 != X0
% 2.40/1.03      | k1_xboole_0 = k2_struct_0(sK1) ),
% 2.40/1.03      inference(instantiation,[status(thm)],[c_371]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_503,plain,
% 2.40/1.03      ( k2_struct_0(sK1) != k1_xboole_0
% 2.40/1.03      | k1_xboole_0 = k2_struct_0(sK1)
% 2.40/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 2.40/1.03      inference(instantiation,[status(thm)],[c_502]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_65,plain,
% 2.40/1.03      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.40/1.03      inference(instantiation,[status(thm)],[c_1]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_2,plain,
% 2.40/1.03      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.40/1.03      | k1_xboole_0 = X1
% 2.40/1.03      | k1_xboole_0 = X0 ),
% 2.40/1.03      inference(cnf_transformation,[],[f32]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(c_64,plain,
% 2.40/1.03      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.40/1.03      | k1_xboole_0 = k1_xboole_0 ),
% 2.40/1.03      inference(instantiation,[status(thm)],[c_2]) ).
% 2.40/1.03  
% 2.40/1.03  cnf(contradiction,plain,
% 2.40/1.03      ( $false ),
% 2.40/1.03      inference(minisat,
% 2.40/1.03                [status(thm)],
% 2.40/1.03                [c_2245,c_2090,c_1812,c_1439,c_1322,c_1321,c_1151,c_1075,
% 2.40/1.03                 c_598,c_574,c_573,c_563,c_503,c_210,c_205,c_65,c_64,
% 2.40/1.03                 c_18,c_19]) ).
% 2.40/1.03  
% 2.40/1.03  
% 2.40/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.40/1.03  
% 2.40/1.03  ------                               Statistics
% 2.40/1.03  
% 2.40/1.03  ------ General
% 2.40/1.03  
% 2.40/1.03  abstr_ref_over_cycles:                  0
% 2.40/1.03  abstr_ref_under_cycles:                 0
% 2.40/1.03  gc_basic_clause_elim:                   0
% 2.40/1.03  forced_gc_time:                         0
% 2.40/1.03  parsing_time:                           0.008
% 2.40/1.03  unif_index_cands_time:                  0.
% 2.40/1.03  unif_index_add_time:                    0.
% 2.40/1.03  orderings_time:                         0.
% 2.40/1.03  out_proof_time:                         0.017
% 2.40/1.03  total_time:                             0.127
% 2.40/1.03  num_of_symbols:                         51
% 2.40/1.03  num_of_terms:                           2294
% 2.40/1.03  
% 2.40/1.03  ------ Preprocessing
% 2.40/1.03  
% 2.40/1.03  num_of_splits:                          0
% 2.40/1.03  num_of_split_atoms:                     0
% 2.40/1.03  num_of_reused_defs:                     0
% 2.40/1.03  num_eq_ax_congr_red:                    17
% 2.40/1.03  num_of_sem_filtered_clauses:            0
% 2.40/1.03  num_of_subtypes:                        0
% 2.40/1.03  monotx_restored_types:                  0
% 2.40/1.03  sat_num_of_epr_types:                   0
% 2.40/1.03  sat_num_of_non_cyclic_types:            0
% 2.40/1.03  sat_guarded_non_collapsed_types:        0
% 2.40/1.03  num_pure_diseq_elim:                    0
% 2.40/1.03  simp_replaced_by:                       0
% 2.40/1.03  res_preprocessed:                       81
% 2.40/1.03  prep_upred:                             0
% 2.40/1.03  prep_unflattend:                        15
% 2.40/1.03  smt_new_axioms:                         0
% 2.40/1.03  pred_elim_cands:                        0
% 2.40/1.03  pred_elim:                              4
% 2.40/1.03  pred_elim_cl:                           4
% 2.40/1.03  pred_elim_cycles:                       5
% 2.40/1.03  merged_defs:                            0
% 2.40/1.03  merged_defs_ncl:                        0
% 2.40/1.03  bin_hyper_res:                          0
% 2.40/1.03  prep_cycles:                            3
% 2.40/1.03  pred_elim_time:                         0.004
% 2.40/1.03  splitting_time:                         0.
% 2.40/1.03  sem_filter_time:                        0.
% 2.40/1.03  monotx_time:                            0.
% 2.40/1.03  subtype_inf_time:                       0.
% 2.40/1.03  
% 2.40/1.03  ------ Problem properties
% 2.40/1.03  
% 2.40/1.03  clauses:                                21
% 2.40/1.03  conjectures:                            2
% 2.40/1.03  epr:                                    0
% 2.40/1.03  horn:                                   19
% 2.40/1.03  ground:                                 9
% 2.40/1.03  unary:                                  9
% 2.40/1.03  binary:                                 10
% 2.40/1.03  lits:                                   35
% 2.40/1.03  lits_eq:                                35
% 2.40/1.03  fd_pure:                                0
% 2.40/1.03  fd_pseudo:                              0
% 2.40/1.03  fd_cond:                                1
% 2.40/1.03  fd_pseudo_cond:                         0
% 2.40/1.03  ac_symbols:                             0
% 2.40/1.03  
% 2.40/1.03  ------ Propositional Solver
% 2.40/1.03  
% 2.40/1.03  prop_solver_calls:                      24
% 2.40/1.03  prop_fast_solver_calls:                 418
% 2.40/1.03  smt_solver_calls:                       0
% 2.40/1.03  smt_fast_solver_calls:                  0
% 2.40/1.03  prop_num_of_clauses:                    889
% 2.40/1.03  prop_preprocess_simplified:             2404
% 2.40/1.03  prop_fo_subsumed:                       4
% 2.40/1.03  prop_solver_time:                       0.
% 2.40/1.03  smt_solver_time:                        0.
% 2.40/1.03  smt_fast_solver_time:                   0.
% 2.40/1.03  prop_fast_solver_time:                  0.
% 2.40/1.03  prop_unsat_core_time:                   0.
% 2.40/1.03  
% 2.40/1.03  ------ QBF
% 2.40/1.03  
% 2.40/1.03  qbf_q_res:                              0
% 2.40/1.03  qbf_num_tautologies:                    0
% 2.40/1.03  qbf_prep_cycles:                        0
% 2.40/1.03  
% 2.40/1.03  ------ BMC1
% 2.40/1.03  
% 2.40/1.03  bmc1_current_bound:                     -1
% 2.40/1.03  bmc1_last_solved_bound:                 -1
% 2.40/1.03  bmc1_unsat_core_size:                   -1
% 2.40/1.03  bmc1_unsat_core_parents_size:           -1
% 2.40/1.03  bmc1_merge_next_fun:                    0
% 2.40/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.40/1.03  
% 2.40/1.03  ------ Instantiation
% 2.40/1.03  
% 2.40/1.03  inst_num_of_clauses:                    506
% 2.40/1.03  inst_num_in_passive:                    115
% 2.40/1.03  inst_num_in_active:                     187
% 2.40/1.03  inst_num_in_unprocessed:                204
% 2.40/1.03  inst_num_of_loops:                      240
% 2.40/1.03  inst_num_of_learning_restarts:          0
% 2.40/1.03  inst_num_moves_active_passive:          49
% 2.40/1.03  inst_lit_activity:                      0
% 2.40/1.03  inst_lit_activity_moves:                0
% 2.40/1.03  inst_num_tautologies:                   0
% 2.40/1.03  inst_num_prop_implied:                  0
% 2.40/1.03  inst_num_existing_simplified:           0
% 2.40/1.03  inst_num_eq_res_simplified:             0
% 2.40/1.03  inst_num_child_elim:                    0
% 2.40/1.03  inst_num_of_dismatching_blockings:      82
% 2.40/1.03  inst_num_of_non_proper_insts:           352
% 2.40/1.03  inst_num_of_duplicates:                 0
% 2.40/1.03  inst_inst_num_from_inst_to_res:         0
% 2.40/1.03  inst_dismatching_checking_time:         0.
% 2.40/1.03  
% 2.40/1.03  ------ Resolution
% 2.40/1.03  
% 2.40/1.03  res_num_of_clauses:                     0
% 2.40/1.03  res_num_in_passive:                     0
% 2.40/1.03  res_num_in_active:                      0
% 2.40/1.03  res_num_of_loops:                       84
% 2.40/1.03  res_forward_subset_subsumed:            58
% 2.40/1.03  res_backward_subset_subsumed:           4
% 2.40/1.03  res_forward_subsumed:                   0
% 2.40/1.03  res_backward_subsumed:                  0
% 2.40/1.03  res_forward_subsumption_resolution:     0
% 2.40/1.03  res_backward_subsumption_resolution:    0
% 2.40/1.03  res_clause_to_clause_subsumption:       114
% 2.40/1.03  res_orphan_elimination:                 0
% 2.40/1.03  res_tautology_del:                      52
% 2.40/1.03  res_num_eq_res_simplified:              1
% 2.40/1.03  res_num_sel_changes:                    0
% 2.40/1.03  res_moves_from_active_to_pass:          0
% 2.40/1.03  
% 2.40/1.03  ------ Superposition
% 2.40/1.03  
% 2.40/1.03  sup_time_total:                         0.
% 2.40/1.03  sup_time_generating:                    0.
% 2.40/1.03  sup_time_sim_full:                      0.
% 2.40/1.03  sup_time_sim_immed:                     0.
% 2.40/1.03  
% 2.40/1.03  sup_num_of_clauses:                     30
% 2.40/1.03  sup_num_in_active:                      11
% 2.40/1.03  sup_num_in_passive:                     19
% 2.40/1.03  sup_num_of_loops:                       47
% 2.40/1.03  sup_fw_superposition:                   8
% 2.40/1.03  sup_bw_superposition:                   12
% 2.40/1.03  sup_immediate_simplified:               70
% 2.40/1.03  sup_given_eliminated:                   0
% 2.40/1.03  comparisons_done:                       0
% 2.40/1.03  comparisons_avoided:                    6
% 2.40/1.03  
% 2.40/1.03  ------ Simplifications
% 2.40/1.03  
% 2.40/1.03  
% 2.40/1.03  sim_fw_subset_subsumed:                 0
% 2.40/1.03  sim_bw_subset_subsumed:                 0
% 2.40/1.03  sim_fw_subsumed:                        2
% 2.40/1.03  sim_bw_subsumed:                        4
% 2.40/1.03  sim_fw_subsumption_res:                 0
% 2.40/1.03  sim_bw_subsumption_res:                 0
% 2.40/1.03  sim_tautology_del:                      0
% 2.40/1.03  sim_eq_tautology_del:                   6
% 2.40/1.03  sim_eq_res_simp:                        12
% 2.40/1.03  sim_fw_demodulated:                     31
% 2.40/1.03  sim_bw_demodulated:                     46
% 2.40/1.03  sim_light_normalised:                   57
% 2.40/1.03  sim_joinable_taut:                      0
% 2.40/1.03  sim_joinable_simp:                      0
% 2.40/1.03  sim_ac_normalised:                      0
% 2.40/1.03  sim_smt_subsumption:                    0
% 2.40/1.03  
%------------------------------------------------------------------------------
