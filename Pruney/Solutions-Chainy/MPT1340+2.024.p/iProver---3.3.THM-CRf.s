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
% DateTime   : Thu Dec  3 12:17:26 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :  217 (2642 expanded)
%              Number of clauses        :  136 ( 728 expanded)
%              Number of leaves         :   20 ( 776 expanded)
%              Depth                    :   25
%              Number of atoms          :  768 (17322 expanded)
%              Number of equality atoms :  327 (2959 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,
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

fof(f51,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f50,f49,f48])).

fof(f88,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f80,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f89,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f87,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f84,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f90,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f59,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f86,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f79,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f78,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
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

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f60,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f73])).

fof(f91,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f57,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f54,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1198,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_28,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_37,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_466,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_37])).

cnf(c_467,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_39,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_471,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_39])).

cnf(c_472,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_1239,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1198,c_467,c_472])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1214,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1645,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1239,c_1214])).

cnf(c_33,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1236,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_33,c_467,c_472])).

cnf(c_1858,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1645,c_1236])).

cnf(c_1960,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1858,c_1239])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1205,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4216,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1960,c_1205])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1212,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2742,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(superposition,[status(thm)],[c_1960,c_1212])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1213,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2476,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1960,c_1213])).

cnf(c_2743,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(demodulation,[status(thm)],[c_2742,c_2476])).

cnf(c_4220,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k2_struct_0(sK0)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4216,c_2743])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1197,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1233,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1197,c_467,c_472])).

cnf(c_1961,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1858,c_1233])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_29,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_439,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_29])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_457,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_439,c_38])).

cnf(c_458,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_460,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_458,c_37])).

cnf(c_1230,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_460,c_467])).

cnf(c_1962,plain,
    ( k2_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1858,c_1230])).

cnf(c_7236,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4220,c_1961,c_1962])).

cnf(c_32,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1199,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_6,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1218,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3945,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1199,c_1218])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1479,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1494,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4351,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3945,c_36,c_34,c_32,c_1479,c_1494])).

cnf(c_25,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1202,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4354,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4351,c_1202])).

cnf(c_7,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1217,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3720,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1199,c_1217])).

cnf(c_1497,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4331,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3720,c_36,c_34,c_32,c_1479,c_1497])).

cnf(c_4366,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4354,c_4331])).

cnf(c_43,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_45,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_46,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1480,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1479])).

cnf(c_26,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1598,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1610,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1598])).

cnf(c_1597,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1612,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1597])).

cnf(c_1798,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1539,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1823,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1539])).

cnf(c_1824,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1823])).

cnf(c_4429,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4366,c_36,c_43,c_34,c_45,c_46,c_1479,c_1480,c_1610,c_1597,c_1612,c_1798,c_1824])).

cnf(c_4440,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4429,c_1214])).

cnf(c_4442,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4440,c_4351])).

cnf(c_1204,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4655,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4442,c_1204])).

cnf(c_8,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1216,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3008,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1199,c_1216])).

cnf(c_1500,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3243,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3008,c_36,c_34,c_32,c_1479,c_1500])).

cnf(c_4661,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4655,c_3243])).

cnf(c_5207,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4661,c_43,c_45,c_1480,c_1612])).

cnf(c_5215,plain,
    ( k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    inference(superposition,[status(thm)],[c_5207,c_1212])).

cnf(c_1215,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1563,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1239,c_1215])).

cnf(c_2965,plain,
    ( k8_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0,X1) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_1213])).

cnf(c_3574,plain,
    ( k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1563,c_2965])).

cnf(c_1797,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3594,plain,
    ( k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3574,c_36,c_34,c_1479,c_1597,c_1797])).

cnf(c_5223,plain,
    ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(demodulation,[status(thm)],[c_5215,c_3594])).

cnf(c_4215,plain,
    ( k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_1205])).

cnf(c_58,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5690,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4215,c_58])).

cnf(c_5691,plain,
    ( k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5690])).

cnf(c_5701,plain,
    ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1563,c_5691])).

cnf(c_5935,plain,
    ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5701,c_43,c_1962])).

cnf(c_6230,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_5223,c_5935])).

cnf(c_7238,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_7236,c_6230])).

cnf(c_1958,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1858,c_1645])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1200,plain,
    ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2151,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1958,c_1200])).

cnf(c_2632,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2151,c_43,c_46,c_1960,c_1961])).

cnf(c_20,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_31,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_480,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_31])).

cnf(c_481,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_1194,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_1402,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1194,c_467,c_472])).

cnf(c_1959,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1858,c_1402])).

cnf(c_2635,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2632,c_1959])).

cnf(c_7246,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7238,c_2635])).

cnf(c_4469,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4442,c_1200])).

cnf(c_4475,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4469,c_3243])).

cnf(c_3,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1476,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1477,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1476])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_229,plain,
    ( v1_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_9,c_1])).

cnf(c_230,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(renaming,[status(thm)],[c_229])).

cnf(c_1195,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_230])).

cnf(c_1558,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1239,c_1195])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1544,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1828,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1544])).

cnf(c_1829,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1828])).

cnf(c_5174,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4475,c_36,c_43,c_34,c_45,c_46,c_1477,c_1479,c_1480,c_1558,c_1610,c_1597,c_1612,c_1798,c_1824,c_1829])).

cnf(c_7260,plain,
    ( sK2 != sK2
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7246,c_5174])).

cnf(c_7261,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7260])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7261,c_1612,c_1610,c_1480,c_45,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:41:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 2.90/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/0.97  
% 2.90/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.90/0.97  
% 2.90/0.97  ------  iProver source info
% 2.90/0.97  
% 2.90/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.90/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.90/0.97  git: non_committed_changes: false
% 2.90/0.97  git: last_make_outside_of_git: false
% 2.90/0.97  
% 2.90/0.97  ------ 
% 2.90/0.97  
% 2.90/0.97  ------ Input Options
% 2.90/0.97  
% 2.90/0.97  --out_options                           all
% 2.90/0.97  --tptp_safe_out                         true
% 2.90/0.97  --problem_path                          ""
% 2.90/0.97  --include_path                          ""
% 2.90/0.97  --clausifier                            res/vclausify_rel
% 2.90/0.97  --clausifier_options                    --mode clausify
% 2.90/0.97  --stdin                                 false
% 2.90/0.97  --stats_out                             all
% 2.90/0.97  
% 2.90/0.97  ------ General Options
% 2.90/0.97  
% 2.90/0.97  --fof                                   false
% 2.90/0.97  --time_out_real                         305.
% 2.90/0.97  --time_out_virtual                      -1.
% 2.90/0.97  --symbol_type_check                     false
% 2.90/0.97  --clausify_out                          false
% 2.90/0.97  --sig_cnt_out                           false
% 2.90/0.97  --trig_cnt_out                          false
% 2.90/0.97  --trig_cnt_out_tolerance                1.
% 2.90/0.97  --trig_cnt_out_sk_spl                   false
% 2.90/0.97  --abstr_cl_out                          false
% 2.90/0.97  
% 2.90/0.97  ------ Global Options
% 2.90/0.97  
% 2.90/0.97  --schedule                              default
% 2.90/0.97  --add_important_lit                     false
% 2.90/0.97  --prop_solver_per_cl                    1000
% 2.90/0.97  --min_unsat_core                        false
% 2.90/0.97  --soft_assumptions                      false
% 2.90/0.97  --soft_lemma_size                       3
% 2.90/0.97  --prop_impl_unit_size                   0
% 2.90/0.97  --prop_impl_unit                        []
% 2.90/0.97  --share_sel_clauses                     true
% 2.90/0.97  --reset_solvers                         false
% 2.90/0.97  --bc_imp_inh                            [conj_cone]
% 2.90/0.97  --conj_cone_tolerance                   3.
% 2.90/0.97  --extra_neg_conj                        none
% 2.90/0.97  --large_theory_mode                     true
% 2.90/0.97  --prolific_symb_bound                   200
% 2.90/0.97  --lt_threshold                          2000
% 2.90/0.97  --clause_weak_htbl                      true
% 2.90/0.97  --gc_record_bc_elim                     false
% 2.90/0.97  
% 2.90/0.97  ------ Preprocessing Options
% 2.90/0.97  
% 2.90/0.97  --preprocessing_flag                    true
% 2.90/0.97  --time_out_prep_mult                    0.1
% 2.90/0.97  --splitting_mode                        input
% 2.90/0.97  --splitting_grd                         true
% 2.90/0.97  --splitting_cvd                         false
% 2.90/0.97  --splitting_cvd_svl                     false
% 2.90/0.97  --splitting_nvd                         32
% 2.90/0.97  --sub_typing                            true
% 2.90/0.97  --prep_gs_sim                           true
% 2.90/0.97  --prep_unflatten                        true
% 2.90/0.97  --prep_res_sim                          true
% 2.90/0.97  --prep_upred                            true
% 2.90/0.97  --prep_sem_filter                       exhaustive
% 2.90/0.97  --prep_sem_filter_out                   false
% 2.90/0.97  --pred_elim                             true
% 2.90/0.97  --res_sim_input                         true
% 2.90/0.97  --eq_ax_congr_red                       true
% 2.90/0.97  --pure_diseq_elim                       true
% 2.90/0.97  --brand_transform                       false
% 2.90/0.97  --non_eq_to_eq                          false
% 2.90/0.97  --prep_def_merge                        true
% 2.90/0.97  --prep_def_merge_prop_impl              false
% 2.90/0.97  --prep_def_merge_mbd                    true
% 2.90/0.97  --prep_def_merge_tr_red                 false
% 2.90/0.97  --prep_def_merge_tr_cl                  false
% 2.90/0.97  --smt_preprocessing                     true
% 2.90/0.97  --smt_ac_axioms                         fast
% 2.90/0.97  --preprocessed_out                      false
% 2.90/0.97  --preprocessed_stats                    false
% 2.90/0.97  
% 2.90/0.97  ------ Abstraction refinement Options
% 2.90/0.97  
% 2.90/0.97  --abstr_ref                             []
% 2.90/0.97  --abstr_ref_prep                        false
% 2.90/0.97  --abstr_ref_until_sat                   false
% 2.90/0.97  --abstr_ref_sig_restrict                funpre
% 2.90/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.90/0.97  --abstr_ref_under                       []
% 2.90/0.97  
% 2.90/0.97  ------ SAT Options
% 2.90/0.97  
% 2.90/0.97  --sat_mode                              false
% 2.90/0.97  --sat_fm_restart_options                ""
% 2.90/0.97  --sat_gr_def                            false
% 2.90/0.97  --sat_epr_types                         true
% 2.90/0.97  --sat_non_cyclic_types                  false
% 2.90/0.97  --sat_finite_models                     false
% 2.90/0.97  --sat_fm_lemmas                         false
% 2.90/0.97  --sat_fm_prep                           false
% 2.90/0.97  --sat_fm_uc_incr                        true
% 2.90/0.97  --sat_out_model                         small
% 2.90/0.97  --sat_out_clauses                       false
% 2.90/0.97  
% 2.90/0.97  ------ QBF Options
% 2.90/0.97  
% 2.90/0.97  --qbf_mode                              false
% 2.90/0.97  --qbf_elim_univ                         false
% 2.90/0.97  --qbf_dom_inst                          none
% 2.90/0.97  --qbf_dom_pre_inst                      false
% 2.90/0.97  --qbf_sk_in                             false
% 2.90/0.97  --qbf_pred_elim                         true
% 2.90/0.97  --qbf_split                             512
% 2.90/0.97  
% 2.90/0.97  ------ BMC1 Options
% 2.90/0.97  
% 2.90/0.97  --bmc1_incremental                      false
% 2.90/0.97  --bmc1_axioms                           reachable_all
% 2.90/0.97  --bmc1_min_bound                        0
% 2.90/0.97  --bmc1_max_bound                        -1
% 2.90/0.97  --bmc1_max_bound_default                -1
% 2.90/0.97  --bmc1_symbol_reachability              true
% 2.90/0.97  --bmc1_property_lemmas                  false
% 2.90/0.97  --bmc1_k_induction                      false
% 2.90/0.97  --bmc1_non_equiv_states                 false
% 2.90/0.97  --bmc1_deadlock                         false
% 2.90/0.97  --bmc1_ucm                              false
% 2.90/0.97  --bmc1_add_unsat_core                   none
% 2.90/0.97  --bmc1_unsat_core_children              false
% 2.90/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.90/0.97  --bmc1_out_stat                         full
% 2.90/0.97  --bmc1_ground_init                      false
% 2.90/0.97  --bmc1_pre_inst_next_state              false
% 2.90/0.97  --bmc1_pre_inst_state                   false
% 2.90/0.97  --bmc1_pre_inst_reach_state             false
% 2.90/0.97  --bmc1_out_unsat_core                   false
% 2.90/0.97  --bmc1_aig_witness_out                  false
% 2.90/0.97  --bmc1_verbose                          false
% 2.90/0.97  --bmc1_dump_clauses_tptp                false
% 2.90/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.90/0.97  --bmc1_dump_file                        -
% 2.90/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.90/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.90/0.97  --bmc1_ucm_extend_mode                  1
% 2.90/0.97  --bmc1_ucm_init_mode                    2
% 2.90/0.97  --bmc1_ucm_cone_mode                    none
% 2.90/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.90/0.97  --bmc1_ucm_relax_model                  4
% 2.90/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.90/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.90/0.97  --bmc1_ucm_layered_model                none
% 2.90/0.97  --bmc1_ucm_max_lemma_size               10
% 2.90/0.97  
% 2.90/0.97  ------ AIG Options
% 2.90/0.97  
% 2.90/0.97  --aig_mode                              false
% 2.90/0.97  
% 2.90/0.97  ------ Instantiation Options
% 2.90/0.97  
% 2.90/0.97  --instantiation_flag                    true
% 2.90/0.97  --inst_sos_flag                         false
% 2.90/0.97  --inst_sos_phase                        true
% 2.90/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.90/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.90/0.97  --inst_lit_sel_side                     num_symb
% 2.90/0.97  --inst_solver_per_active                1400
% 2.90/0.97  --inst_solver_calls_frac                1.
% 2.90/0.97  --inst_passive_queue_type               priority_queues
% 2.90/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.90/0.97  --inst_passive_queues_freq              [25;2]
% 2.90/0.97  --inst_dismatching                      true
% 2.90/0.97  --inst_eager_unprocessed_to_passive     true
% 2.90/0.97  --inst_prop_sim_given                   true
% 2.90/0.97  --inst_prop_sim_new                     false
% 2.90/0.97  --inst_subs_new                         false
% 2.90/0.97  --inst_eq_res_simp                      false
% 2.90/0.97  --inst_subs_given                       false
% 2.90/0.97  --inst_orphan_elimination               true
% 2.90/0.97  --inst_learning_loop_flag               true
% 2.90/0.97  --inst_learning_start                   3000
% 2.90/0.97  --inst_learning_factor                  2
% 2.90/0.97  --inst_start_prop_sim_after_learn       3
% 2.90/0.97  --inst_sel_renew                        solver
% 2.90/0.97  --inst_lit_activity_flag                true
% 2.90/0.97  --inst_restr_to_given                   false
% 2.90/0.97  --inst_activity_threshold               500
% 2.90/0.97  --inst_out_proof                        true
% 2.90/0.97  
% 2.90/0.97  ------ Resolution Options
% 2.90/0.97  
% 2.90/0.97  --resolution_flag                       true
% 2.90/0.97  --res_lit_sel                           adaptive
% 2.90/0.97  --res_lit_sel_side                      none
% 2.90/0.97  --res_ordering                          kbo
% 2.90/0.97  --res_to_prop_solver                    active
% 2.90/0.97  --res_prop_simpl_new                    false
% 2.90/0.97  --res_prop_simpl_given                  true
% 2.90/0.97  --res_passive_queue_type                priority_queues
% 2.90/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.90/0.97  --res_passive_queues_freq               [15;5]
% 2.90/0.97  --res_forward_subs                      full
% 2.90/0.97  --res_backward_subs                     full
% 2.90/0.97  --res_forward_subs_resolution           true
% 2.90/0.97  --res_backward_subs_resolution          true
% 2.90/0.97  --res_orphan_elimination                true
% 2.90/0.97  --res_time_limit                        2.
% 2.90/0.97  --res_out_proof                         true
% 2.90/0.97  
% 2.90/0.97  ------ Superposition Options
% 2.90/0.97  
% 2.90/0.97  --superposition_flag                    true
% 2.90/0.97  --sup_passive_queue_type                priority_queues
% 2.90/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.90/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.90/0.97  --demod_completeness_check              fast
% 2.90/0.97  --demod_use_ground                      true
% 2.90/0.97  --sup_to_prop_solver                    passive
% 2.90/0.97  --sup_prop_simpl_new                    true
% 2.90/0.97  --sup_prop_simpl_given                  true
% 2.90/0.97  --sup_fun_splitting                     false
% 2.90/0.97  --sup_smt_interval                      50000
% 2.90/0.97  
% 2.90/0.97  ------ Superposition Simplification Setup
% 2.90/0.97  
% 2.90/0.97  --sup_indices_passive                   []
% 2.90/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.90/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/0.97  --sup_full_bw                           [BwDemod]
% 2.90/0.97  --sup_immed_triv                        [TrivRules]
% 2.90/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.90/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/0.97  --sup_immed_bw_main                     []
% 2.90/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.90/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.90/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.90/0.97  
% 2.90/0.97  ------ Combination Options
% 2.90/0.97  
% 2.90/0.97  --comb_res_mult                         3
% 2.90/0.97  --comb_sup_mult                         2
% 2.90/0.97  --comb_inst_mult                        10
% 2.90/0.97  
% 2.90/0.97  ------ Debug Options
% 2.90/0.97  
% 2.90/0.97  --dbg_backtrace                         false
% 2.90/0.97  --dbg_dump_prop_clauses                 false
% 2.90/0.97  --dbg_dump_prop_clauses_file            -
% 2.90/0.97  --dbg_out_stat                          false
% 2.90/0.97  ------ Parsing...
% 2.90/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.90/0.97  
% 2.90/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.90/0.97  
% 2.90/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.90/0.97  
% 2.90/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.90/0.97  ------ Proving...
% 2.90/0.97  ------ Problem Properties 
% 2.90/0.97  
% 2.90/0.97  
% 2.90/0.97  clauses                                 32
% 2.90/0.97  conjectures                             5
% 2.90/0.97  EPR                                     2
% 2.90/0.97  Horn                                    28
% 2.90/0.97  unary                                   8
% 2.90/0.97  binary                                  5
% 2.90/0.97  lits                                    92
% 2.90/0.97  lits eq                                 25
% 2.90/0.97  fd_pure                                 0
% 2.90/0.97  fd_pseudo                               0
% 2.90/0.97  fd_cond                                 3
% 2.90/0.97  fd_pseudo_cond                          0
% 2.90/0.97  AC symbols                              0
% 2.90/0.97  
% 2.90/0.97  ------ Schedule dynamic 5 is on 
% 2.90/0.97  
% 2.90/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.90/0.97  
% 2.90/0.97  
% 2.90/0.97  ------ 
% 2.90/0.97  Current options:
% 2.90/0.97  ------ 
% 2.90/0.97  
% 2.90/0.97  ------ Input Options
% 2.90/0.97  
% 2.90/0.97  --out_options                           all
% 2.90/0.97  --tptp_safe_out                         true
% 2.90/0.97  --problem_path                          ""
% 2.90/0.97  --include_path                          ""
% 2.90/0.97  --clausifier                            res/vclausify_rel
% 2.90/0.97  --clausifier_options                    --mode clausify
% 2.90/0.97  --stdin                                 false
% 2.90/0.97  --stats_out                             all
% 2.90/0.97  
% 2.90/0.97  ------ General Options
% 2.90/0.97  
% 2.90/0.97  --fof                                   false
% 2.90/0.97  --time_out_real                         305.
% 2.90/0.97  --time_out_virtual                      -1.
% 2.90/0.97  --symbol_type_check                     false
% 2.90/0.97  --clausify_out                          false
% 2.90/0.97  --sig_cnt_out                           false
% 2.90/0.97  --trig_cnt_out                          false
% 2.90/0.97  --trig_cnt_out_tolerance                1.
% 2.90/0.97  --trig_cnt_out_sk_spl                   false
% 2.90/0.97  --abstr_cl_out                          false
% 2.90/0.97  
% 2.90/0.97  ------ Global Options
% 2.90/0.97  
% 2.90/0.97  --schedule                              default
% 2.90/0.97  --add_important_lit                     false
% 2.90/0.97  --prop_solver_per_cl                    1000
% 2.90/0.97  --min_unsat_core                        false
% 2.90/0.97  --soft_assumptions                      false
% 2.90/0.97  --soft_lemma_size                       3
% 2.90/0.97  --prop_impl_unit_size                   0
% 2.90/0.97  --prop_impl_unit                        []
% 2.90/0.97  --share_sel_clauses                     true
% 2.90/0.97  --reset_solvers                         false
% 2.90/0.97  --bc_imp_inh                            [conj_cone]
% 2.90/0.97  --conj_cone_tolerance                   3.
% 2.90/0.97  --extra_neg_conj                        none
% 2.90/0.97  --large_theory_mode                     true
% 2.90/0.97  --prolific_symb_bound                   200
% 2.90/0.97  --lt_threshold                          2000
% 2.90/0.97  --clause_weak_htbl                      true
% 2.90/0.97  --gc_record_bc_elim                     false
% 2.90/0.97  
% 2.90/0.97  ------ Preprocessing Options
% 2.90/0.97  
% 2.90/0.97  --preprocessing_flag                    true
% 2.90/0.97  --time_out_prep_mult                    0.1
% 2.90/0.97  --splitting_mode                        input
% 2.90/0.97  --splitting_grd                         true
% 2.90/0.97  --splitting_cvd                         false
% 2.90/0.97  --splitting_cvd_svl                     false
% 2.90/0.97  --splitting_nvd                         32
% 2.90/0.97  --sub_typing                            true
% 2.90/0.97  --prep_gs_sim                           true
% 2.90/0.97  --prep_unflatten                        true
% 2.90/0.97  --prep_res_sim                          true
% 2.90/0.97  --prep_upred                            true
% 2.90/0.97  --prep_sem_filter                       exhaustive
% 2.90/0.97  --prep_sem_filter_out                   false
% 2.90/0.97  --pred_elim                             true
% 2.90/0.97  --res_sim_input                         true
% 2.90/0.97  --eq_ax_congr_red                       true
% 2.90/0.97  --pure_diseq_elim                       true
% 2.90/0.97  --brand_transform                       false
% 2.90/0.97  --non_eq_to_eq                          false
% 2.90/0.97  --prep_def_merge                        true
% 2.90/0.97  --prep_def_merge_prop_impl              false
% 2.90/0.97  --prep_def_merge_mbd                    true
% 2.90/0.97  --prep_def_merge_tr_red                 false
% 2.90/0.97  --prep_def_merge_tr_cl                  false
% 2.90/0.97  --smt_preprocessing                     true
% 2.90/0.97  --smt_ac_axioms                         fast
% 2.90/0.97  --preprocessed_out                      false
% 2.90/0.97  --preprocessed_stats                    false
% 2.90/0.97  
% 2.90/0.97  ------ Abstraction refinement Options
% 2.90/0.97  
% 2.90/0.97  --abstr_ref                             []
% 2.90/0.97  --abstr_ref_prep                        false
% 2.90/0.97  --abstr_ref_until_sat                   false
% 2.90/0.97  --abstr_ref_sig_restrict                funpre
% 2.90/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.90/0.97  --abstr_ref_under                       []
% 2.90/0.97  
% 2.90/0.97  ------ SAT Options
% 2.90/0.97  
% 2.90/0.97  --sat_mode                              false
% 2.90/0.97  --sat_fm_restart_options                ""
% 2.90/0.97  --sat_gr_def                            false
% 2.90/0.97  --sat_epr_types                         true
% 2.90/0.97  --sat_non_cyclic_types                  false
% 2.90/0.97  --sat_finite_models                     false
% 2.90/0.97  --sat_fm_lemmas                         false
% 2.90/0.97  --sat_fm_prep                           false
% 2.90/0.97  --sat_fm_uc_incr                        true
% 2.90/0.97  --sat_out_model                         small
% 2.90/0.97  --sat_out_clauses                       false
% 2.90/0.97  
% 2.90/0.97  ------ QBF Options
% 2.90/0.97  
% 2.90/0.97  --qbf_mode                              false
% 2.90/0.97  --qbf_elim_univ                         false
% 2.90/0.97  --qbf_dom_inst                          none
% 2.90/0.97  --qbf_dom_pre_inst                      false
% 2.90/0.97  --qbf_sk_in                             false
% 2.90/0.97  --qbf_pred_elim                         true
% 2.90/0.97  --qbf_split                             512
% 2.90/0.97  
% 2.90/0.97  ------ BMC1 Options
% 2.90/0.97  
% 2.90/0.97  --bmc1_incremental                      false
% 2.90/0.97  --bmc1_axioms                           reachable_all
% 2.90/0.97  --bmc1_min_bound                        0
% 2.90/0.97  --bmc1_max_bound                        -1
% 2.90/0.97  --bmc1_max_bound_default                -1
% 2.90/0.97  --bmc1_symbol_reachability              true
% 2.90/0.97  --bmc1_property_lemmas                  false
% 2.90/0.97  --bmc1_k_induction                      false
% 2.90/0.97  --bmc1_non_equiv_states                 false
% 2.90/0.97  --bmc1_deadlock                         false
% 2.90/0.97  --bmc1_ucm                              false
% 2.90/0.97  --bmc1_add_unsat_core                   none
% 2.90/0.97  --bmc1_unsat_core_children              false
% 2.90/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.90/0.97  --bmc1_out_stat                         full
% 2.90/0.97  --bmc1_ground_init                      false
% 2.90/0.97  --bmc1_pre_inst_next_state              false
% 2.90/0.97  --bmc1_pre_inst_state                   false
% 2.90/0.97  --bmc1_pre_inst_reach_state             false
% 2.90/0.97  --bmc1_out_unsat_core                   false
% 2.90/0.97  --bmc1_aig_witness_out                  false
% 2.90/0.97  --bmc1_verbose                          false
% 2.90/0.97  --bmc1_dump_clauses_tptp                false
% 2.90/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.90/0.97  --bmc1_dump_file                        -
% 2.90/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.90/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.90/0.97  --bmc1_ucm_extend_mode                  1
% 2.90/0.97  --bmc1_ucm_init_mode                    2
% 2.90/0.97  --bmc1_ucm_cone_mode                    none
% 2.90/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.90/0.97  --bmc1_ucm_relax_model                  4
% 2.90/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.90/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.90/0.97  --bmc1_ucm_layered_model                none
% 2.90/0.97  --bmc1_ucm_max_lemma_size               10
% 2.90/0.97  
% 2.90/0.97  ------ AIG Options
% 2.90/0.97  
% 2.90/0.97  --aig_mode                              false
% 2.90/0.97  
% 2.90/0.97  ------ Instantiation Options
% 2.90/0.97  
% 2.90/0.97  --instantiation_flag                    true
% 2.90/0.97  --inst_sos_flag                         false
% 2.90/0.97  --inst_sos_phase                        true
% 2.90/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.90/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.90/0.97  --inst_lit_sel_side                     none
% 2.90/0.97  --inst_solver_per_active                1400
% 2.90/0.97  --inst_solver_calls_frac                1.
% 2.90/0.97  --inst_passive_queue_type               priority_queues
% 2.90/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.90/0.97  --inst_passive_queues_freq              [25;2]
% 2.90/0.97  --inst_dismatching                      true
% 2.90/0.97  --inst_eager_unprocessed_to_passive     true
% 2.90/0.97  --inst_prop_sim_given                   true
% 2.90/0.97  --inst_prop_sim_new                     false
% 2.90/0.97  --inst_subs_new                         false
% 2.90/0.97  --inst_eq_res_simp                      false
% 2.90/0.97  --inst_subs_given                       false
% 2.90/0.97  --inst_orphan_elimination               true
% 2.90/0.97  --inst_learning_loop_flag               true
% 2.90/0.97  --inst_learning_start                   3000
% 2.90/0.97  --inst_learning_factor                  2
% 2.90/0.97  --inst_start_prop_sim_after_learn       3
% 2.90/0.97  --inst_sel_renew                        solver
% 2.90/0.97  --inst_lit_activity_flag                true
% 2.90/0.97  --inst_restr_to_given                   false
% 2.90/0.97  --inst_activity_threshold               500
% 2.90/0.97  --inst_out_proof                        true
% 2.90/0.97  
% 2.90/0.97  ------ Resolution Options
% 2.90/0.97  
% 2.90/0.97  --resolution_flag                       false
% 2.90/0.97  --res_lit_sel                           adaptive
% 2.90/0.97  --res_lit_sel_side                      none
% 2.90/0.97  --res_ordering                          kbo
% 2.90/0.97  --res_to_prop_solver                    active
% 2.90/0.97  --res_prop_simpl_new                    false
% 2.90/0.97  --res_prop_simpl_given                  true
% 2.90/0.97  --res_passive_queue_type                priority_queues
% 2.90/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.90/0.97  --res_passive_queues_freq               [15;5]
% 2.90/0.97  --res_forward_subs                      full
% 2.90/0.97  --res_backward_subs                     full
% 2.90/0.97  --res_forward_subs_resolution           true
% 2.90/0.97  --res_backward_subs_resolution          true
% 2.90/0.97  --res_orphan_elimination                true
% 2.90/0.97  --res_time_limit                        2.
% 2.90/0.97  --res_out_proof                         true
% 2.90/0.97  
% 2.90/0.97  ------ Superposition Options
% 2.90/0.97  
% 2.90/0.97  --superposition_flag                    true
% 2.90/0.97  --sup_passive_queue_type                priority_queues
% 2.90/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.90/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.90/0.97  --demod_completeness_check              fast
% 2.90/0.97  --demod_use_ground                      true
% 2.90/0.97  --sup_to_prop_solver                    passive
% 2.90/0.97  --sup_prop_simpl_new                    true
% 2.90/0.97  --sup_prop_simpl_given                  true
% 2.90/0.97  --sup_fun_splitting                     false
% 2.90/0.97  --sup_smt_interval                      50000
% 2.90/0.97  
% 2.90/0.97  ------ Superposition Simplification Setup
% 2.90/0.97  
% 2.90/0.97  --sup_indices_passive                   []
% 2.90/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.90/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/0.97  --sup_full_bw                           [BwDemod]
% 2.90/0.97  --sup_immed_triv                        [TrivRules]
% 2.90/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.90/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/0.97  --sup_immed_bw_main                     []
% 2.90/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.90/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.90/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.90/0.97  
% 2.90/0.97  ------ Combination Options
% 2.90/0.97  
% 2.90/0.97  --comb_res_mult                         3
% 2.90/0.97  --comb_sup_mult                         2
% 2.90/0.97  --comb_inst_mult                        10
% 2.90/0.97  
% 2.90/0.97  ------ Debug Options
% 2.90/0.97  
% 2.90/0.97  --dbg_backtrace                         false
% 2.90/0.97  --dbg_dump_prop_clauses                 false
% 2.90/0.97  --dbg_dump_prop_clauses_file            -
% 2.90/0.97  --dbg_out_stat                          false
% 2.90/0.97  
% 2.90/0.97  
% 2.90/0.97  
% 2.90/0.97  
% 2.90/0.97  ------ Proving...
% 2.90/0.97  
% 2.90/0.97  
% 2.90/0.97  % SZS status Theorem for theBenchmark.p
% 2.90/0.97  
% 2.90/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.90/0.97  
% 2.90/0.97  fof(f17,conjecture,(
% 2.90/0.97    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.90/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.97  
% 2.90/0.97  fof(f18,negated_conjecture,(
% 2.90/0.97    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.90/0.97    inference(negated_conjecture,[],[f17])).
% 2.90/0.97  
% 2.90/0.97  fof(f44,plain,(
% 2.90/0.97    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.90/0.97    inference(ennf_transformation,[],[f18])).
% 2.90/0.97  
% 2.90/0.97  fof(f45,plain,(
% 2.90/0.97    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.90/0.97    inference(flattening,[],[f44])).
% 2.90/0.97  
% 2.90/0.97  fof(f50,plain,(
% 2.90/0.97    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.90/0.97    introduced(choice_axiom,[])).
% 2.90/0.97  
% 2.90/0.97  fof(f49,plain,(
% 2.90/0.97    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.90/0.97    introduced(choice_axiom,[])).
% 2.90/0.97  
% 2.90/0.97  fof(f48,plain,(
% 2.90/0.97    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.90/0.97    introduced(choice_axiom,[])).
% 2.90/0.97  
% 2.90/0.97  fof(f51,plain,(
% 2.90/0.97    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.90/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f50,f49,f48])).
% 2.90/0.97  
% 2.90/0.97  fof(f88,plain,(
% 2.90/0.97    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.90/0.97    inference(cnf_transformation,[],[f51])).
% 2.90/0.97  
% 2.90/0.97  fof(f14,axiom,(
% 2.90/0.97    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.90/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.97  
% 2.90/0.97  fof(f39,plain,(
% 2.90/0.97    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.90/0.97    inference(ennf_transformation,[],[f14])).
% 2.90/0.97  
% 2.90/0.97  fof(f80,plain,(
% 2.90/0.97    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.90/0.97    inference(cnf_transformation,[],[f39])).
% 2.90/0.97  
% 2.90/0.97  fof(f85,plain,(
% 2.90/0.97    l1_struct_0(sK1)),
% 2.90/0.97    inference(cnf_transformation,[],[f51])).
% 2.90/0.97  
% 2.90/0.97  fof(f83,plain,(
% 2.90/0.97    l1_struct_0(sK0)),
% 2.90/0.97    inference(cnf_transformation,[],[f51])).
% 2.90/0.97  
% 2.90/0.97  fof(f7,axiom,(
% 2.90/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.90/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.97  
% 2.90/0.97  fof(f28,plain,(
% 2.90/0.97    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/0.97    inference(ennf_transformation,[],[f7])).
% 2.90/0.97  
% 2.90/0.97  fof(f62,plain,(
% 2.90/0.97    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.90/0.97    inference(cnf_transformation,[],[f28])).
% 2.90/0.97  
% 2.90/0.97  fof(f89,plain,(
% 2.90/0.97    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.90/0.97    inference(cnf_transformation,[],[f51])).
% 2.90/0.97  
% 2.90/0.97  fof(f10,axiom,(
% 2.90/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.90/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.97  
% 2.90/0.97  fof(f31,plain,(
% 2.90/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/0.97    inference(ennf_transformation,[],[f10])).
% 2.90/0.97  
% 2.90/0.97  fof(f32,plain,(
% 2.90/0.97    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/0.97    inference(flattening,[],[f31])).
% 2.90/0.97  
% 2.90/0.97  fof(f46,plain,(
% 2.90/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/0.97    inference(nnf_transformation,[],[f32])).
% 2.90/0.97  
% 2.90/0.97  fof(f66,plain,(
% 2.90/0.97    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.90/0.97    inference(cnf_transformation,[],[f46])).
% 2.90/0.97  
% 2.90/0.97  fof(f9,axiom,(
% 2.90/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 2.90/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.97  
% 2.90/0.97  fof(f30,plain,(
% 2.90/0.97    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/0.97    inference(ennf_transformation,[],[f9])).
% 2.90/0.97  
% 2.90/0.97  fof(f65,plain,(
% 2.90/0.97    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.90/0.97    inference(cnf_transformation,[],[f30])).
% 2.90/0.97  
% 2.90/0.97  fof(f8,axiom,(
% 2.90/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 2.90/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.97  
% 2.90/0.97  fof(f29,plain,(
% 2.90/0.97    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/0.97    inference(ennf_transformation,[],[f8])).
% 2.90/0.97  
% 2.90/0.97  fof(f63,plain,(
% 2.90/0.97    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.90/0.97    inference(cnf_transformation,[],[f29])).
% 2.90/0.97  
% 2.90/0.97  fof(f87,plain,(
% 2.90/0.97    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.90/0.97    inference(cnf_transformation,[],[f51])).
% 2.90/0.97  
% 2.90/0.97  fof(f1,axiom,(
% 2.90/0.97    v1_xboole_0(k1_xboole_0)),
% 2.90/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.97  
% 2.90/0.97  fof(f52,plain,(
% 2.90/0.97    v1_xboole_0(k1_xboole_0)),
% 2.90/0.97    inference(cnf_transformation,[],[f1])).
% 2.90/0.97  
% 2.90/0.97  fof(f15,axiom,(
% 2.90/0.97    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.90/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.97  
% 2.90/0.97  fof(f40,plain,(
% 2.90/0.97    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.90/0.97    inference(ennf_transformation,[],[f15])).
% 2.90/0.97  
% 2.90/0.97  fof(f41,plain,(
% 2.90/0.97    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.90/0.97    inference(flattening,[],[f40])).
% 2.90/0.97  
% 2.90/0.97  fof(f81,plain,(
% 2.90/0.97    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.90/0.97    inference(cnf_transformation,[],[f41])).
% 2.90/0.97  
% 2.90/0.97  fof(f84,plain,(
% 2.90/0.97    ~v2_struct_0(sK1)),
% 2.90/0.97    inference(cnf_transformation,[],[f51])).
% 2.90/0.97  
% 2.90/0.97  fof(f90,plain,(
% 2.90/0.97    v2_funct_1(sK2)),
% 2.90/0.97    inference(cnf_transformation,[],[f51])).
% 2.90/0.97  
% 2.90/0.97  fof(f4,axiom,(
% 2.90/0.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.90/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.97  
% 2.90/0.97  fof(f23,plain,(
% 2.90/0.97    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.90/0.97    inference(ennf_transformation,[],[f4])).
% 2.90/0.97  
% 2.90/0.97  fof(f24,plain,(
% 2.90/0.97    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.90/0.97    inference(flattening,[],[f23])).
% 2.90/0.97  
% 2.90/0.97  fof(f59,plain,(
% 2.90/0.97    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.90/0.97    inference(cnf_transformation,[],[f24])).
% 2.90/0.97  
% 2.90/0.97  fof(f86,plain,(
% 2.90/0.97    v1_funct_1(sK2)),
% 2.90/0.97    inference(cnf_transformation,[],[f51])).
% 2.90/0.97  
% 2.90/0.97  fof(f6,axiom,(
% 2.90/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.90/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.97  
% 2.90/0.97  fof(f27,plain,(
% 2.90/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/0.97    inference(ennf_transformation,[],[f6])).
% 2.90/0.97  
% 2.90/0.97  fof(f61,plain,(
% 2.90/0.97    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.90/0.97    inference(cnf_transformation,[],[f27])).
% 2.90/0.97  
% 2.90/0.97  fof(f13,axiom,(
% 2.90/0.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.90/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.97  
% 2.90/0.97  fof(f37,plain,(
% 2.90/0.97    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.90/0.97    inference(ennf_transformation,[],[f13])).
% 2.90/0.97  
% 2.90/0.97  fof(f38,plain,(
% 2.90/0.97    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.90/0.97    inference(flattening,[],[f37])).
% 2.90/0.97  
% 2.90/0.97  fof(f79,plain,(
% 2.90/0.97    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.90/0.97    inference(cnf_transformation,[],[f38])).
% 2.90/0.97  
% 2.90/0.97  fof(f58,plain,(
% 2.90/0.97    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.90/0.97    inference(cnf_transformation,[],[f24])).
% 2.90/0.97  
% 2.90/0.97  fof(f78,plain,(
% 2.90/0.97    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.90/0.97    inference(cnf_transformation,[],[f38])).
% 2.90/0.97  
% 2.90/0.97  fof(f12,axiom,(
% 2.90/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.90/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.97  
% 2.90/0.97  fof(f35,plain,(
% 2.90/0.97    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.90/0.97    inference(ennf_transformation,[],[f12])).
% 2.90/0.97  
% 2.90/0.97  fof(f36,plain,(
% 2.90/0.97    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.90/0.97    inference(flattening,[],[f35])).
% 2.90/0.97  
% 2.90/0.97  fof(f76,plain,(
% 2.90/0.97    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.90/0.97    inference(cnf_transformation,[],[f36])).
% 2.90/0.97  
% 2.90/0.97  fof(f5,axiom,(
% 2.90/0.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.90/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.97  
% 2.90/0.97  fof(f25,plain,(
% 2.90/0.97    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.90/0.97    inference(ennf_transformation,[],[f5])).
% 2.90/0.97  
% 2.90/0.97  fof(f26,plain,(
% 2.90/0.97    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.90/0.97    inference(flattening,[],[f25])).
% 2.90/0.97  
% 2.90/0.97  fof(f60,plain,(
% 2.90/0.97    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.90/0.97    inference(cnf_transformation,[],[f26])).
% 2.90/0.97  
% 2.90/0.97  fof(f16,axiom,(
% 2.90/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.90/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.97  
% 2.90/0.97  fof(f42,plain,(
% 2.90/0.97    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.90/0.97    inference(ennf_transformation,[],[f16])).
% 2.90/0.97  
% 2.90/0.97  fof(f43,plain,(
% 2.90/0.97    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.90/0.97    inference(flattening,[],[f42])).
% 2.90/0.97  
% 2.90/0.97  fof(f82,plain,(
% 2.90/0.97    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.90/0.97    inference(cnf_transformation,[],[f43])).
% 2.90/0.97  
% 2.90/0.97  fof(f11,axiom,(
% 2.90/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.90/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.97  
% 2.90/0.97  fof(f33,plain,(
% 2.90/0.97    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.90/0.97    inference(ennf_transformation,[],[f11])).
% 2.90/0.97  
% 2.90/0.97  fof(f34,plain,(
% 2.90/0.97    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.90/0.97    inference(flattening,[],[f33])).
% 2.90/0.97  
% 2.90/0.97  fof(f47,plain,(
% 2.90/0.97    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.90/0.97    inference(nnf_transformation,[],[f34])).
% 2.90/0.97  
% 2.90/0.97  fof(f73,plain,(
% 2.90/0.97    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.90/0.97    inference(cnf_transformation,[],[f47])).
% 2.90/0.97  
% 2.90/0.97  fof(f97,plain,(
% 2.90/0.97    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.90/0.97    inference(equality_resolution,[],[f73])).
% 2.90/0.97  
% 2.90/0.97  fof(f91,plain,(
% 2.90/0.97    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 2.90/0.97    inference(cnf_transformation,[],[f51])).
% 2.90/0.97  
% 2.90/0.97  fof(f3,axiom,(
% 2.90/0.97    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.90/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.97  
% 2.90/0.97  fof(f21,plain,(
% 2.90/0.97    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.90/0.97    inference(ennf_transformation,[],[f3])).
% 2.90/0.97  
% 2.90/0.97  fof(f22,plain,(
% 2.90/0.97    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.90/0.97    inference(flattening,[],[f21])).
% 2.90/0.97  
% 2.90/0.97  fof(f57,plain,(
% 2.90/0.97    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.90/0.97    inference(cnf_transformation,[],[f22])).
% 2.90/0.97  
% 2.90/0.97  fof(f74,plain,(
% 2.90/0.97    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.90/0.97    inference(cnf_transformation,[],[f36])).
% 2.90/0.97  
% 2.90/0.97  fof(f2,axiom,(
% 2.90/0.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.90/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.90/0.97  
% 2.90/0.97  fof(f19,plain,(
% 2.90/0.97    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.90/0.97    inference(ennf_transformation,[],[f2])).
% 2.90/0.97  
% 2.90/0.97  fof(f20,plain,(
% 2.90/0.97    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.90/0.97    inference(flattening,[],[f19])).
% 2.90/0.97  
% 2.90/0.97  fof(f54,plain,(
% 2.90/0.97    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.90/0.97    inference(cnf_transformation,[],[f20])).
% 2.90/0.97  
% 2.90/0.97  fof(f75,plain,(
% 2.90/0.97    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.90/0.97    inference(cnf_transformation,[],[f36])).
% 2.90/0.97  
% 2.90/0.97  cnf(c_34,negated_conjecture,
% 2.90/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.90/0.97      inference(cnf_transformation,[],[f88]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_1198,plain,
% 2.90/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.90/0.97      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_28,plain,
% 2.90/0.97      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.90/0.97      inference(cnf_transformation,[],[f80]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_37,negated_conjecture,
% 2.90/0.97      ( l1_struct_0(sK1) ),
% 2.90/0.97      inference(cnf_transformation,[],[f85]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_466,plain,
% 2.90/0.97      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.90/0.97      inference(resolution_lifted,[status(thm)],[c_28,c_37]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_467,plain,
% 2.90/0.97      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.90/0.97      inference(unflattening,[status(thm)],[c_466]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_39,negated_conjecture,
% 2.90/0.97      ( l1_struct_0(sK0) ),
% 2.90/0.97      inference(cnf_transformation,[],[f83]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_471,plain,
% 2.90/0.97      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.90/0.97      inference(resolution_lifted,[status(thm)],[c_28,c_39]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_472,plain,
% 2.90/0.97      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.90/0.97      inference(unflattening,[status(thm)],[c_471]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_1239,plain,
% 2.90/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.90/0.97      inference(light_normalisation,[status(thm)],[c_1198,c_467,c_472]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_10,plain,
% 2.90/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/0.97      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.90/0.97      inference(cnf_transformation,[],[f62]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_1214,plain,
% 2.90/0.97      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.90/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.90/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_1645,plain,
% 2.90/0.97      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.90/0.97      inference(superposition,[status(thm)],[c_1239,c_1214]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_33,negated_conjecture,
% 2.90/0.97      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.90/0.97      inference(cnf_transformation,[],[f89]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_1236,plain,
% 2.90/0.97      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.90/0.97      inference(light_normalisation,[status(thm)],[c_33,c_467,c_472]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_1858,plain,
% 2.90/0.97      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.90/0.97      inference(demodulation,[status(thm)],[c_1645,c_1236]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_1960,plain,
% 2.90/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.90/0.97      inference(demodulation,[status(thm)],[c_1858,c_1239]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_19,plain,
% 2.90/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 2.90/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/0.97      | k1_relset_1(X1,X2,X0) = X1
% 2.90/0.97      | k1_xboole_0 = X2 ),
% 2.90/0.97      inference(cnf_transformation,[],[f66]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_1205,plain,
% 2.90/0.97      ( k1_relset_1(X0,X1,X2) = X0
% 2.90/0.97      | k1_xboole_0 = X1
% 2.90/0.97      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.90/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.90/0.97      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_4216,plain,
% 2.90/0.97      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0)
% 2.90/0.97      | k2_relat_1(sK2) = k1_xboole_0
% 2.90/0.97      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
% 2.90/0.97      inference(superposition,[status(thm)],[c_1960,c_1205]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_12,plain,
% 2.90/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/0.97      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 2.90/0.97      inference(cnf_transformation,[],[f65]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_1212,plain,
% 2.90/0.97      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 2.90/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.90/0.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_2742,plain,
% 2.90/0.97      ( k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
% 2.90/0.97      inference(superposition,[status(thm)],[c_1960,c_1212]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_11,plain,
% 2.90/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/0.97      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.90/0.97      inference(cnf_transformation,[],[f63]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_1213,plain,
% 2.90/0.97      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 2.90/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.90/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_2476,plain,
% 2.90/0.97      ( k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0) ),
% 2.90/0.97      inference(superposition,[status(thm)],[c_1960,c_1213]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_2743,plain,
% 2.90/0.97      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
% 2.90/0.97      inference(demodulation,[status(thm)],[c_2742,c_2476]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_4220,plain,
% 2.90/0.97      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k2_struct_0(sK0)
% 2.90/0.97      | k2_relat_1(sK2) = k1_xboole_0
% 2.90/0.97      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
% 2.90/0.97      inference(demodulation,[status(thm)],[c_4216,c_2743]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_35,negated_conjecture,
% 2.90/0.97      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.90/0.97      inference(cnf_transformation,[],[f87]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_1197,plain,
% 2.90/0.97      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.90/0.97      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_1233,plain,
% 2.90/0.97      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.90/0.97      inference(light_normalisation,[status(thm)],[c_1197,c_467,c_472]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_1961,plain,
% 2.90/0.97      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.90/0.97      inference(demodulation,[status(thm)],[c_1858,c_1233]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_0,plain,
% 2.90/0.97      ( v1_xboole_0(k1_xboole_0) ),
% 2.90/0.97      inference(cnf_transformation,[],[f52]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_29,plain,
% 2.90/0.97      ( v2_struct_0(X0)
% 2.90/0.97      | ~ l1_struct_0(X0)
% 2.90/0.97      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.90/0.97      inference(cnf_transformation,[],[f81]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_439,plain,
% 2.90/0.97      ( v2_struct_0(X0)
% 2.90/0.97      | ~ l1_struct_0(X0)
% 2.90/0.97      | u1_struct_0(X0) != k1_xboole_0 ),
% 2.90/0.97      inference(resolution_lifted,[status(thm)],[c_0,c_29]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_38,negated_conjecture,
% 2.90/0.97      ( ~ v2_struct_0(sK1) ),
% 2.90/0.97      inference(cnf_transformation,[],[f84]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_457,plain,
% 2.90/0.97      ( ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 2.90/0.97      inference(resolution_lifted,[status(thm)],[c_439,c_38]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_458,plain,
% 2.90/0.97      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.90/0.97      inference(unflattening,[status(thm)],[c_457]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_460,plain,
% 2.90/0.97      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 2.90/0.97      inference(global_propositional_subsumption,
% 2.90/0.97                [status(thm)],
% 2.90/0.97                [c_458,c_37]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_1230,plain,
% 2.90/0.97      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 2.90/0.97      inference(light_normalisation,[status(thm)],[c_460,c_467]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_1962,plain,
% 2.90/0.97      ( k2_relat_1(sK2) != k1_xboole_0 ),
% 2.90/0.97      inference(demodulation,[status(thm)],[c_1858,c_1230]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_7236,plain,
% 2.90/0.97      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k2_struct_0(sK0) ),
% 2.90/0.97      inference(global_propositional_subsumption,
% 2.90/0.97                [status(thm)],
% 2.90/0.97                [c_4220,c_1961,c_1962]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_32,negated_conjecture,
% 2.90/0.97      ( v2_funct_1(sK2) ),
% 2.90/0.97      inference(cnf_transformation,[],[f90]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_1199,plain,
% 2.90/0.97      ( v2_funct_1(sK2) = iProver_top ),
% 2.90/0.97      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.90/0.97  
% 2.90/0.97  cnf(c_6,plain,
% 2.90/0.97      ( ~ v2_funct_1(X0)
% 2.90/0.98      | ~ v1_relat_1(X0)
% 2.90/0.98      | ~ v1_funct_1(X0)
% 2.90/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.90/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1218,plain,
% 2.90/0.98      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.90/0.98      | v2_funct_1(X0) != iProver_top
% 2.90/0.98      | v1_relat_1(X0) != iProver_top
% 2.90/0.98      | v1_funct_1(X0) != iProver_top ),
% 2.90/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_3945,plain,
% 2.90/0.98      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.90/0.98      | v1_relat_1(sK2) != iProver_top
% 2.90/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.90/0.98      inference(superposition,[status(thm)],[c_1199,c_1218]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_36,negated_conjecture,
% 2.90/0.98      ( v1_funct_1(sK2) ),
% 2.90/0.98      inference(cnf_transformation,[],[f86]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_9,plain,
% 2.90/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/0.98      | v1_relat_1(X0) ),
% 2.90/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1479,plain,
% 2.90/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.90/0.98      | v1_relat_1(sK2) ),
% 2.90/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1494,plain,
% 2.90/0.98      ( ~ v2_funct_1(sK2)
% 2.90/0.98      | ~ v1_relat_1(sK2)
% 2.90/0.98      | ~ v1_funct_1(sK2)
% 2.90/0.98      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.90/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_4351,plain,
% 2.90/0.98      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.90/0.98      inference(global_propositional_subsumption,
% 2.90/0.98                [status(thm)],
% 2.90/0.98                [c_3945,c_36,c_34,c_32,c_1479,c_1494]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_25,plain,
% 2.90/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.90/0.98      | ~ v1_relat_1(X0)
% 2.90/0.98      | ~ v1_funct_1(X0) ),
% 2.90/0.98      inference(cnf_transformation,[],[f79]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1202,plain,
% 2.90/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 2.90/0.98      | v1_relat_1(X0) != iProver_top
% 2.90/0.98      | v1_funct_1(X0) != iProver_top ),
% 2.90/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_4354,plain,
% 2.90/0.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 2.90/0.98      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 2.90/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.90/0.98      inference(superposition,[status(thm)],[c_4351,c_1202]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_7,plain,
% 2.90/0.98      ( ~ v2_funct_1(X0)
% 2.90/0.98      | ~ v1_relat_1(X0)
% 2.90/0.98      | ~ v1_funct_1(X0)
% 2.90/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.90/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1217,plain,
% 2.90/0.98      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.90/0.98      | v2_funct_1(X0) != iProver_top
% 2.90/0.98      | v1_relat_1(X0) != iProver_top
% 2.90/0.98      | v1_funct_1(X0) != iProver_top ),
% 2.90/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_3720,plain,
% 2.90/0.98      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.90/0.98      | v1_relat_1(sK2) != iProver_top
% 2.90/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.90/0.98      inference(superposition,[status(thm)],[c_1199,c_1217]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1497,plain,
% 2.90/0.98      ( ~ v2_funct_1(sK2)
% 2.90/0.98      | ~ v1_relat_1(sK2)
% 2.90/0.98      | ~ v1_funct_1(sK2)
% 2.90/0.98      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.90/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_4331,plain,
% 2.90/0.98      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.90/0.98      inference(global_propositional_subsumption,
% 2.90/0.98                [status(thm)],
% 2.90/0.98                [c_3720,c_36,c_34,c_32,c_1479,c_1497]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_4366,plain,
% 2.90/0.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 2.90/0.98      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 2.90/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.90/0.98      inference(light_normalisation,[status(thm)],[c_4354,c_4331]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_43,plain,
% 2.90/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 2.90/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_45,plain,
% 2.90/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.90/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_46,plain,
% 2.90/0.98      ( v2_funct_1(sK2) = iProver_top ),
% 2.90/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1480,plain,
% 2.90/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.90/0.98      | v1_relat_1(sK2) = iProver_top ),
% 2.90/0.98      inference(predicate_to_equality,[status(thm)],[c_1479]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_26,plain,
% 2.90/0.98      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.90/0.98      | ~ v1_relat_1(X0)
% 2.90/0.98      | ~ v1_funct_1(X0) ),
% 2.90/0.98      inference(cnf_transformation,[],[f78]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1598,plain,
% 2.90/0.98      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
% 2.90/0.98      | ~ v1_relat_1(sK2)
% 2.90/0.98      | ~ v1_funct_1(sK2) ),
% 2.90/0.98      inference(instantiation,[status(thm)],[c_26]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1610,plain,
% 2.90/0.98      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top
% 2.90/0.98      | v1_relat_1(sK2) != iProver_top
% 2.90/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.90/0.98      inference(predicate_to_equality,[status(thm)],[c_1598]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1597,plain,
% 2.90/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 2.90/0.98      | ~ v1_relat_1(sK2)
% 2.90/0.98      | ~ v1_funct_1(sK2) ),
% 2.90/0.98      inference(instantiation,[status(thm)],[c_25]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1612,plain,
% 2.90/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
% 2.90/0.98      | v1_relat_1(sK2) != iProver_top
% 2.90/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.90/0.98      inference(predicate_to_equality,[status(thm)],[c_1597]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1798,plain,
% 2.90/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 2.90/0.98      | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.90/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_22,plain,
% 2.90/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.90/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/0.98      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.90/0.98      | ~ v2_funct_1(X0)
% 2.90/0.98      | ~ v1_funct_1(X0)
% 2.90/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.90/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1539,plain,
% 2.90/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 2.90/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.90/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.90/0.98      | ~ v2_funct_1(sK2)
% 2.90/0.98      | ~ v1_funct_1(sK2)
% 2.90/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.90/0.98      inference(instantiation,[status(thm)],[c_22]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1823,plain,
% 2.90/0.98      ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
% 2.90/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
% 2.90/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 2.90/0.98      | ~ v2_funct_1(sK2)
% 2.90/0.98      | ~ v1_funct_1(sK2)
% 2.90/0.98      | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2) ),
% 2.90/0.98      inference(instantiation,[status(thm)],[c_1539]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1824,plain,
% 2.90/0.98      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
% 2.90/0.98      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.90/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 2.90/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.90/0.98      | v2_funct_1(sK2) != iProver_top
% 2.90/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.90/0.98      inference(predicate_to_equality,[status(thm)],[c_1823]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_4429,plain,
% 2.90/0.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 2.90/0.98      inference(global_propositional_subsumption,
% 2.90/0.98                [status(thm)],
% 2.90/0.98                [c_4366,c_36,c_43,c_34,c_45,c_46,c_1479,c_1480,c_1610,
% 2.90/0.98                 c_1597,c_1612,c_1798,c_1824]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_4440,plain,
% 2.90/0.98      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.90/0.98      inference(superposition,[status(thm)],[c_4429,c_1214]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_4442,plain,
% 2.90/0.98      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.90/0.98      inference(light_normalisation,[status(thm)],[c_4440,c_4351]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1204,plain,
% 2.90/0.98      ( k2_relset_1(X0,X1,X2) != X1
% 2.90/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.90/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.90/0.98      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 2.90/0.98      | v2_funct_1(X2) != iProver_top
% 2.90/0.98      | v1_funct_1(X2) != iProver_top ),
% 2.90/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_4655,plain,
% 2.90/0.98      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.90/0.98      | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
% 2.90/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.90/0.98      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.90/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.90/0.98      inference(superposition,[status(thm)],[c_4442,c_1204]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_8,plain,
% 2.90/0.98      ( ~ v2_funct_1(X0)
% 2.90/0.98      | ~ v1_relat_1(X0)
% 2.90/0.98      | ~ v1_funct_1(X0)
% 2.90/0.98      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.90/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1216,plain,
% 2.90/0.98      ( k2_funct_1(k2_funct_1(X0)) = X0
% 2.90/0.98      | v2_funct_1(X0) != iProver_top
% 2.90/0.98      | v1_relat_1(X0) != iProver_top
% 2.90/0.98      | v1_funct_1(X0) != iProver_top ),
% 2.90/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_3008,plain,
% 2.90/0.98      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.90/0.98      | v1_relat_1(sK2) != iProver_top
% 2.90/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.90/0.98      inference(superposition,[status(thm)],[c_1199,c_1216]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1500,plain,
% 2.90/0.98      ( ~ v2_funct_1(sK2)
% 2.90/0.98      | ~ v1_relat_1(sK2)
% 2.90/0.98      | ~ v1_funct_1(sK2)
% 2.90/0.98      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.90/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_3243,plain,
% 2.90/0.98      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.90/0.98      inference(global_propositional_subsumption,
% 2.90/0.98                [status(thm)],
% 2.90/0.98                [c_3008,c_36,c_34,c_32,c_1479,c_1500]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_4661,plain,
% 2.90/0.98      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.90/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.90/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
% 2.90/0.98      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.90/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.90/0.98      inference(light_normalisation,[status(thm)],[c_4655,c_3243]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_5207,plain,
% 2.90/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 2.90/0.98      inference(global_propositional_subsumption,
% 2.90/0.98                [status(thm)],
% 2.90/0.98                [c_4661,c_43,c_45,c_1480,c_1612]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_5215,plain,
% 2.90/0.98      ( k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
% 2.90/0.98      inference(superposition,[status(thm)],[c_5207,c_1212]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1215,plain,
% 2.90/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.90/0.98      | v1_relat_1(X0) = iProver_top ),
% 2.90/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1563,plain,
% 2.90/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 2.90/0.98      inference(superposition,[status(thm)],[c_1239,c_1215]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_2965,plain,
% 2.90/0.98      ( k8_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0,X1) = k10_relat_1(X0,X1)
% 2.90/0.98      | v1_relat_1(X0) != iProver_top
% 2.90/0.98      | v1_funct_1(X0) != iProver_top ),
% 2.90/0.98      inference(superposition,[status(thm)],[c_1202,c_1213]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_3574,plain,
% 2.90/0.98      ( k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0)
% 2.90/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.90/0.98      inference(superposition,[status(thm)],[c_1563,c_2965]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1797,plain,
% 2.90/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 2.90/0.98      | k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0) ),
% 2.90/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_3594,plain,
% 2.90/0.98      ( k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0) ),
% 2.90/0.98      inference(global_propositional_subsumption,
% 2.90/0.98                [status(thm)],
% 2.90/0.98                [c_3574,c_36,c_34,c_1479,c_1597,c_1797]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_5223,plain,
% 2.90/0.98      ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
% 2.90/0.98      inference(demodulation,[status(thm)],[c_5215,c_3594]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_4215,plain,
% 2.90/0.98      ( k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
% 2.90/0.98      | k2_relat_1(X0) = k1_xboole_0
% 2.90/0.98      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) != iProver_top
% 2.90/0.98      | v1_relat_1(X0) != iProver_top
% 2.90/0.98      | v1_funct_1(X0) != iProver_top ),
% 2.90/0.98      inference(superposition,[status(thm)],[c_1202,c_1205]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_58,plain,
% 2.90/0.98      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
% 2.90/0.98      | v1_relat_1(X0) != iProver_top
% 2.90/0.98      | v1_funct_1(X0) != iProver_top ),
% 2.90/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_5690,plain,
% 2.90/0.98      ( k2_relat_1(X0) = k1_xboole_0
% 2.90/0.98      | k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
% 2.90/0.98      | v1_relat_1(X0) != iProver_top
% 2.90/0.98      | v1_funct_1(X0) != iProver_top ),
% 2.90/0.98      inference(global_propositional_subsumption,
% 2.90/0.98                [status(thm)],
% 2.90/0.98                [c_4215,c_58]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_5691,plain,
% 2.90/0.98      ( k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
% 2.90/0.98      | k2_relat_1(X0) = k1_xboole_0
% 2.90/0.98      | v1_relat_1(X0) != iProver_top
% 2.90/0.98      | v1_funct_1(X0) != iProver_top ),
% 2.90/0.98      inference(renaming,[status(thm)],[c_5690]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_5701,plain,
% 2.90/0.98      ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k1_relat_1(sK2)
% 2.90/0.98      | k2_relat_1(sK2) = k1_xboole_0
% 2.90/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.90/0.98      inference(superposition,[status(thm)],[c_1563,c_5691]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_5935,plain,
% 2.90/0.98      ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k1_relat_1(sK2) ),
% 2.90/0.98      inference(global_propositional_subsumption,
% 2.90/0.98                [status(thm)],
% 2.90/0.98                [c_5701,c_43,c_1962]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_6230,plain,
% 2.90/0.98      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.90/0.98      inference(light_normalisation,[status(thm)],[c_5223,c_5935]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_7238,plain,
% 2.90/0.98      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.90/0.98      inference(light_normalisation,[status(thm)],[c_7236,c_6230]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1958,plain,
% 2.90/0.98      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.90/0.98      inference(demodulation,[status(thm)],[c_1858,c_1645]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_30,plain,
% 2.90/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.90/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/0.98      | ~ v2_funct_1(X0)
% 2.90/0.98      | ~ v1_funct_1(X0)
% 2.90/0.98      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.90/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.90/0.98      inference(cnf_transformation,[],[f82]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1200,plain,
% 2.90/0.98      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
% 2.90/0.98      | k2_relset_1(X0,X1,X2) != X1
% 2.90/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.90/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.90/0.98      | v2_funct_1(X2) != iProver_top
% 2.90/0.98      | v1_funct_1(X2) != iProver_top ),
% 2.90/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_2151,plain,
% 2.90/0.98      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 2.90/0.98      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.90/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.90/0.98      | v2_funct_1(sK2) != iProver_top
% 2.90/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.90/0.98      inference(superposition,[status(thm)],[c_1958,c_1200]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_2632,plain,
% 2.90/0.98      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.90/0.98      inference(global_propositional_subsumption,
% 2.90/0.98                [status(thm)],
% 2.90/0.98                [c_2151,c_43,c_46,c_1960,c_1961]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_20,plain,
% 2.90/0.98      ( r2_funct_2(X0,X1,X2,X2)
% 2.90/0.98      | ~ v1_funct_2(X2,X0,X1)
% 2.90/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.90/0.98      | ~ v1_funct_1(X2) ),
% 2.90/0.98      inference(cnf_transformation,[],[f97]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_31,negated_conjecture,
% 2.90/0.98      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 2.90/0.98      inference(cnf_transformation,[],[f91]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_480,plain,
% 2.90/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.90/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/0.98      | ~ v1_funct_1(X0)
% 2.90/0.98      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 2.90/0.98      | u1_struct_0(sK1) != X2
% 2.90/0.98      | u1_struct_0(sK0) != X1
% 2.90/0.98      | sK2 != X0 ),
% 2.90/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_31]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_481,plain,
% 2.90/0.98      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.90/0.98      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.90/0.98      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.90/0.98      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.90/0.98      inference(unflattening,[status(thm)],[c_480]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1194,plain,
% 2.90/0.98      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.90/0.98      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.90/0.98      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.90/0.98      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 2.90/0.98      inference(predicate_to_equality,[status(thm)],[c_481]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1402,plain,
% 2.90/0.98      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.90/0.98      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.90/0.98      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.90/0.98      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.90/0.98      inference(light_normalisation,[status(thm)],[c_1194,c_467,c_472]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1959,plain,
% 2.90/0.98      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
% 2.90/0.98      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.90/0.98      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.90/0.98      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
% 2.90/0.98      inference(demodulation,[status(thm)],[c_1858,c_1402]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_2635,plain,
% 2.90/0.98      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 2.90/0.98      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.90/0.98      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.90/0.98      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 2.90/0.98      inference(demodulation,[status(thm)],[c_2632,c_1959]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_7246,plain,
% 2.90/0.98      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 2.90/0.98      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.90/0.98      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.90/0.98      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 2.90/0.98      inference(demodulation,[status(thm)],[c_7238,c_2635]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_4469,plain,
% 2.90/0.98      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.90/0.98      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.90/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.90/0.98      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.90/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.90/0.98      inference(superposition,[status(thm)],[c_4442,c_1200]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_4475,plain,
% 2.90/0.98      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 2.90/0.98      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.90/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.90/0.98      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.90/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.90/0.98      inference(light_normalisation,[status(thm)],[c_4469,c_3243]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_3,plain,
% 2.90/0.98      ( ~ v2_funct_1(X0)
% 2.90/0.98      | v2_funct_1(k2_funct_1(X0))
% 2.90/0.98      | ~ v1_relat_1(X0)
% 2.90/0.98      | ~ v1_funct_1(X0) ),
% 2.90/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1476,plain,
% 2.90/0.98      ( v2_funct_1(k2_funct_1(sK2))
% 2.90/0.98      | ~ v2_funct_1(sK2)
% 2.90/0.98      | ~ v1_relat_1(sK2)
% 2.90/0.98      | ~ v1_funct_1(sK2) ),
% 2.90/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1477,plain,
% 2.90/0.98      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.90/0.98      | v2_funct_1(sK2) != iProver_top
% 2.90/0.98      | v1_relat_1(sK2) != iProver_top
% 2.90/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.90/0.98      inference(predicate_to_equality,[status(thm)],[c_1476]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_24,plain,
% 2.90/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.90/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/0.98      | ~ v2_funct_1(X0)
% 2.90/0.98      | ~ v1_funct_1(X0)
% 2.90/0.98      | v1_funct_1(k2_funct_1(X0))
% 2.90/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.90/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1,plain,
% 2.90/0.98      ( ~ v1_relat_1(X0)
% 2.90/0.98      | ~ v1_funct_1(X0)
% 2.90/0.98      | v1_funct_1(k2_funct_1(X0)) ),
% 2.90/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_229,plain,
% 2.90/0.98      ( v1_funct_1(k2_funct_1(X0))
% 2.90/0.98      | ~ v1_funct_1(X0)
% 2.90/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.90/0.98      inference(global_propositional_subsumption,
% 2.90/0.98                [status(thm)],
% 2.90/0.98                [c_24,c_9,c_1]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_230,plain,
% 2.90/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/0.98      | ~ v1_funct_1(X0)
% 2.90/0.98      | v1_funct_1(k2_funct_1(X0)) ),
% 2.90/0.98      inference(renaming,[status(thm)],[c_229]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1195,plain,
% 2.90/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.90/0.98      | v1_funct_1(X0) != iProver_top
% 2.90/0.98      | v1_funct_1(k2_funct_1(X0)) = iProver_top ),
% 2.90/0.98      inference(predicate_to_equality,[status(thm)],[c_230]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1558,plain,
% 2.90/0.98      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.90/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.90/0.98      inference(superposition,[status(thm)],[c_1239,c_1195]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_23,plain,
% 2.90/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.90/0.98      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.90/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/0.98      | ~ v2_funct_1(X0)
% 2.90/0.98      | ~ v1_funct_1(X0)
% 2.90/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.90/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1544,plain,
% 2.90/0.98      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 2.90/0.98      | ~ v1_funct_2(sK2,X1,X0)
% 2.90/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.90/0.98      | ~ v2_funct_1(sK2)
% 2.90/0.98      | ~ v1_funct_1(sK2)
% 2.90/0.98      | k2_relset_1(X1,X0,sK2) != X0 ),
% 2.90/0.98      inference(instantiation,[status(thm)],[c_23]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1828,plain,
% 2.90/0.98      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
% 2.90/0.98      | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
% 2.90/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 2.90/0.98      | ~ v2_funct_1(sK2)
% 2.90/0.98      | ~ v1_funct_1(sK2)
% 2.90/0.98      | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2) ),
% 2.90/0.98      inference(instantiation,[status(thm)],[c_1544]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_1829,plain,
% 2.90/0.98      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
% 2.90/0.98      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 2.90/0.98      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.90/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.90/0.98      | v2_funct_1(sK2) != iProver_top
% 2.90/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.90/0.98      inference(predicate_to_equality,[status(thm)],[c_1828]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_5174,plain,
% 2.90/0.98      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 2.90/0.98      inference(global_propositional_subsumption,
% 2.90/0.98                [status(thm)],
% 2.90/0.98                [c_4475,c_36,c_43,c_34,c_45,c_46,c_1477,c_1479,c_1480,
% 2.90/0.98                 c_1558,c_1610,c_1597,c_1612,c_1798,c_1824,c_1829]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_7260,plain,
% 2.90/0.98      ( sK2 != sK2
% 2.90/0.98      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.90/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.90/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.90/0.98      inference(light_normalisation,[status(thm)],[c_7246,c_5174]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(c_7261,plain,
% 2.90/0.98      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.90/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.90/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.90/0.98      inference(equality_resolution_simp,[status(thm)],[c_7260]) ).
% 2.90/0.98  
% 2.90/0.98  cnf(contradiction,plain,
% 2.90/0.98      ( $false ),
% 2.90/0.98      inference(minisat,
% 2.90/0.98                [status(thm)],
% 2.90/0.98                [c_7261,c_1612,c_1610,c_1480,c_45,c_43]) ).
% 2.90/0.98  
% 2.90/0.98  
% 2.90/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.90/0.98  
% 2.90/0.98  ------                               Statistics
% 2.90/0.98  
% 2.90/0.98  ------ General
% 2.90/0.98  
% 2.90/0.98  abstr_ref_over_cycles:                  0
% 2.90/0.98  abstr_ref_under_cycles:                 0
% 2.90/0.98  gc_basic_clause_elim:                   0
% 2.90/0.98  forced_gc_time:                         0
% 2.90/0.98  parsing_time:                           0.01
% 2.90/0.98  unif_index_cands_time:                  0.
% 2.90/0.98  unif_index_add_time:                    0.
% 2.90/0.98  orderings_time:                         0.
% 2.90/0.98  out_proof_time:                         0.012
% 2.90/0.98  total_time:                             0.221
% 2.90/0.98  num_of_symbols:                         57
% 2.90/0.98  num_of_terms:                           6193
% 2.90/0.98  
% 2.90/0.98  ------ Preprocessing
% 2.90/0.98  
% 2.90/0.98  num_of_splits:                          0
% 2.90/0.98  num_of_split_atoms:                     0
% 2.90/0.98  num_of_reused_defs:                     0
% 2.90/0.98  num_eq_ax_congr_red:                    36
% 2.90/0.98  num_of_sem_filtered_clauses:            1
% 2.90/0.98  num_of_subtypes:                        0
% 2.90/0.98  monotx_restored_types:                  0
% 2.90/0.98  sat_num_of_epr_types:                   0
% 2.90/0.98  sat_num_of_non_cyclic_types:            0
% 2.90/0.98  sat_guarded_non_collapsed_types:        0
% 2.90/0.98  num_pure_diseq_elim:                    0
% 2.90/0.98  simp_replaced_by:                       0
% 2.90/0.98  res_preprocessed:                       168
% 2.90/0.98  prep_upred:                             0
% 2.90/0.98  prep_unflattend:                        10
% 2.90/0.98  smt_new_axioms:                         0
% 2.90/0.98  pred_elim_cands:                        5
% 2.90/0.98  pred_elim:                              4
% 2.90/0.98  pred_elim_cl:                           5
% 2.90/0.98  pred_elim_cycles:                       6
% 2.90/0.98  merged_defs:                            0
% 2.90/0.98  merged_defs_ncl:                        0
% 2.90/0.98  bin_hyper_res:                          0
% 2.90/0.98  prep_cycles:                            4
% 2.90/0.98  pred_elim_time:                         0.002
% 2.90/0.98  splitting_time:                         0.
% 2.90/0.98  sem_filter_time:                        0.
% 2.90/0.98  monotx_time:                            0.
% 2.90/0.98  subtype_inf_time:                       0.
% 2.90/0.98  
% 2.90/0.98  ------ Problem properties
% 2.90/0.98  
% 2.90/0.98  clauses:                                32
% 2.90/0.98  conjectures:                            5
% 2.90/0.98  epr:                                    2
% 2.90/0.98  horn:                                   28
% 2.90/0.98  ground:                                 9
% 2.90/0.98  unary:                                  8
% 2.90/0.98  binary:                                 5
% 2.90/0.98  lits:                                   92
% 2.90/0.98  lits_eq:                                25
% 2.90/0.98  fd_pure:                                0
% 2.90/0.98  fd_pseudo:                              0
% 2.90/0.98  fd_cond:                                3
% 2.90/0.98  fd_pseudo_cond:                         0
% 2.90/0.98  ac_symbols:                             0
% 2.90/0.98  
% 2.90/0.98  ------ Propositional Solver
% 2.90/0.98  
% 2.90/0.98  prop_solver_calls:                      29
% 2.90/0.98  prop_fast_solver_calls:                 1301
% 2.90/0.98  smt_solver_calls:                       0
% 2.90/0.98  smt_fast_solver_calls:                  0
% 2.90/0.98  prop_num_of_clauses:                    2421
% 2.90/0.98  prop_preprocess_simplified:             8088
% 2.90/0.98  prop_fo_subsumed:                       72
% 2.90/0.98  prop_solver_time:                       0.
% 2.90/0.98  smt_solver_time:                        0.
% 2.90/0.98  smt_fast_solver_time:                   0.
% 2.90/0.98  prop_fast_solver_time:                  0.
% 2.90/0.98  prop_unsat_core_time:                   0.
% 2.90/0.98  
% 2.90/0.98  ------ QBF
% 2.90/0.98  
% 2.90/0.98  qbf_q_res:                              0
% 2.90/0.98  qbf_num_tautologies:                    0
% 2.90/0.98  qbf_prep_cycles:                        0
% 2.90/0.98  
% 2.90/0.98  ------ BMC1
% 2.90/0.98  
% 2.90/0.98  bmc1_current_bound:                     -1
% 2.90/0.98  bmc1_last_solved_bound:                 -1
% 2.90/0.98  bmc1_unsat_core_size:                   -1
% 2.90/0.98  bmc1_unsat_core_parents_size:           -1
% 2.90/0.98  bmc1_merge_next_fun:                    0
% 2.90/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.90/0.98  
% 2.90/0.98  ------ Instantiation
% 2.90/0.98  
% 2.90/0.98  inst_num_of_clauses:                    871
% 2.90/0.98  inst_num_in_passive:                    440
% 2.90/0.98  inst_num_in_active:                     432
% 2.90/0.98  inst_num_in_unprocessed:                0
% 2.90/0.98  inst_num_of_loops:                      440
% 2.90/0.98  inst_num_of_learning_restarts:          0
% 2.90/0.98  inst_num_moves_active_passive:          5
% 2.90/0.98  inst_lit_activity:                      0
% 2.90/0.98  inst_lit_activity_moves:                0
% 2.90/0.98  inst_num_tautologies:                   0
% 2.90/0.98  inst_num_prop_implied:                  0
% 2.90/0.98  inst_num_existing_simplified:           0
% 2.90/0.98  inst_num_eq_res_simplified:             0
% 2.90/0.98  inst_num_child_elim:                    0
% 2.90/0.98  inst_num_of_dismatching_blockings:      99
% 2.90/0.98  inst_num_of_non_proper_insts:           572
% 2.90/0.98  inst_num_of_duplicates:                 0
% 2.90/0.98  inst_inst_num_from_inst_to_res:         0
% 2.90/0.98  inst_dismatching_checking_time:         0.
% 2.90/0.98  
% 2.90/0.98  ------ Resolution
% 2.90/0.98  
% 2.90/0.98  res_num_of_clauses:                     0
% 2.90/0.98  res_num_in_passive:                     0
% 2.90/0.98  res_num_in_active:                      0
% 2.90/0.98  res_num_of_loops:                       172
% 2.90/0.98  res_forward_subset_subsumed:            35
% 2.90/0.98  res_backward_subset_subsumed:           6
% 2.90/0.98  res_forward_subsumed:                   0
% 2.90/0.98  res_backward_subsumed:                  0
% 2.90/0.98  res_forward_subsumption_resolution:     0
% 2.90/0.98  res_backward_subsumption_resolution:    0
% 2.90/0.98  res_clause_to_clause_subsumption:       217
% 2.90/0.98  res_orphan_elimination:                 0
% 2.90/0.98  res_tautology_del:                      58
% 2.90/0.98  res_num_eq_res_simplified:              0
% 2.90/0.98  res_num_sel_changes:                    0
% 2.90/0.98  res_moves_from_active_to_pass:          0
% 2.90/0.98  
% 2.90/0.98  ------ Superposition
% 2.90/0.98  
% 2.90/0.98  sup_time_total:                         0.
% 2.90/0.98  sup_time_generating:                    0.
% 2.90/0.98  sup_time_sim_full:                      0.
% 2.90/0.98  sup_time_sim_immed:                     0.
% 2.90/0.98  
% 2.90/0.98  sup_num_of_clauses:                     78
% 2.90/0.98  sup_num_in_active:                      64
% 2.90/0.98  sup_num_in_passive:                     14
% 2.90/0.98  sup_num_of_loops:                       87
% 2.90/0.98  sup_fw_superposition:                   53
% 2.90/0.98  sup_bw_superposition:                   52
% 2.90/0.98  sup_immediate_simplified:               56
% 2.90/0.98  sup_given_eliminated:                   0
% 2.90/0.98  comparisons_done:                       0
% 2.90/0.98  comparisons_avoided:                    12
% 2.90/0.98  
% 2.90/0.98  ------ Simplifications
% 2.90/0.98  
% 2.90/0.98  
% 2.90/0.98  sim_fw_subset_subsumed:                 12
% 2.90/0.98  sim_bw_subset_subsumed:                 5
% 2.90/0.98  sim_fw_subsumed:                        4
% 2.90/0.98  sim_bw_subsumed:                        0
% 2.90/0.98  sim_fw_subsumption_res:                 0
% 2.90/0.98  sim_bw_subsumption_res:                 0
% 2.90/0.98  sim_tautology_del:                      1
% 2.90/0.98  sim_eq_tautology_del:                   13
% 2.90/0.98  sim_eq_res_simp:                        2
% 2.90/0.98  sim_fw_demodulated:                     12
% 2.90/0.98  sim_bw_demodulated:                     23
% 2.90/0.98  sim_light_normalised:                   44
% 2.90/0.98  sim_joinable_taut:                      0
% 2.90/0.98  sim_joinable_simp:                      0
% 2.90/0.98  sim_ac_normalised:                      0
% 2.90/0.98  sim_smt_subsumption:                    0
% 2.90/0.98  
%------------------------------------------------------------------------------
