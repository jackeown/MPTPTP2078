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
% DateTime   : Thu Dec  3 12:17:42 EST 2020

% Result     : Theorem 1.42s
% Output     : CNFRefutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  220 (2425 expanded)
%              Number of clauses        :  140 ( 696 expanded)
%              Number of leaves         :   20 ( 704 expanded)
%              Depth                    :   29
%              Number of atoms          :  758 (15598 expanded)
%              Number of equality atoms :  329 (2633 expanded)
%              Maximal formula depth    :   13 (   4 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f42,plain,(
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

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,
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

fof(f49,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f43,f48,f47,f46])).

fof(f85,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f77,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f82,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f80,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f86,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f81,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f83,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f56,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f87,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f54,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f76,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f58,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f75,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f70])).

fof(f88,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f55,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1194,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_27,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_36,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_446,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_36])).

cnf(c_447,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_38,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_451,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_38])).

cnf(c_452,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_1238,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1194,c_447,c_452])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1211,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1676,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1238,c_1211])).

cnf(c_32,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1235,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_32,c_447,c_452])).

cnf(c_1784,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1676,c_1235])).

cnf(c_1817,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1784,c_1238])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1202,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4243,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1817,c_1202])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1209,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2286,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(superposition,[status(thm)],[c_1817,c_1209])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1210,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2288,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1817,c_1210])).

cnf(c_2295,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(demodulation,[status(thm)],[c_2286,c_2288])).

cnf(c_4247,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k2_struct_0(sK0)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4243,c_2295])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1193,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1232,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1193,c_447,c_452])).

cnf(c_1818,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1784,c_1232])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_28,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_419,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_28])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_437,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_419,c_37])).

cnf(c_438,plain,
    ( ~ l1_struct_0(sK1)
    | k2_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_440,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_438,c_36])).

cnf(c_1820,plain,
    ( k2_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1784,c_440])).

cnf(c_7194,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4247,c_1818,c_1820])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1192,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1213,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3524,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1192,c_1213])).

cnf(c_31,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1529,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1489,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1786,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1489])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1956,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3694,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3524,c_35,c_33,c_31,c_1529,c_1786,c_1956])).

cnf(c_1814,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1784,c_1676])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1199,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(X2)) = iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2702,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1814,c_1199])).

cnf(c_42,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_44,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_45,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1497,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1498,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1497])).

cnf(c_1787,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1786])).

cnf(c_1957,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1956])).

cnf(c_3029,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2702,c_42,c_44,c_45,c_1498,c_1787,c_1957])).

cnf(c_24,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1198,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2138,plain,
    ( k2_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1198,c_1211])).

cnf(c_3222,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3029,c_2138])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1500,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1609,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2434,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | k2_relset_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3282,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3222,c_35,c_33,c_31,c_1497,c_1500,c_1609,c_1786,c_1956,c_2434])).

cnf(c_3698,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(demodulation,[status(thm)],[c_3694,c_3282])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1214,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3562,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1192,c_1214])).

cnf(c_1526,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3720,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3562,c_35,c_33,c_31,c_1526,c_1786,c_1956])).

cnf(c_3929,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3698,c_3720])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1201,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4095,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3929,c_1201])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1212,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2709,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1192,c_1212])).

cnf(c_1532,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2976,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2709,c_35,c_33,c_31,c_1532,c_1786,c_1956])).

cnf(c_4101,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4095,c_2976])).

cnf(c_1523,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1524,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1523])).

cnf(c_4634,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4101,c_42,c_44,c_1524,c_1787,c_1957])).

cnf(c_4641,plain,
    ( k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    inference(superposition,[status(thm)],[c_4634,c_1209])).

cnf(c_2137,plain,
    ( k8_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0,X1) = k10_relat_1(X0,X1)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1198,c_1210])).

cnf(c_4322,plain,
    ( k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1192,c_2137])).

cnf(c_2364,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4421,plain,
    ( k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4322,c_35,c_33,c_1523,c_1786,c_1956,c_2364])).

cnf(c_4649,plain,
    ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(demodulation,[status(thm)],[c_4641,c_4421])).

cnf(c_4242,plain,
    ( k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1198,c_1202])).

cnf(c_25,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_57,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4918,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4242,c_57])).

cnf(c_4919,plain,
    ( k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4918])).

cnf(c_4929,plain,
    ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1192,c_4919])).

cnf(c_4963,plain,
    ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4929,c_44,c_1787,c_1820,c_1957])).

cnf(c_5079,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4649,c_4963])).

cnf(c_7196,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_7194,c_5079])).

cnf(c_19,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_30,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_460,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_461,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_1191,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_1413,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1191,c_447,c_452])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1196,plain,
    ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1593,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1235,c_1196])).

cnf(c_1732,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1593,c_42,c_45,c_1238,c_1232])).

cnf(c_1777,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1413,c_1732])).

cnf(c_1815,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1784,c_1777])).

cnf(c_7207,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7196,c_1815])).

cnf(c_3286,plain,
    ( k2_tops_2(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3282,c_1196])).

cnf(c_3292,plain,
    ( k2_tops_2(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3286,c_2976])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1494,plain,
    ( ~ v1_funct_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1495,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1494])).

cnf(c_1501,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1500])).

cnf(c_1610,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1625,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1610])).

cnf(c_1627,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1609])).

cnf(c_3352,plain,
    ( k2_tops_2(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3292,c_42,c_44,c_45,c_1495,c_1498,c_1501,c_1625,c_1627,c_1787,c_1957])).

cnf(c_3697,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_3694,c_3352])).

cnf(c_3927,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3697,c_3720])).

cnf(c_7219,plain,
    ( sK2 != sK2
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7207,c_3927])).

cnf(c_7220,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7219])).

cnf(c_1520,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1521,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1520])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7220,c_1957,c_1787,c_1524,c_1521,c_44,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:14:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.42/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.42/1.04  
% 1.42/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.42/1.04  
% 1.42/1.04  ------  iProver source info
% 1.42/1.04  
% 1.42/1.04  git: date: 2020-06-30 10:37:57 +0100
% 1.42/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.42/1.04  git: non_committed_changes: false
% 1.42/1.04  git: last_make_outside_of_git: false
% 1.42/1.04  
% 1.42/1.04  ------ 
% 1.42/1.04  
% 1.42/1.04  ------ Input Options
% 1.42/1.04  
% 1.42/1.04  --out_options                           all
% 1.42/1.04  --tptp_safe_out                         true
% 1.42/1.04  --problem_path                          ""
% 1.42/1.04  --include_path                          ""
% 1.42/1.04  --clausifier                            res/vclausify_rel
% 1.42/1.04  --clausifier_options                    --mode clausify
% 1.42/1.04  --stdin                                 false
% 1.42/1.04  --stats_out                             all
% 1.42/1.04  
% 1.42/1.04  ------ General Options
% 1.42/1.04  
% 1.42/1.04  --fof                                   false
% 1.42/1.04  --time_out_real                         305.
% 1.42/1.04  --time_out_virtual                      -1.
% 1.42/1.04  --symbol_type_check                     false
% 1.42/1.04  --clausify_out                          false
% 1.42/1.04  --sig_cnt_out                           false
% 1.42/1.04  --trig_cnt_out                          false
% 1.42/1.04  --trig_cnt_out_tolerance                1.
% 1.42/1.04  --trig_cnt_out_sk_spl                   false
% 1.42/1.04  --abstr_cl_out                          false
% 1.42/1.04  
% 1.42/1.04  ------ Global Options
% 1.42/1.04  
% 1.42/1.04  --schedule                              default
% 1.42/1.04  --add_important_lit                     false
% 1.42/1.04  --prop_solver_per_cl                    1000
% 1.42/1.04  --min_unsat_core                        false
% 1.42/1.04  --soft_assumptions                      false
% 1.42/1.04  --soft_lemma_size                       3
% 1.42/1.04  --prop_impl_unit_size                   0
% 1.42/1.04  --prop_impl_unit                        []
% 1.42/1.04  --share_sel_clauses                     true
% 1.42/1.04  --reset_solvers                         false
% 1.42/1.04  --bc_imp_inh                            [conj_cone]
% 1.42/1.04  --conj_cone_tolerance                   3.
% 1.42/1.04  --extra_neg_conj                        none
% 1.42/1.04  --large_theory_mode                     true
% 1.42/1.04  --prolific_symb_bound                   200
% 1.42/1.04  --lt_threshold                          2000
% 1.42/1.04  --clause_weak_htbl                      true
% 1.42/1.04  --gc_record_bc_elim                     false
% 1.42/1.04  
% 1.42/1.04  ------ Preprocessing Options
% 1.42/1.04  
% 1.42/1.04  --preprocessing_flag                    true
% 1.42/1.04  --time_out_prep_mult                    0.1
% 1.42/1.04  --splitting_mode                        input
% 1.42/1.04  --splitting_grd                         true
% 1.42/1.04  --splitting_cvd                         false
% 1.42/1.04  --splitting_cvd_svl                     false
% 1.42/1.04  --splitting_nvd                         32
% 1.42/1.04  --sub_typing                            true
% 1.42/1.04  --prep_gs_sim                           true
% 1.42/1.04  --prep_unflatten                        true
% 1.42/1.04  --prep_res_sim                          true
% 1.42/1.04  --prep_upred                            true
% 1.42/1.04  --prep_sem_filter                       exhaustive
% 1.42/1.04  --prep_sem_filter_out                   false
% 1.42/1.04  --pred_elim                             true
% 1.42/1.04  --res_sim_input                         true
% 1.42/1.04  --eq_ax_congr_red                       true
% 1.42/1.04  --pure_diseq_elim                       true
% 1.42/1.04  --brand_transform                       false
% 1.42/1.04  --non_eq_to_eq                          false
% 1.42/1.04  --prep_def_merge                        true
% 1.42/1.04  --prep_def_merge_prop_impl              false
% 1.42/1.04  --prep_def_merge_mbd                    true
% 1.42/1.04  --prep_def_merge_tr_red                 false
% 1.42/1.04  --prep_def_merge_tr_cl                  false
% 1.42/1.04  --smt_preprocessing                     true
% 1.42/1.04  --smt_ac_axioms                         fast
% 1.42/1.04  --preprocessed_out                      false
% 1.42/1.04  --preprocessed_stats                    false
% 1.42/1.04  
% 1.42/1.04  ------ Abstraction refinement Options
% 1.42/1.04  
% 1.42/1.04  --abstr_ref                             []
% 1.42/1.04  --abstr_ref_prep                        false
% 1.42/1.04  --abstr_ref_until_sat                   false
% 1.42/1.04  --abstr_ref_sig_restrict                funpre
% 1.42/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 1.42/1.04  --abstr_ref_under                       []
% 1.42/1.04  
% 1.42/1.04  ------ SAT Options
% 1.42/1.04  
% 1.42/1.04  --sat_mode                              false
% 1.42/1.04  --sat_fm_restart_options                ""
% 1.42/1.04  --sat_gr_def                            false
% 1.42/1.04  --sat_epr_types                         true
% 1.42/1.04  --sat_non_cyclic_types                  false
% 1.42/1.04  --sat_finite_models                     false
% 1.42/1.04  --sat_fm_lemmas                         false
% 1.42/1.04  --sat_fm_prep                           false
% 1.42/1.04  --sat_fm_uc_incr                        true
% 1.42/1.04  --sat_out_model                         small
% 1.42/1.04  --sat_out_clauses                       false
% 1.42/1.04  
% 1.42/1.04  ------ QBF Options
% 1.42/1.04  
% 1.42/1.04  --qbf_mode                              false
% 1.42/1.04  --qbf_elim_univ                         false
% 1.42/1.04  --qbf_dom_inst                          none
% 1.42/1.04  --qbf_dom_pre_inst                      false
% 1.42/1.04  --qbf_sk_in                             false
% 1.42/1.04  --qbf_pred_elim                         true
% 1.42/1.04  --qbf_split                             512
% 1.42/1.04  
% 1.42/1.04  ------ BMC1 Options
% 1.42/1.04  
% 1.42/1.04  --bmc1_incremental                      false
% 1.42/1.04  --bmc1_axioms                           reachable_all
% 1.42/1.04  --bmc1_min_bound                        0
% 1.42/1.04  --bmc1_max_bound                        -1
% 1.42/1.04  --bmc1_max_bound_default                -1
% 1.42/1.04  --bmc1_symbol_reachability              true
% 1.42/1.04  --bmc1_property_lemmas                  false
% 1.42/1.04  --bmc1_k_induction                      false
% 1.42/1.04  --bmc1_non_equiv_states                 false
% 1.42/1.04  --bmc1_deadlock                         false
% 1.42/1.04  --bmc1_ucm                              false
% 1.42/1.04  --bmc1_add_unsat_core                   none
% 1.42/1.04  --bmc1_unsat_core_children              false
% 1.42/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 1.42/1.04  --bmc1_out_stat                         full
% 1.42/1.04  --bmc1_ground_init                      false
% 1.42/1.04  --bmc1_pre_inst_next_state              false
% 1.42/1.04  --bmc1_pre_inst_state                   false
% 1.42/1.04  --bmc1_pre_inst_reach_state             false
% 1.42/1.04  --bmc1_out_unsat_core                   false
% 1.42/1.04  --bmc1_aig_witness_out                  false
% 1.42/1.04  --bmc1_verbose                          false
% 1.42/1.04  --bmc1_dump_clauses_tptp                false
% 1.42/1.04  --bmc1_dump_unsat_core_tptp             false
% 1.42/1.04  --bmc1_dump_file                        -
% 1.42/1.04  --bmc1_ucm_expand_uc_limit              128
% 1.42/1.04  --bmc1_ucm_n_expand_iterations          6
% 1.42/1.04  --bmc1_ucm_extend_mode                  1
% 1.42/1.04  --bmc1_ucm_init_mode                    2
% 1.42/1.04  --bmc1_ucm_cone_mode                    none
% 1.42/1.04  --bmc1_ucm_reduced_relation_type        0
% 1.42/1.04  --bmc1_ucm_relax_model                  4
% 1.42/1.04  --bmc1_ucm_full_tr_after_sat            true
% 1.42/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 1.42/1.04  --bmc1_ucm_layered_model                none
% 1.42/1.04  --bmc1_ucm_max_lemma_size               10
% 1.42/1.04  
% 1.42/1.04  ------ AIG Options
% 1.42/1.04  
% 1.42/1.04  --aig_mode                              false
% 1.42/1.04  
% 1.42/1.04  ------ Instantiation Options
% 1.42/1.04  
% 1.42/1.04  --instantiation_flag                    true
% 1.42/1.04  --inst_sos_flag                         false
% 1.42/1.04  --inst_sos_phase                        true
% 1.42/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.42/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.42/1.04  --inst_lit_sel_side                     num_symb
% 1.42/1.04  --inst_solver_per_active                1400
% 1.42/1.04  --inst_solver_calls_frac                1.
% 1.42/1.04  --inst_passive_queue_type               priority_queues
% 1.42/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.42/1.04  --inst_passive_queues_freq              [25;2]
% 1.42/1.04  --inst_dismatching                      true
% 1.42/1.04  --inst_eager_unprocessed_to_passive     true
% 1.42/1.04  --inst_prop_sim_given                   true
% 1.42/1.04  --inst_prop_sim_new                     false
% 1.42/1.04  --inst_subs_new                         false
% 1.42/1.04  --inst_eq_res_simp                      false
% 1.42/1.04  --inst_subs_given                       false
% 1.42/1.04  --inst_orphan_elimination               true
% 1.42/1.04  --inst_learning_loop_flag               true
% 1.42/1.04  --inst_learning_start                   3000
% 1.42/1.04  --inst_learning_factor                  2
% 1.42/1.04  --inst_start_prop_sim_after_learn       3
% 1.42/1.04  --inst_sel_renew                        solver
% 1.42/1.04  --inst_lit_activity_flag                true
% 1.42/1.04  --inst_restr_to_given                   false
% 1.42/1.04  --inst_activity_threshold               500
% 1.42/1.04  --inst_out_proof                        true
% 1.42/1.04  
% 1.42/1.04  ------ Resolution Options
% 1.42/1.04  
% 1.42/1.04  --resolution_flag                       true
% 1.42/1.04  --res_lit_sel                           adaptive
% 1.42/1.04  --res_lit_sel_side                      none
% 1.42/1.04  --res_ordering                          kbo
% 1.42/1.04  --res_to_prop_solver                    active
% 1.42/1.04  --res_prop_simpl_new                    false
% 1.42/1.04  --res_prop_simpl_given                  true
% 1.42/1.04  --res_passive_queue_type                priority_queues
% 1.42/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.42/1.04  --res_passive_queues_freq               [15;5]
% 1.42/1.04  --res_forward_subs                      full
% 1.42/1.04  --res_backward_subs                     full
% 1.42/1.04  --res_forward_subs_resolution           true
% 1.42/1.04  --res_backward_subs_resolution          true
% 1.42/1.04  --res_orphan_elimination                true
% 1.42/1.04  --res_time_limit                        2.
% 1.42/1.04  --res_out_proof                         true
% 1.42/1.04  
% 1.42/1.04  ------ Superposition Options
% 1.42/1.04  
% 1.42/1.04  --superposition_flag                    true
% 1.42/1.04  --sup_passive_queue_type                priority_queues
% 1.42/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.42/1.04  --sup_passive_queues_freq               [8;1;4]
% 1.42/1.04  --demod_completeness_check              fast
% 1.42/1.04  --demod_use_ground                      true
% 1.42/1.04  --sup_to_prop_solver                    passive
% 1.42/1.04  --sup_prop_simpl_new                    true
% 1.42/1.04  --sup_prop_simpl_given                  true
% 1.42/1.04  --sup_fun_splitting                     false
% 1.42/1.04  --sup_smt_interval                      50000
% 1.42/1.04  
% 1.42/1.04  ------ Superposition Simplification Setup
% 1.42/1.04  
% 1.42/1.04  --sup_indices_passive                   []
% 1.42/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.42/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.42/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.42/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 1.42/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.42/1.04  --sup_full_bw                           [BwDemod]
% 1.42/1.04  --sup_immed_triv                        [TrivRules]
% 1.42/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.42/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.42/1.04  --sup_immed_bw_main                     []
% 1.42/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.42/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 1.42/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.42/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.42/1.04  
% 1.42/1.04  ------ Combination Options
% 1.42/1.04  
% 1.42/1.04  --comb_res_mult                         3
% 1.42/1.04  --comb_sup_mult                         2
% 1.42/1.04  --comb_inst_mult                        10
% 1.42/1.04  
% 1.42/1.04  ------ Debug Options
% 1.42/1.04  
% 1.42/1.04  --dbg_backtrace                         false
% 1.42/1.04  --dbg_dump_prop_clauses                 false
% 1.42/1.04  --dbg_dump_prop_clauses_file            -
% 1.42/1.04  --dbg_out_stat                          false
% 1.42/1.04  ------ Parsing...
% 1.42/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.42/1.04  
% 1.42/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.42/1.04  
% 1.42/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.42/1.04  
% 1.42/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.42/1.04  ------ Proving...
% 1.42/1.04  ------ Problem Properties 
% 1.42/1.04  
% 1.42/1.04  
% 1.42/1.04  clauses                                 33
% 1.42/1.04  conjectures                             5
% 1.42/1.04  EPR                                     2
% 1.42/1.04  Horn                                    29
% 1.42/1.04  unary                                   9
% 1.42/1.04  binary                                  4
% 1.42/1.04  lits                                    99
% 1.42/1.04  lits eq                                 26
% 1.42/1.04  fd_pure                                 0
% 1.42/1.04  fd_pseudo                               0
% 1.42/1.04  fd_cond                                 3
% 1.42/1.04  fd_pseudo_cond                          0
% 1.42/1.04  AC symbols                              0
% 1.42/1.04  
% 1.42/1.04  ------ Schedule dynamic 5 is on 
% 1.42/1.04  
% 1.42/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.42/1.04  
% 1.42/1.04  
% 1.42/1.04  ------ 
% 1.42/1.04  Current options:
% 1.42/1.04  ------ 
% 1.42/1.04  
% 1.42/1.04  ------ Input Options
% 1.42/1.04  
% 1.42/1.04  --out_options                           all
% 1.42/1.04  --tptp_safe_out                         true
% 1.42/1.04  --problem_path                          ""
% 1.42/1.04  --include_path                          ""
% 1.42/1.04  --clausifier                            res/vclausify_rel
% 1.42/1.04  --clausifier_options                    --mode clausify
% 1.42/1.04  --stdin                                 false
% 1.42/1.04  --stats_out                             all
% 1.42/1.04  
% 1.42/1.04  ------ General Options
% 1.42/1.04  
% 1.42/1.04  --fof                                   false
% 1.42/1.04  --time_out_real                         305.
% 1.42/1.04  --time_out_virtual                      -1.
% 1.42/1.04  --symbol_type_check                     false
% 1.42/1.04  --clausify_out                          false
% 1.42/1.04  --sig_cnt_out                           false
% 1.42/1.04  --trig_cnt_out                          false
% 1.42/1.04  --trig_cnt_out_tolerance                1.
% 1.42/1.04  --trig_cnt_out_sk_spl                   false
% 1.42/1.04  --abstr_cl_out                          false
% 1.42/1.04  
% 1.42/1.04  ------ Global Options
% 1.42/1.04  
% 1.42/1.04  --schedule                              default
% 1.42/1.04  --add_important_lit                     false
% 1.42/1.04  --prop_solver_per_cl                    1000
% 1.42/1.04  --min_unsat_core                        false
% 1.42/1.04  --soft_assumptions                      false
% 1.42/1.04  --soft_lemma_size                       3
% 1.42/1.04  --prop_impl_unit_size                   0
% 1.42/1.04  --prop_impl_unit                        []
% 1.42/1.04  --share_sel_clauses                     true
% 1.42/1.04  --reset_solvers                         false
% 1.42/1.04  --bc_imp_inh                            [conj_cone]
% 1.42/1.04  --conj_cone_tolerance                   3.
% 1.42/1.04  --extra_neg_conj                        none
% 1.42/1.04  --large_theory_mode                     true
% 1.42/1.04  --prolific_symb_bound                   200
% 1.42/1.04  --lt_threshold                          2000
% 1.42/1.04  --clause_weak_htbl                      true
% 1.42/1.04  --gc_record_bc_elim                     false
% 1.42/1.04  
% 1.42/1.04  ------ Preprocessing Options
% 1.42/1.04  
% 1.42/1.04  --preprocessing_flag                    true
% 1.42/1.04  --time_out_prep_mult                    0.1
% 1.42/1.04  --splitting_mode                        input
% 1.42/1.04  --splitting_grd                         true
% 1.42/1.04  --splitting_cvd                         false
% 1.42/1.04  --splitting_cvd_svl                     false
% 1.42/1.04  --splitting_nvd                         32
% 1.42/1.04  --sub_typing                            true
% 1.42/1.04  --prep_gs_sim                           true
% 1.42/1.04  --prep_unflatten                        true
% 1.42/1.04  --prep_res_sim                          true
% 1.42/1.04  --prep_upred                            true
% 1.42/1.04  --prep_sem_filter                       exhaustive
% 1.42/1.04  --prep_sem_filter_out                   false
% 1.42/1.04  --pred_elim                             true
% 1.42/1.04  --res_sim_input                         true
% 1.42/1.04  --eq_ax_congr_red                       true
% 1.42/1.04  --pure_diseq_elim                       true
% 1.42/1.04  --brand_transform                       false
% 1.42/1.04  --non_eq_to_eq                          false
% 1.42/1.04  --prep_def_merge                        true
% 1.42/1.04  --prep_def_merge_prop_impl              false
% 1.42/1.04  --prep_def_merge_mbd                    true
% 1.42/1.04  --prep_def_merge_tr_red                 false
% 1.42/1.04  --prep_def_merge_tr_cl                  false
% 1.42/1.04  --smt_preprocessing                     true
% 1.42/1.04  --smt_ac_axioms                         fast
% 1.42/1.04  --preprocessed_out                      false
% 1.42/1.04  --preprocessed_stats                    false
% 1.42/1.04  
% 1.42/1.04  ------ Abstraction refinement Options
% 1.42/1.04  
% 1.42/1.04  --abstr_ref                             []
% 1.42/1.04  --abstr_ref_prep                        false
% 1.42/1.04  --abstr_ref_until_sat                   false
% 1.42/1.04  --abstr_ref_sig_restrict                funpre
% 1.42/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 1.42/1.04  --abstr_ref_under                       []
% 1.42/1.04  
% 1.42/1.04  ------ SAT Options
% 1.42/1.04  
% 1.42/1.04  --sat_mode                              false
% 1.42/1.04  --sat_fm_restart_options                ""
% 1.42/1.04  --sat_gr_def                            false
% 1.42/1.04  --sat_epr_types                         true
% 1.42/1.04  --sat_non_cyclic_types                  false
% 1.42/1.04  --sat_finite_models                     false
% 1.42/1.04  --sat_fm_lemmas                         false
% 1.42/1.04  --sat_fm_prep                           false
% 1.42/1.04  --sat_fm_uc_incr                        true
% 1.42/1.04  --sat_out_model                         small
% 1.42/1.04  --sat_out_clauses                       false
% 1.42/1.04  
% 1.42/1.04  ------ QBF Options
% 1.42/1.04  
% 1.42/1.04  --qbf_mode                              false
% 1.42/1.04  --qbf_elim_univ                         false
% 1.42/1.04  --qbf_dom_inst                          none
% 1.42/1.04  --qbf_dom_pre_inst                      false
% 1.42/1.04  --qbf_sk_in                             false
% 1.42/1.04  --qbf_pred_elim                         true
% 1.42/1.04  --qbf_split                             512
% 1.42/1.04  
% 1.42/1.04  ------ BMC1 Options
% 1.42/1.04  
% 1.42/1.04  --bmc1_incremental                      false
% 1.42/1.04  --bmc1_axioms                           reachable_all
% 1.42/1.04  --bmc1_min_bound                        0
% 1.42/1.04  --bmc1_max_bound                        -1
% 1.42/1.04  --bmc1_max_bound_default                -1
% 1.42/1.04  --bmc1_symbol_reachability              true
% 1.42/1.04  --bmc1_property_lemmas                  false
% 1.42/1.04  --bmc1_k_induction                      false
% 1.42/1.04  --bmc1_non_equiv_states                 false
% 1.42/1.04  --bmc1_deadlock                         false
% 1.42/1.04  --bmc1_ucm                              false
% 1.42/1.04  --bmc1_add_unsat_core                   none
% 1.42/1.04  --bmc1_unsat_core_children              false
% 1.42/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 1.42/1.04  --bmc1_out_stat                         full
% 1.42/1.04  --bmc1_ground_init                      false
% 1.42/1.04  --bmc1_pre_inst_next_state              false
% 1.42/1.04  --bmc1_pre_inst_state                   false
% 1.42/1.04  --bmc1_pre_inst_reach_state             false
% 1.42/1.04  --bmc1_out_unsat_core                   false
% 1.42/1.04  --bmc1_aig_witness_out                  false
% 1.42/1.04  --bmc1_verbose                          false
% 1.42/1.04  --bmc1_dump_clauses_tptp                false
% 1.42/1.04  --bmc1_dump_unsat_core_tptp             false
% 1.42/1.04  --bmc1_dump_file                        -
% 1.42/1.04  --bmc1_ucm_expand_uc_limit              128
% 1.42/1.04  --bmc1_ucm_n_expand_iterations          6
% 1.42/1.04  --bmc1_ucm_extend_mode                  1
% 1.42/1.04  --bmc1_ucm_init_mode                    2
% 1.42/1.04  --bmc1_ucm_cone_mode                    none
% 1.42/1.04  --bmc1_ucm_reduced_relation_type        0
% 1.42/1.04  --bmc1_ucm_relax_model                  4
% 1.42/1.04  --bmc1_ucm_full_tr_after_sat            true
% 1.42/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 1.42/1.04  --bmc1_ucm_layered_model                none
% 1.42/1.04  --bmc1_ucm_max_lemma_size               10
% 1.42/1.04  
% 1.42/1.04  ------ AIG Options
% 1.42/1.04  
% 1.42/1.04  --aig_mode                              false
% 1.42/1.04  
% 1.42/1.04  ------ Instantiation Options
% 1.42/1.04  
% 1.42/1.04  --instantiation_flag                    true
% 1.42/1.04  --inst_sos_flag                         false
% 1.42/1.04  --inst_sos_phase                        true
% 1.42/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.42/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.42/1.04  --inst_lit_sel_side                     none
% 1.42/1.04  --inst_solver_per_active                1400
% 1.42/1.04  --inst_solver_calls_frac                1.
% 1.42/1.04  --inst_passive_queue_type               priority_queues
% 1.42/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.42/1.04  --inst_passive_queues_freq              [25;2]
% 1.42/1.04  --inst_dismatching                      true
% 1.42/1.04  --inst_eager_unprocessed_to_passive     true
% 1.42/1.04  --inst_prop_sim_given                   true
% 1.42/1.04  --inst_prop_sim_new                     false
% 1.42/1.04  --inst_subs_new                         false
% 1.42/1.04  --inst_eq_res_simp                      false
% 1.42/1.04  --inst_subs_given                       false
% 1.42/1.04  --inst_orphan_elimination               true
% 1.42/1.04  --inst_learning_loop_flag               true
% 1.42/1.04  --inst_learning_start                   3000
% 1.42/1.04  --inst_learning_factor                  2
% 1.42/1.04  --inst_start_prop_sim_after_learn       3
% 1.42/1.04  --inst_sel_renew                        solver
% 1.42/1.04  --inst_lit_activity_flag                true
% 1.42/1.04  --inst_restr_to_given                   false
% 1.42/1.04  --inst_activity_threshold               500
% 1.42/1.04  --inst_out_proof                        true
% 1.42/1.04  
% 1.42/1.04  ------ Resolution Options
% 1.42/1.04  
% 1.42/1.04  --resolution_flag                       false
% 1.42/1.04  --res_lit_sel                           adaptive
% 1.42/1.04  --res_lit_sel_side                      none
% 1.42/1.04  --res_ordering                          kbo
% 1.42/1.04  --res_to_prop_solver                    active
% 1.42/1.04  --res_prop_simpl_new                    false
% 1.42/1.04  --res_prop_simpl_given                  true
% 1.42/1.04  --res_passive_queue_type                priority_queues
% 1.42/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.42/1.04  --res_passive_queues_freq               [15;5]
% 1.42/1.04  --res_forward_subs                      full
% 1.42/1.04  --res_backward_subs                     full
% 1.42/1.04  --res_forward_subs_resolution           true
% 1.42/1.04  --res_backward_subs_resolution          true
% 1.42/1.04  --res_orphan_elimination                true
% 1.42/1.04  --res_time_limit                        2.
% 1.42/1.04  --res_out_proof                         true
% 1.42/1.04  
% 1.42/1.04  ------ Superposition Options
% 1.42/1.04  
% 1.42/1.04  --superposition_flag                    true
% 1.42/1.04  --sup_passive_queue_type                priority_queues
% 1.42/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.42/1.04  --sup_passive_queues_freq               [8;1;4]
% 1.42/1.04  --demod_completeness_check              fast
% 1.42/1.04  --demod_use_ground                      true
% 1.42/1.04  --sup_to_prop_solver                    passive
% 1.42/1.04  --sup_prop_simpl_new                    true
% 1.42/1.04  --sup_prop_simpl_given                  true
% 1.42/1.04  --sup_fun_splitting                     false
% 1.42/1.04  --sup_smt_interval                      50000
% 1.42/1.04  
% 1.42/1.04  ------ Superposition Simplification Setup
% 1.42/1.04  
% 1.42/1.04  --sup_indices_passive                   []
% 1.42/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.42/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.42/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.42/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 1.42/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.42/1.04  --sup_full_bw                           [BwDemod]
% 1.42/1.04  --sup_immed_triv                        [TrivRules]
% 1.42/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.42/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.42/1.04  --sup_immed_bw_main                     []
% 1.42/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.42/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 1.42/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.42/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.42/1.04  
% 1.42/1.04  ------ Combination Options
% 1.42/1.04  
% 1.42/1.04  --comb_res_mult                         3
% 1.42/1.04  --comb_sup_mult                         2
% 1.42/1.04  --comb_inst_mult                        10
% 1.42/1.04  
% 1.42/1.04  ------ Debug Options
% 1.42/1.04  
% 1.42/1.04  --dbg_backtrace                         false
% 1.42/1.04  --dbg_dump_prop_clauses                 false
% 1.42/1.04  --dbg_dump_prop_clauses_file            -
% 1.42/1.04  --dbg_out_stat                          false
% 1.42/1.04  
% 1.42/1.04  
% 1.42/1.04  
% 1.42/1.04  
% 1.42/1.04  ------ Proving...
% 1.42/1.04  
% 1.42/1.04  
% 1.42/1.04  % SZS status Theorem for theBenchmark.p
% 1.42/1.04  
% 1.42/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 1.42/1.04  
% 1.42/1.04  fof(f17,conjecture,(
% 1.42/1.04    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.42/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.42/1.04  
% 1.42/1.04  fof(f18,negated_conjecture,(
% 1.42/1.04    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.42/1.04    inference(negated_conjecture,[],[f17])).
% 1.42/1.04  
% 1.42/1.04  fof(f42,plain,(
% 1.42/1.04    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 1.42/1.04    inference(ennf_transformation,[],[f18])).
% 1.42/1.04  
% 1.42/1.04  fof(f43,plain,(
% 1.42/1.04    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 1.42/1.04    inference(flattening,[],[f42])).
% 1.42/1.04  
% 1.42/1.04  fof(f48,plain,(
% 1.42/1.04    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 1.42/1.04    introduced(choice_axiom,[])).
% 1.42/1.04  
% 1.42/1.04  fof(f47,plain,(
% 1.42/1.04    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 1.42/1.04    introduced(choice_axiom,[])).
% 1.42/1.04  
% 1.42/1.04  fof(f46,plain,(
% 1.42/1.04    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 1.42/1.04    introduced(choice_axiom,[])).
% 1.42/1.04  
% 1.42/1.04  fof(f49,plain,(
% 1.42/1.04    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 1.42/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f43,f48,f47,f46])).
% 1.42/1.04  
% 1.42/1.04  fof(f85,plain,(
% 1.42/1.04    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.42/1.04    inference(cnf_transformation,[],[f49])).
% 1.42/1.04  
% 1.42/1.04  fof(f14,axiom,(
% 1.42/1.04    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.42/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.42/1.04  
% 1.42/1.04  fof(f37,plain,(
% 1.42/1.04    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.42/1.04    inference(ennf_transformation,[],[f14])).
% 1.42/1.04  
% 1.42/1.04  fof(f77,plain,(
% 1.42/1.04    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.42/1.04    inference(cnf_transformation,[],[f37])).
% 1.42/1.04  
% 1.42/1.04  fof(f82,plain,(
% 1.42/1.04    l1_struct_0(sK1)),
% 1.42/1.04    inference(cnf_transformation,[],[f49])).
% 1.42/1.04  
% 1.42/1.04  fof(f80,plain,(
% 1.42/1.04    l1_struct_0(sK0)),
% 1.42/1.04    inference(cnf_transformation,[],[f49])).
% 1.42/1.04  
% 1.42/1.04  fof(f7,axiom,(
% 1.42/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.42/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.42/1.04  
% 1.42/1.04  fof(f26,plain,(
% 1.42/1.04    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/1.04    inference(ennf_transformation,[],[f7])).
% 1.42/1.04  
% 1.42/1.04  fof(f59,plain,(
% 1.42/1.04    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.42/1.04    inference(cnf_transformation,[],[f26])).
% 1.42/1.04  
% 1.42/1.04  fof(f86,plain,(
% 1.42/1.04    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 1.42/1.04    inference(cnf_transformation,[],[f49])).
% 1.42/1.04  
% 1.42/1.04  fof(f10,axiom,(
% 1.42/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.42/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.42/1.04  
% 1.42/1.04  fof(f29,plain,(
% 1.42/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/1.04    inference(ennf_transformation,[],[f10])).
% 1.42/1.04  
% 1.42/1.04  fof(f30,plain,(
% 1.42/1.04    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/1.04    inference(flattening,[],[f29])).
% 1.42/1.04  
% 1.42/1.04  fof(f44,plain,(
% 1.42/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/1.04    inference(nnf_transformation,[],[f30])).
% 1.42/1.04  
% 1.42/1.04  fof(f63,plain,(
% 1.42/1.04    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.42/1.04    inference(cnf_transformation,[],[f44])).
% 1.42/1.04  
% 1.42/1.04  fof(f9,axiom,(
% 1.42/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 1.42/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.42/1.04  
% 1.42/1.04  fof(f28,plain,(
% 1.42/1.04    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/1.04    inference(ennf_transformation,[],[f9])).
% 1.42/1.04  
% 1.42/1.04  fof(f62,plain,(
% 1.42/1.04    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.42/1.04    inference(cnf_transformation,[],[f28])).
% 1.42/1.04  
% 1.42/1.04  fof(f8,axiom,(
% 1.42/1.04    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.42/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.42/1.04  
% 1.42/1.04  fof(f27,plain,(
% 1.42/1.04    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/1.04    inference(ennf_transformation,[],[f8])).
% 1.42/1.04  
% 1.42/1.04  fof(f60,plain,(
% 1.42/1.04    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.42/1.04    inference(cnf_transformation,[],[f27])).
% 1.42/1.04  
% 1.42/1.04  fof(f84,plain,(
% 1.42/1.04    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.42/1.04    inference(cnf_transformation,[],[f49])).
% 1.42/1.04  
% 1.42/1.04  fof(f1,axiom,(
% 1.42/1.04    v1_xboole_0(k1_xboole_0)),
% 1.42/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.42/1.04  
% 1.42/1.04  fof(f50,plain,(
% 1.42/1.04    v1_xboole_0(k1_xboole_0)),
% 1.42/1.04    inference(cnf_transformation,[],[f1])).
% 1.42/1.04  
% 1.42/1.04  fof(f15,axiom,(
% 1.42/1.04    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 1.42/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.42/1.04  
% 1.42/1.04  fof(f38,plain,(
% 1.42/1.04    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.42/1.04    inference(ennf_transformation,[],[f15])).
% 1.42/1.04  
% 1.42/1.04  fof(f39,plain,(
% 1.42/1.04    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.42/1.04    inference(flattening,[],[f38])).
% 1.42/1.04  
% 1.42/1.04  fof(f78,plain,(
% 1.42/1.04    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.42/1.04    inference(cnf_transformation,[],[f39])).
% 1.42/1.04  
% 1.42/1.04  fof(f81,plain,(
% 1.42/1.04    ~v2_struct_0(sK1)),
% 1.42/1.04    inference(cnf_transformation,[],[f49])).
% 1.42/1.04  
% 1.42/1.04  fof(f83,plain,(
% 1.42/1.04    v1_funct_1(sK2)),
% 1.42/1.04    inference(cnf_transformation,[],[f49])).
% 1.42/1.04  
% 1.42/1.04  fof(f5,axiom,(
% 1.42/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.42/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.42/1.04  
% 1.42/1.04  fof(f22,plain,(
% 1.42/1.04    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.42/1.04    inference(ennf_transformation,[],[f5])).
% 1.42/1.04  
% 1.42/1.04  fof(f23,plain,(
% 1.42/1.04    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.42/1.04    inference(flattening,[],[f22])).
% 1.42/1.04  
% 1.42/1.04  fof(f56,plain,(
% 1.42/1.04    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.42/1.04    inference(cnf_transformation,[],[f23])).
% 1.42/1.04  
% 1.42/1.04  fof(f87,plain,(
% 1.42/1.04    v2_funct_1(sK2)),
% 1.42/1.04    inference(cnf_transformation,[],[f49])).
% 1.42/1.04  
% 1.42/1.04  fof(f2,axiom,(
% 1.42/1.04    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.42/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.42/1.04  
% 1.42/1.04  fof(f19,plain,(
% 1.42/1.04    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.42/1.04    inference(ennf_transformation,[],[f2])).
% 1.42/1.04  
% 1.42/1.04  fof(f51,plain,(
% 1.42/1.04    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.42/1.04    inference(cnf_transformation,[],[f19])).
% 1.42/1.04  
% 1.42/1.04  fof(f3,axiom,(
% 1.42/1.04    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.42/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.42/1.04  
% 1.42/1.04  fof(f52,plain,(
% 1.42/1.04    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.42/1.04    inference(cnf_transformation,[],[f3])).
% 1.42/1.04  
% 1.42/1.04  fof(f12,axiom,(
% 1.42/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.42/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.42/1.04  
% 1.42/1.04  fof(f33,plain,(
% 1.42/1.04    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.42/1.04    inference(ennf_transformation,[],[f12])).
% 1.42/1.04  
% 1.42/1.04  fof(f34,plain,(
% 1.42/1.04    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.42/1.04    inference(flattening,[],[f33])).
% 1.42/1.04  
% 1.42/1.04  fof(f71,plain,(
% 1.42/1.04    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.42/1.04    inference(cnf_transformation,[],[f34])).
% 1.42/1.04  
% 1.42/1.04  fof(f4,axiom,(
% 1.42/1.04    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.42/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.42/1.04  
% 1.42/1.04  fof(f20,plain,(
% 1.42/1.04    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.42/1.04    inference(ennf_transformation,[],[f4])).
% 1.42/1.04  
% 1.42/1.04  fof(f21,plain,(
% 1.42/1.04    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.42/1.04    inference(flattening,[],[f20])).
% 1.42/1.04  
% 1.42/1.04  fof(f54,plain,(
% 1.42/1.04    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.42/1.04    inference(cnf_transformation,[],[f21])).
% 1.42/1.04  
% 1.42/1.04  fof(f13,axiom,(
% 1.42/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.42/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.42/1.04  
% 1.42/1.04  fof(f35,plain,(
% 1.42/1.04    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.42/1.04    inference(ennf_transformation,[],[f13])).
% 1.42/1.04  
% 1.42/1.04  fof(f36,plain,(
% 1.42/1.04    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.42/1.04    inference(flattening,[],[f35])).
% 1.42/1.04  
% 1.42/1.04  fof(f76,plain,(
% 1.42/1.04    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.42/1.04    inference(cnf_transformation,[],[f36])).
% 1.42/1.04  
% 1.42/1.04  fof(f53,plain,(
% 1.42/1.04    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.42/1.04    inference(cnf_transformation,[],[f21])).
% 1.42/1.04  
% 1.42/1.04  fof(f57,plain,(
% 1.42/1.04    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.42/1.04    inference(cnf_transformation,[],[f23])).
% 1.42/1.04  
% 1.42/1.04  fof(f73,plain,(
% 1.42/1.04    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.42/1.04    inference(cnf_transformation,[],[f34])).
% 1.42/1.04  
% 1.42/1.04  fof(f6,axiom,(
% 1.42/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.42/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.42/1.04  
% 1.42/1.04  fof(f24,plain,(
% 1.42/1.04    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.42/1.04    inference(ennf_transformation,[],[f6])).
% 1.42/1.04  
% 1.42/1.04  fof(f25,plain,(
% 1.42/1.04    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.42/1.04    inference(flattening,[],[f24])).
% 1.42/1.04  
% 1.42/1.04  fof(f58,plain,(
% 1.42/1.04    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.42/1.04    inference(cnf_transformation,[],[f25])).
% 1.42/1.04  
% 1.42/1.04  fof(f75,plain,(
% 1.42/1.04    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.42/1.04    inference(cnf_transformation,[],[f36])).
% 1.42/1.04  
% 1.42/1.04  fof(f11,axiom,(
% 1.42/1.04    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.42/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.42/1.04  
% 1.42/1.04  fof(f31,plain,(
% 1.42/1.04    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.42/1.04    inference(ennf_transformation,[],[f11])).
% 1.42/1.04  
% 1.42/1.04  fof(f32,plain,(
% 1.42/1.04    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.42/1.04    inference(flattening,[],[f31])).
% 1.42/1.04  
% 1.42/1.04  fof(f45,plain,(
% 1.42/1.04    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.42/1.04    inference(nnf_transformation,[],[f32])).
% 1.42/1.04  
% 1.42/1.04  fof(f70,plain,(
% 1.42/1.04    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.42/1.04    inference(cnf_transformation,[],[f45])).
% 1.42/1.04  
% 1.42/1.04  fof(f94,plain,(
% 1.42/1.04    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.42/1.04    inference(equality_resolution,[],[f70])).
% 1.42/1.04  
% 1.42/1.04  fof(f88,plain,(
% 1.42/1.04    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 1.42/1.04    inference(cnf_transformation,[],[f49])).
% 1.42/1.04  
% 1.42/1.04  fof(f16,axiom,(
% 1.42/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 1.42/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.42/1.04  
% 1.42/1.04  fof(f40,plain,(
% 1.42/1.04    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.42/1.04    inference(ennf_transformation,[],[f16])).
% 1.42/1.04  
% 1.42/1.04  fof(f41,plain,(
% 1.42/1.04    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.42/1.04    inference(flattening,[],[f40])).
% 1.42/1.04  
% 1.42/1.04  fof(f79,plain,(
% 1.42/1.04    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.42/1.04    inference(cnf_transformation,[],[f41])).
% 1.42/1.04  
% 1.42/1.04  fof(f55,plain,(
% 1.42/1.04    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.42/1.04    inference(cnf_transformation,[],[f21])).
% 1.42/1.04  
% 1.42/1.04  cnf(c_33,negated_conjecture,
% 1.42/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 1.42/1.04      inference(cnf_transformation,[],[f85]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1194,plain,
% 1.42/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_27,plain,
% 1.42/1.04      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.42/1.04      inference(cnf_transformation,[],[f77]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_36,negated_conjecture,
% 1.42/1.04      ( l1_struct_0(sK1) ),
% 1.42/1.04      inference(cnf_transformation,[],[f82]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_446,plain,
% 1.42/1.04      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 1.42/1.04      inference(resolution_lifted,[status(thm)],[c_27,c_36]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_447,plain,
% 1.42/1.04      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.42/1.04      inference(unflattening,[status(thm)],[c_446]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_38,negated_conjecture,
% 1.42/1.04      ( l1_struct_0(sK0) ),
% 1.42/1.04      inference(cnf_transformation,[],[f80]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_451,plain,
% 1.42/1.04      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 1.42/1.04      inference(resolution_lifted,[status(thm)],[c_27,c_38]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_452,plain,
% 1.42/1.04      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 1.42/1.04      inference(unflattening,[status(thm)],[c_451]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1238,plain,
% 1.42/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 1.42/1.04      inference(light_normalisation,[status(thm)],[c_1194,c_447,c_452]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_9,plain,
% 1.42/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.42/1.04      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.42/1.04      inference(cnf_transformation,[],[f59]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1211,plain,
% 1.42/1.04      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 1.42/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1676,plain,
% 1.42/1.04      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 1.42/1.04      inference(superposition,[status(thm)],[c_1238,c_1211]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_32,negated_conjecture,
% 1.42/1.04      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 1.42/1.04      inference(cnf_transformation,[],[f86]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1235,plain,
% 1.42/1.04      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 1.42/1.04      inference(light_normalisation,[status(thm)],[c_32,c_447,c_452]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1784,plain,
% 1.42/1.04      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 1.42/1.04      inference(demodulation,[status(thm)],[c_1676,c_1235]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1817,plain,
% 1.42/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 1.42/1.04      inference(demodulation,[status(thm)],[c_1784,c_1238]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_18,plain,
% 1.42/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 1.42/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.42/1.04      | k1_relset_1(X1,X2,X0) = X1
% 1.42/1.04      | k1_xboole_0 = X2 ),
% 1.42/1.04      inference(cnf_transformation,[],[f63]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1202,plain,
% 1.42/1.04      ( k1_relset_1(X0,X1,X2) = X0
% 1.42/1.04      | k1_xboole_0 = X1
% 1.42/1.04      | v1_funct_2(X2,X0,X1) != iProver_top
% 1.42/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_4243,plain,
% 1.42/1.04      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0)
% 1.42/1.04      | k2_relat_1(sK2) = k1_xboole_0
% 1.42/1.04      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
% 1.42/1.04      inference(superposition,[status(thm)],[c_1817,c_1202]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_11,plain,
% 1.42/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.42/1.04      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 1.42/1.04      inference(cnf_transformation,[],[f62]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1209,plain,
% 1.42/1.04      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 1.42/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_2286,plain,
% 1.42/1.04      ( k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
% 1.42/1.04      inference(superposition,[status(thm)],[c_1817,c_1209]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_10,plain,
% 1.42/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.42/1.04      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 1.42/1.04      inference(cnf_transformation,[],[f60]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1210,plain,
% 1.42/1.04      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 1.42/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_2288,plain,
% 1.42/1.04      ( k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0) ),
% 1.42/1.04      inference(superposition,[status(thm)],[c_1817,c_1210]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_2295,plain,
% 1.42/1.04      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
% 1.42/1.04      inference(demodulation,[status(thm)],[c_2286,c_2288]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_4247,plain,
% 1.42/1.04      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k2_struct_0(sK0)
% 1.42/1.04      | k2_relat_1(sK2) = k1_xboole_0
% 1.42/1.04      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
% 1.42/1.04      inference(demodulation,[status(thm)],[c_4243,c_2295]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_34,negated_conjecture,
% 1.42/1.04      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 1.42/1.04      inference(cnf_transformation,[],[f84]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1193,plain,
% 1.42/1.04      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1232,plain,
% 1.42/1.04      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 1.42/1.04      inference(light_normalisation,[status(thm)],[c_1193,c_447,c_452]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1818,plain,
% 1.42/1.04      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 1.42/1.04      inference(demodulation,[status(thm)],[c_1784,c_1232]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_0,plain,
% 1.42/1.04      ( v1_xboole_0(k1_xboole_0) ),
% 1.42/1.04      inference(cnf_transformation,[],[f50]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_28,plain,
% 1.42/1.04      ( v2_struct_0(X0)
% 1.42/1.04      | ~ l1_struct_0(X0)
% 1.42/1.04      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 1.42/1.04      inference(cnf_transformation,[],[f78]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_419,plain,
% 1.42/1.04      ( v2_struct_0(X0)
% 1.42/1.04      | ~ l1_struct_0(X0)
% 1.42/1.04      | k2_struct_0(X0) != k1_xboole_0 ),
% 1.42/1.04      inference(resolution_lifted,[status(thm)],[c_0,c_28]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_37,negated_conjecture,
% 1.42/1.04      ( ~ v2_struct_0(sK1) ),
% 1.42/1.04      inference(cnf_transformation,[],[f81]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_437,plain,
% 1.42/1.04      ( ~ l1_struct_0(X0) | k2_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 1.42/1.04      inference(resolution_lifted,[status(thm)],[c_419,c_37]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_438,plain,
% 1.42/1.04      ( ~ l1_struct_0(sK1) | k2_struct_0(sK1) != k1_xboole_0 ),
% 1.42/1.04      inference(unflattening,[status(thm)],[c_437]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_440,plain,
% 1.42/1.04      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 1.42/1.04      inference(global_propositional_subsumption,
% 1.42/1.04                [status(thm)],
% 1.42/1.04                [c_438,c_36]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1820,plain,
% 1.42/1.04      ( k2_relat_1(sK2) != k1_xboole_0 ),
% 1.42/1.04      inference(demodulation,[status(thm)],[c_1784,c_440]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_7194,plain,
% 1.42/1.04      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k2_struct_0(sK0) ),
% 1.42/1.04      inference(global_propositional_subsumption,
% 1.42/1.04                [status(thm)],
% 1.42/1.04                [c_4247,c_1818,c_1820]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_35,negated_conjecture,
% 1.42/1.04      ( v1_funct_1(sK2) ),
% 1.42/1.04      inference(cnf_transformation,[],[f83]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1192,plain,
% 1.42/1.04      ( v1_funct_1(sK2) = iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_7,plain,
% 1.42/1.04      ( ~ v1_funct_1(X0)
% 1.42/1.04      | ~ v2_funct_1(X0)
% 1.42/1.04      | ~ v1_relat_1(X0)
% 1.42/1.04      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 1.42/1.04      inference(cnf_transformation,[],[f56]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1213,plain,
% 1.42/1.04      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 1.42/1.04      | v1_funct_1(X0) != iProver_top
% 1.42/1.04      | v2_funct_1(X0) != iProver_top
% 1.42/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_3524,plain,
% 1.42/1.04      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 1.42/1.04      | v2_funct_1(sK2) != iProver_top
% 1.42/1.04      | v1_relat_1(sK2) != iProver_top ),
% 1.42/1.04      inference(superposition,[status(thm)],[c_1192,c_1213]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_31,negated_conjecture,
% 1.42/1.04      ( v2_funct_1(sK2) ),
% 1.42/1.04      inference(cnf_transformation,[],[f87]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1529,plain,
% 1.42/1.04      ( ~ v1_funct_1(sK2)
% 1.42/1.04      | ~ v2_funct_1(sK2)
% 1.42/1.04      | ~ v1_relat_1(sK2)
% 1.42/1.04      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 1.42/1.04      inference(instantiation,[status(thm)],[c_7]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1,plain,
% 1.42/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.42/1.04      | ~ v1_relat_1(X1)
% 1.42/1.04      | v1_relat_1(X0) ),
% 1.42/1.04      inference(cnf_transformation,[],[f51]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1489,plain,
% 1.42/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.42/1.04      | v1_relat_1(X0)
% 1.42/1.04      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 1.42/1.04      inference(instantiation,[status(thm)],[c_1]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1786,plain,
% 1.42/1.04      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.42/1.04      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 1.42/1.04      | v1_relat_1(sK2) ),
% 1.42/1.04      inference(instantiation,[status(thm)],[c_1489]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_2,plain,
% 1.42/1.04      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.42/1.04      inference(cnf_transformation,[],[f52]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1956,plain,
% 1.42/1.04      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 1.42/1.04      inference(instantiation,[status(thm)],[c_2]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_3694,plain,
% 1.42/1.04      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 1.42/1.04      inference(global_propositional_subsumption,
% 1.42/1.04                [status(thm)],
% 1.42/1.04                [c_3524,c_35,c_33,c_31,c_1529,c_1786,c_1956]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1814,plain,
% 1.42/1.04      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 1.42/1.04      inference(demodulation,[status(thm)],[c_1784,c_1676]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_23,plain,
% 1.42/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 1.42/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.42/1.04      | ~ v1_funct_1(X0)
% 1.42/1.04      | v1_funct_1(k2_funct_1(X0))
% 1.42/1.04      | ~ v2_funct_1(X0)
% 1.42/1.04      | k2_relset_1(X1,X2,X0) != X2 ),
% 1.42/1.04      inference(cnf_transformation,[],[f71]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1199,plain,
% 1.42/1.04      ( k2_relset_1(X0,X1,X2) != X1
% 1.42/1.04      | v1_funct_2(X2,X0,X1) != iProver_top
% 1.42/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.42/1.04      | v1_funct_1(X2) != iProver_top
% 1.42/1.04      | v1_funct_1(k2_funct_1(X2)) = iProver_top
% 1.42/1.04      | v2_funct_1(X2) != iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_2702,plain,
% 1.42/1.04      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 1.42/1.04      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 1.42/1.04      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 1.42/1.04      | v1_funct_1(sK2) != iProver_top
% 1.42/1.04      | v2_funct_1(sK2) != iProver_top ),
% 1.42/1.04      inference(superposition,[status(thm)],[c_1814,c_1199]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_42,plain,
% 1.42/1.04      ( v1_funct_1(sK2) = iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_44,plain,
% 1.42/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_45,plain,
% 1.42/1.04      ( v2_funct_1(sK2) = iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_4,plain,
% 1.42/1.04      ( ~ v1_funct_1(X0)
% 1.42/1.04      | v1_funct_1(k2_funct_1(X0))
% 1.42/1.04      | ~ v2_funct_1(X0)
% 1.42/1.04      | ~ v1_relat_1(X0) ),
% 1.42/1.04      inference(cnf_transformation,[],[f54]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1497,plain,
% 1.42/1.04      ( v1_funct_1(k2_funct_1(sK2))
% 1.42/1.04      | ~ v1_funct_1(sK2)
% 1.42/1.04      | ~ v2_funct_1(sK2)
% 1.42/1.04      | ~ v1_relat_1(sK2) ),
% 1.42/1.04      inference(instantiation,[status(thm)],[c_4]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1498,plain,
% 1.42/1.04      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 1.42/1.04      | v1_funct_1(sK2) != iProver_top
% 1.42/1.04      | v2_funct_1(sK2) != iProver_top
% 1.42/1.04      | v1_relat_1(sK2) != iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_1497]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1787,plain,
% 1.42/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 1.42/1.04      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 1.42/1.04      | v1_relat_1(sK2) = iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_1786]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1957,plain,
% 1.42/1.04      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_1956]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_3029,plain,
% 1.42/1.04      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 1.42/1.04      inference(global_propositional_subsumption,
% 1.42/1.04                [status(thm)],
% 1.42/1.04                [c_2702,c_42,c_44,c_45,c_1498,c_1787,c_1957]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_24,plain,
% 1.42/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 1.42/1.04      | ~ v1_funct_1(X0)
% 1.42/1.04      | ~ v1_relat_1(X0) ),
% 1.42/1.04      inference(cnf_transformation,[],[f76]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1198,plain,
% 1.42/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 1.42/1.04      | v1_funct_1(X0) != iProver_top
% 1.42/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_2138,plain,
% 1.42/1.04      ( k2_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k2_relat_1(X0)
% 1.42/1.04      | v1_funct_1(X0) != iProver_top
% 1.42/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.42/1.04      inference(superposition,[status(thm)],[c_1198,c_1211]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_3222,plain,
% 1.42/1.04      ( k2_relset_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
% 1.42/1.04      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 1.42/1.04      inference(superposition,[status(thm)],[c_3029,c_2138]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_5,plain,
% 1.42/1.04      ( ~ v1_funct_1(X0)
% 1.42/1.04      | ~ v2_funct_1(X0)
% 1.42/1.04      | ~ v1_relat_1(X0)
% 1.42/1.04      | v1_relat_1(k2_funct_1(X0)) ),
% 1.42/1.04      inference(cnf_transformation,[],[f53]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1500,plain,
% 1.42/1.04      ( ~ v1_funct_1(sK2)
% 1.42/1.04      | ~ v2_funct_1(sK2)
% 1.42/1.04      | v1_relat_1(k2_funct_1(sK2))
% 1.42/1.04      | ~ v1_relat_1(sK2) ),
% 1.42/1.04      inference(instantiation,[status(thm)],[c_5]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1609,plain,
% 1.42/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
% 1.42/1.04      | ~ v1_funct_1(k2_funct_1(sK2))
% 1.42/1.04      | ~ v1_relat_1(k2_funct_1(sK2)) ),
% 1.42/1.04      inference(instantiation,[status(thm)],[c_24]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_2434,plain,
% 1.42/1.04      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
% 1.42/1.04      | k2_relset_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 1.42/1.04      inference(instantiation,[status(thm)],[c_9]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_3282,plain,
% 1.42/1.04      ( k2_relset_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 1.42/1.04      inference(global_propositional_subsumption,
% 1.42/1.04                [status(thm)],
% 1.42/1.04                [c_3222,c_35,c_33,c_31,c_1497,c_1500,c_1609,c_1786,
% 1.42/1.04                 c_1956,c_2434]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_3698,plain,
% 1.42/1.04      ( k2_relset_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 1.42/1.04      inference(demodulation,[status(thm)],[c_3694,c_3282]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_6,plain,
% 1.42/1.04      ( ~ v1_funct_1(X0)
% 1.42/1.04      | ~ v2_funct_1(X0)
% 1.42/1.04      | ~ v1_relat_1(X0)
% 1.42/1.04      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 1.42/1.04      inference(cnf_transformation,[],[f57]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1214,plain,
% 1.42/1.04      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 1.42/1.04      | v1_funct_1(X0) != iProver_top
% 1.42/1.04      | v2_funct_1(X0) != iProver_top
% 1.42/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_3562,plain,
% 1.42/1.04      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 1.42/1.04      | v2_funct_1(sK2) != iProver_top
% 1.42/1.04      | v1_relat_1(sK2) != iProver_top ),
% 1.42/1.04      inference(superposition,[status(thm)],[c_1192,c_1214]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1526,plain,
% 1.42/1.04      ( ~ v1_funct_1(sK2)
% 1.42/1.04      | ~ v2_funct_1(sK2)
% 1.42/1.04      | ~ v1_relat_1(sK2)
% 1.42/1.04      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.42/1.04      inference(instantiation,[status(thm)],[c_6]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_3720,plain,
% 1.42/1.04      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.42/1.04      inference(global_propositional_subsumption,
% 1.42/1.04                [status(thm)],
% 1.42/1.04                [c_3562,c_35,c_33,c_31,c_1526,c_1786,c_1956]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_3929,plain,
% 1.42/1.04      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.42/1.04      inference(light_normalisation,[status(thm)],[c_3698,c_3720]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_21,plain,
% 1.42/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 1.42/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.42/1.04      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 1.42/1.04      | ~ v1_funct_1(X0)
% 1.42/1.04      | ~ v2_funct_1(X0)
% 1.42/1.04      | k2_relset_1(X1,X2,X0) != X2 ),
% 1.42/1.04      inference(cnf_transformation,[],[f73]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1201,plain,
% 1.42/1.04      ( k2_relset_1(X0,X1,X2) != X1
% 1.42/1.04      | v1_funct_2(X2,X0,X1) != iProver_top
% 1.42/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.42/1.04      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 1.42/1.04      | v1_funct_1(X2) != iProver_top
% 1.42/1.04      | v2_funct_1(X2) != iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_4095,plain,
% 1.42/1.04      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 1.42/1.04      | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
% 1.42/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 1.42/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.42/1.04      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 1.42/1.04      inference(superposition,[status(thm)],[c_3929,c_1201]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_8,plain,
% 1.42/1.04      ( ~ v1_funct_1(X0)
% 1.42/1.04      | ~ v2_funct_1(X0)
% 1.42/1.04      | ~ v1_relat_1(X0)
% 1.42/1.04      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 1.42/1.04      inference(cnf_transformation,[],[f58]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1212,plain,
% 1.42/1.04      ( k2_funct_1(k2_funct_1(X0)) = X0
% 1.42/1.04      | v1_funct_1(X0) != iProver_top
% 1.42/1.04      | v2_funct_1(X0) != iProver_top
% 1.42/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_2709,plain,
% 1.42/1.04      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 1.42/1.04      | v2_funct_1(sK2) != iProver_top
% 1.42/1.04      | v1_relat_1(sK2) != iProver_top ),
% 1.42/1.04      inference(superposition,[status(thm)],[c_1192,c_1212]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1532,plain,
% 1.42/1.04      ( ~ v1_funct_1(sK2)
% 1.42/1.04      | ~ v2_funct_1(sK2)
% 1.42/1.04      | ~ v1_relat_1(sK2)
% 1.42/1.04      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 1.42/1.04      inference(instantiation,[status(thm)],[c_8]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_2976,plain,
% 1.42/1.04      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 1.42/1.04      inference(global_propositional_subsumption,
% 1.42/1.04                [status(thm)],
% 1.42/1.04                [c_2709,c_35,c_33,c_31,c_1532,c_1786,c_1956]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_4101,plain,
% 1.42/1.04      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 1.42/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 1.42/1.04      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
% 1.42/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.42/1.04      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 1.42/1.04      inference(light_normalisation,[status(thm)],[c_4095,c_2976]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1523,plain,
% 1.42/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 1.42/1.04      | ~ v1_funct_1(sK2)
% 1.42/1.04      | ~ v1_relat_1(sK2) ),
% 1.42/1.04      inference(instantiation,[status(thm)],[c_24]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1524,plain,
% 1.42/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
% 1.42/1.04      | v1_funct_1(sK2) != iProver_top
% 1.42/1.04      | v1_relat_1(sK2) != iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_1523]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_4634,plain,
% 1.42/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 1.42/1.04      inference(global_propositional_subsumption,
% 1.42/1.04                [status(thm)],
% 1.42/1.04                [c_4101,c_42,c_44,c_1524,c_1787,c_1957]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_4641,plain,
% 1.42/1.04      ( k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,k2_relat_1(sK2)) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
% 1.42/1.04      inference(superposition,[status(thm)],[c_4634,c_1209]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_2137,plain,
% 1.42/1.04      ( k8_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0,X1) = k10_relat_1(X0,X1)
% 1.42/1.04      | v1_funct_1(X0) != iProver_top
% 1.42/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.42/1.04      inference(superposition,[status(thm)],[c_1198,c_1210]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_4322,plain,
% 1.42/1.04      ( k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0)
% 1.42/1.04      | v1_relat_1(sK2) != iProver_top ),
% 1.42/1.04      inference(superposition,[status(thm)],[c_1192,c_2137]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_2364,plain,
% 1.42/1.04      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 1.42/1.04      | k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0) ),
% 1.42/1.04      inference(instantiation,[status(thm)],[c_10]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_4421,plain,
% 1.42/1.04      ( k8_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0) ),
% 1.42/1.04      inference(global_propositional_subsumption,
% 1.42/1.04                [status(thm)],
% 1.42/1.04                [c_4322,c_35,c_33,c_1523,c_1786,c_1956,c_2364]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_4649,plain,
% 1.42/1.04      ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
% 1.42/1.04      inference(demodulation,[status(thm)],[c_4641,c_4421]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_4242,plain,
% 1.42/1.04      ( k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
% 1.42/1.04      | k2_relat_1(X0) = k1_xboole_0
% 1.42/1.04      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) != iProver_top
% 1.42/1.04      | v1_funct_1(X0) != iProver_top
% 1.42/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.42/1.04      inference(superposition,[status(thm)],[c_1198,c_1202]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_25,plain,
% 1.42/1.04      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 1.42/1.04      | ~ v1_funct_1(X0)
% 1.42/1.04      | ~ v1_relat_1(X0) ),
% 1.42/1.04      inference(cnf_transformation,[],[f75]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_57,plain,
% 1.42/1.04      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
% 1.42/1.04      | v1_funct_1(X0) != iProver_top
% 1.42/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_4918,plain,
% 1.42/1.04      ( k2_relat_1(X0) = k1_xboole_0
% 1.42/1.04      | k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
% 1.42/1.04      | v1_funct_1(X0) != iProver_top
% 1.42/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.42/1.04      inference(global_propositional_subsumption,
% 1.42/1.04                [status(thm)],
% 1.42/1.04                [c_4242,c_57]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_4919,plain,
% 1.42/1.04      ( k1_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k1_relat_1(X0)
% 1.42/1.04      | k2_relat_1(X0) = k1_xboole_0
% 1.42/1.04      | v1_funct_1(X0) != iProver_top
% 1.42/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.42/1.04      inference(renaming,[status(thm)],[c_4918]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_4929,plain,
% 1.42/1.04      ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k1_relat_1(sK2)
% 1.42/1.04      | k2_relat_1(sK2) = k1_xboole_0
% 1.42/1.04      | v1_relat_1(sK2) != iProver_top ),
% 1.42/1.04      inference(superposition,[status(thm)],[c_1192,c_4919]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_4963,plain,
% 1.42/1.04      ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k1_relat_1(sK2) ),
% 1.42/1.04      inference(global_propositional_subsumption,
% 1.42/1.04                [status(thm)],
% 1.42/1.04                [c_4929,c_44,c_1787,c_1820,c_1957]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_5079,plain,
% 1.42/1.04      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 1.42/1.04      inference(light_normalisation,[status(thm)],[c_4649,c_4963]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_7196,plain,
% 1.42/1.04      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 1.42/1.04      inference(light_normalisation,[status(thm)],[c_7194,c_5079]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_19,plain,
% 1.42/1.04      ( r2_funct_2(X0,X1,X2,X2)
% 1.42/1.04      | ~ v1_funct_2(X2,X0,X1)
% 1.42/1.04      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.42/1.04      | ~ v1_funct_1(X2) ),
% 1.42/1.04      inference(cnf_transformation,[],[f94]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_30,negated_conjecture,
% 1.42/1.04      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 1.42/1.04      inference(cnf_transformation,[],[f88]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_460,plain,
% 1.42/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 1.42/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.42/1.04      | ~ v1_funct_1(X0)
% 1.42/1.04      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 1.42/1.04      | u1_struct_0(sK1) != X2
% 1.42/1.04      | u1_struct_0(sK0) != X1
% 1.42/1.04      | sK2 != X0 ),
% 1.42/1.04      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_461,plain,
% 1.42/1.04      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 1.42/1.04      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.42/1.04      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 1.42/1.04      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 1.42/1.04      inference(unflattening,[status(thm)],[c_460]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1191,plain,
% 1.42/1.04      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 1.42/1.04      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 1.42/1.04      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 1.42/1.04      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_461]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1413,plain,
% 1.42/1.04      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 1.42/1.04      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 1.42/1.04      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 1.42/1.04      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 1.42/1.04      inference(light_normalisation,[status(thm)],[c_1191,c_447,c_452]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_29,plain,
% 1.42/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 1.42/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.42/1.04      | ~ v1_funct_1(X0)
% 1.42/1.04      | ~ v2_funct_1(X0)
% 1.42/1.04      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 1.42/1.04      | k2_relset_1(X1,X2,X0) != X2 ),
% 1.42/1.04      inference(cnf_transformation,[],[f79]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1196,plain,
% 1.42/1.04      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
% 1.42/1.04      | k2_relset_1(X0,X1,X2) != X1
% 1.42/1.04      | v1_funct_2(X2,X0,X1) != iProver_top
% 1.42/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.42/1.04      | v1_funct_1(X2) != iProver_top
% 1.42/1.04      | v2_funct_1(X2) != iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1593,plain,
% 1.42/1.04      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 1.42/1.04      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 1.42/1.04      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 1.42/1.04      | v1_funct_1(sK2) != iProver_top
% 1.42/1.04      | v2_funct_1(sK2) != iProver_top ),
% 1.42/1.04      inference(superposition,[status(thm)],[c_1235,c_1196]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1732,plain,
% 1.42/1.04      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 1.42/1.04      inference(global_propositional_subsumption,
% 1.42/1.04                [status(thm)],
% 1.42/1.04                [c_1593,c_42,c_45,c_1238,c_1232]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1777,plain,
% 1.42/1.04      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 1.42/1.04      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 1.42/1.04      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 1.42/1.04      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 1.42/1.04      inference(light_normalisation,[status(thm)],[c_1413,c_1732]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1815,plain,
% 1.42/1.04      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 1.42/1.04      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 1.42/1.04      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 1.42/1.04      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 1.42/1.04      inference(demodulation,[status(thm)],[c_1784,c_1777]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_7207,plain,
% 1.42/1.04      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 1.42/1.04      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 1.42/1.04      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 1.42/1.04      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 1.42/1.04      inference(demodulation,[status(thm)],[c_7196,c_1815]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_3286,plain,
% 1.42/1.04      ( k2_tops_2(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 1.42/1.04      | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) != iProver_top
% 1.42/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) != iProver_top
% 1.42/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.42/1.04      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 1.42/1.04      inference(superposition,[status(thm)],[c_3282,c_1196]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_3292,plain,
% 1.42/1.04      ( k2_tops_2(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = sK2
% 1.42/1.04      | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) != iProver_top
% 1.42/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) != iProver_top
% 1.42/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.42/1.04      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 1.42/1.04      inference(light_normalisation,[status(thm)],[c_3286,c_2976]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_3,plain,
% 1.42/1.04      ( ~ v1_funct_1(X0)
% 1.42/1.04      | ~ v2_funct_1(X0)
% 1.42/1.04      | v2_funct_1(k2_funct_1(X0))
% 1.42/1.04      | ~ v1_relat_1(X0) ),
% 1.42/1.04      inference(cnf_transformation,[],[f55]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1494,plain,
% 1.42/1.04      ( ~ v1_funct_1(sK2)
% 1.42/1.04      | v2_funct_1(k2_funct_1(sK2))
% 1.42/1.04      | ~ v2_funct_1(sK2)
% 1.42/1.04      | ~ v1_relat_1(sK2) ),
% 1.42/1.04      inference(instantiation,[status(thm)],[c_3]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1495,plain,
% 1.42/1.04      ( v1_funct_1(sK2) != iProver_top
% 1.42/1.04      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 1.42/1.04      | v2_funct_1(sK2) != iProver_top
% 1.42/1.04      | v1_relat_1(sK2) != iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_1494]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1501,plain,
% 1.42/1.04      ( v1_funct_1(sK2) != iProver_top
% 1.42/1.04      | v2_funct_1(sK2) != iProver_top
% 1.42/1.04      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 1.42/1.04      | v1_relat_1(sK2) != iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_1500]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1610,plain,
% 1.42/1.04      ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
% 1.42/1.04      | ~ v1_funct_1(k2_funct_1(sK2))
% 1.42/1.04      | ~ v1_relat_1(k2_funct_1(sK2)) ),
% 1.42/1.04      inference(instantiation,[status(thm)],[c_25]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1625,plain,
% 1.42/1.04      ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) = iProver_top
% 1.42/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.42/1.04      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_1610]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1627,plain,
% 1.42/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) = iProver_top
% 1.42/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.42/1.04      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_1609]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_3352,plain,
% 1.42/1.04      ( k2_tops_2(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = sK2 ),
% 1.42/1.04      inference(global_propositional_subsumption,
% 1.42/1.04                [status(thm)],
% 1.42/1.04                [c_3292,c_42,c_44,c_45,c_1495,c_1498,c_1501,c_1625,
% 1.42/1.04                 c_1627,c_1787,c_1957]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_3697,plain,
% 1.42/1.04      ( k2_tops_2(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = sK2 ),
% 1.42/1.04      inference(demodulation,[status(thm)],[c_3694,c_3352]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_3927,plain,
% 1.42/1.04      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 1.42/1.04      inference(light_normalisation,[status(thm)],[c_3697,c_3720]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_7219,plain,
% 1.42/1.04      ( sK2 != sK2
% 1.42/1.04      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 1.42/1.04      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 1.42/1.04      | v1_funct_1(sK2) != iProver_top ),
% 1.42/1.04      inference(light_normalisation,[status(thm)],[c_7207,c_3927]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_7220,plain,
% 1.42/1.04      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 1.42/1.04      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 1.42/1.04      | v1_funct_1(sK2) != iProver_top ),
% 1.42/1.04      inference(equality_resolution_simp,[status(thm)],[c_7219]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1520,plain,
% 1.42/1.04      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
% 1.42/1.04      | ~ v1_funct_1(sK2)
% 1.42/1.04      | ~ v1_relat_1(sK2) ),
% 1.42/1.04      inference(instantiation,[status(thm)],[c_25]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(c_1521,plain,
% 1.42/1.04      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top
% 1.42/1.04      | v1_funct_1(sK2) != iProver_top
% 1.42/1.04      | v1_relat_1(sK2) != iProver_top ),
% 1.42/1.04      inference(predicate_to_equality,[status(thm)],[c_1520]) ).
% 1.42/1.04  
% 1.42/1.04  cnf(contradiction,plain,
% 1.42/1.04      ( $false ),
% 1.42/1.04      inference(minisat,
% 1.42/1.04                [status(thm)],
% 1.42/1.04                [c_7220,c_1957,c_1787,c_1524,c_1521,c_44,c_42]) ).
% 1.42/1.04  
% 1.42/1.04  
% 1.42/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 1.42/1.04  
% 1.42/1.04  ------                               Statistics
% 1.42/1.04  
% 1.42/1.04  ------ General
% 1.42/1.04  
% 1.42/1.04  abstr_ref_over_cycles:                  0
% 1.42/1.04  abstr_ref_under_cycles:                 0
% 1.42/1.04  gc_basic_clause_elim:                   0
% 1.42/1.04  forced_gc_time:                         0
% 1.42/1.04  parsing_time:                           0.031
% 1.42/1.04  unif_index_cands_time:                  0.
% 1.42/1.04  unif_index_add_time:                    0.
% 1.42/1.04  orderings_time:                         0.
% 1.42/1.04  out_proof_time:                         0.014
% 1.42/1.04  total_time:                             0.257
% 1.42/1.04  num_of_symbols:                         57
% 1.42/1.04  num_of_terms:                           6181
% 1.42/1.04  
% 1.42/1.04  ------ Preprocessing
% 1.42/1.04  
% 1.42/1.04  num_of_splits:                          0
% 1.42/1.04  num_of_split_atoms:                     0
% 1.42/1.04  num_of_reused_defs:                     0
% 1.42/1.04  num_eq_ax_congr_red:                    36
% 1.42/1.04  num_of_sem_filtered_clauses:            1
% 1.42/1.04  num_of_subtypes:                        0
% 1.42/1.04  monotx_restored_types:                  0
% 1.42/1.04  sat_num_of_epr_types:                   0
% 1.42/1.04  sat_num_of_non_cyclic_types:            0
% 1.42/1.04  sat_guarded_non_collapsed_types:        0
% 1.42/1.04  num_pure_diseq_elim:                    0
% 1.42/1.04  simp_replaced_by:                       0
% 1.42/1.04  res_preprocessed:                       172
% 1.42/1.04  prep_upred:                             0
% 1.42/1.04  prep_unflattend:                        10
% 1.42/1.04  smt_new_axioms:                         0
% 1.42/1.04  pred_elim_cands:                        5
% 1.42/1.04  pred_elim:                              4
% 1.42/1.04  pred_elim_cl:                           5
% 1.42/1.04  pred_elim_cycles:                       6
% 1.42/1.04  merged_defs:                            0
% 1.42/1.04  merged_defs_ncl:                        0
% 1.42/1.04  bin_hyper_res:                          0
% 1.42/1.04  prep_cycles:                            4
% 1.42/1.04  pred_elim_time:                         0.003
% 1.42/1.04  splitting_time:                         0.
% 1.42/1.04  sem_filter_time:                        0.
% 1.42/1.04  monotx_time:                            0.001
% 1.42/1.04  subtype_inf_time:                       0.
% 1.42/1.04  
% 1.42/1.04  ------ Problem properties
% 1.42/1.04  
% 1.42/1.04  clauses:                                33
% 1.42/1.04  conjectures:                            5
% 1.42/1.04  epr:                                    2
% 1.42/1.04  horn:                                   29
% 1.42/1.04  ground:                                 9
% 1.42/1.04  unary:                                  9
% 1.42/1.04  binary:                                 4
% 1.42/1.04  lits:                                   99
% 1.42/1.04  lits_eq:                                26
% 1.42/1.04  fd_pure:                                0
% 1.42/1.04  fd_pseudo:                              0
% 1.42/1.04  fd_cond:                                3
% 1.42/1.04  fd_pseudo_cond:                         0
% 1.42/1.04  ac_symbols:                             0
% 1.42/1.04  
% 1.42/1.04  ------ Propositional Solver
% 1.42/1.04  
% 1.42/1.04  prop_solver_calls:                      29
% 1.42/1.04  prop_fast_solver_calls:                 1358
% 1.42/1.04  smt_solver_calls:                       0
% 1.42/1.04  smt_fast_solver_calls:                  0
% 1.42/1.04  prop_num_of_clauses:                    2250
% 1.42/1.04  prop_preprocess_simplified:             6890
% 1.42/1.04  prop_fo_subsumed:                       80
% 1.42/1.04  prop_solver_time:                       0.
% 1.42/1.04  smt_solver_time:                        0.
% 1.42/1.04  smt_fast_solver_time:                   0.
% 1.42/1.04  prop_fast_solver_time:                  0.
% 1.42/1.04  prop_unsat_core_time:                   0.
% 1.42/1.04  
% 1.42/1.04  ------ QBF
% 1.42/1.04  
% 1.42/1.04  qbf_q_res:                              0
% 1.42/1.04  qbf_num_tautologies:                    0
% 1.42/1.04  qbf_prep_cycles:                        0
% 1.42/1.04  
% 1.42/1.04  ------ BMC1
% 1.42/1.04  
% 1.42/1.04  bmc1_current_bound:                     -1
% 1.42/1.04  bmc1_last_solved_bound:                 -1
% 1.42/1.04  bmc1_unsat_core_size:                   -1
% 1.42/1.04  bmc1_unsat_core_parents_size:           -1
% 1.42/1.04  bmc1_merge_next_fun:                    0
% 1.42/1.04  bmc1_unsat_core_clauses_time:           0.
% 1.42/1.04  
% 1.42/1.04  ------ Instantiation
% 1.42/1.04  
% 1.42/1.04  inst_num_of_clauses:                    820
% 1.42/1.04  inst_num_in_passive:                    19
% 1.42/1.04  inst_num_in_active:                     415
% 1.42/1.04  inst_num_in_unprocessed:                386
% 1.42/1.04  inst_num_of_loops:                      450
% 1.42/1.04  inst_num_of_learning_restarts:          0
% 1.42/1.04  inst_num_moves_active_passive:          31
% 1.42/1.04  inst_lit_activity:                      0
% 1.42/1.04  inst_lit_activity_moves:                0
% 1.42/1.04  inst_num_tautologies:                   0
% 1.42/1.04  inst_num_prop_implied:                  0
% 1.42/1.04  inst_num_existing_simplified:           0
% 1.42/1.04  inst_num_eq_res_simplified:             0
% 1.42/1.04  inst_num_child_elim:                    0
% 1.42/1.04  inst_num_of_dismatching_blockings:      119
% 1.42/1.04  inst_num_of_non_proper_insts:           608
% 1.42/1.04  inst_num_of_duplicates:                 0
% 1.42/1.04  inst_inst_num_from_inst_to_res:         0
% 1.42/1.04  inst_dismatching_checking_time:         0.
% 1.42/1.04  
% 1.42/1.04  ------ Resolution
% 1.42/1.04  
% 1.42/1.04  res_num_of_clauses:                     0
% 1.42/1.04  res_num_in_passive:                     0
% 1.42/1.04  res_num_in_active:                      0
% 1.42/1.04  res_num_of_loops:                       176
% 1.42/1.04  res_forward_subset_subsumed:            70
% 1.42/1.04  res_backward_subset_subsumed:           0
% 1.42/1.04  res_forward_subsumed:                   0
% 1.42/1.04  res_backward_subsumed:                  0
% 1.42/1.04  res_forward_subsumption_resolution:     0
% 1.42/1.04  res_backward_subsumption_resolution:    0
% 1.42/1.04  res_clause_to_clause_subsumption:       214
% 1.42/1.04  res_orphan_elimination:                 0
% 1.42/1.04  res_tautology_del:                      60
% 1.42/1.04  res_num_eq_res_simplified:              0
% 1.42/1.04  res_num_sel_changes:                    0
% 1.42/1.04  res_moves_from_active_to_pass:          0
% 1.42/1.04  
% 1.42/1.04  ------ Superposition
% 1.42/1.04  
% 1.42/1.04  sup_time_total:                         0.
% 1.42/1.04  sup_time_generating:                    0.
% 1.42/1.04  sup_time_sim_full:                      0.
% 1.42/1.04  sup_time_sim_immed:                     0.
% 1.42/1.04  
% 1.42/1.04  sup_num_of_clauses:                     76
% 1.42/1.04  sup_num_in_active:                      62
% 1.42/1.04  sup_num_in_passive:                     14
% 1.42/1.04  sup_num_of_loops:                       88
% 1.42/1.04  sup_fw_superposition:                   52
% 1.42/1.04  sup_bw_superposition:                   55
% 1.42/1.04  sup_immediate_simplified:               65
% 1.42/1.04  sup_given_eliminated:                   0
% 1.42/1.04  comparisons_done:                       0
% 1.42/1.04  comparisons_avoided:                    9
% 1.42/1.04  
% 1.42/1.04  ------ Simplifications
% 1.42/1.04  
% 1.42/1.04  
% 1.42/1.04  sim_fw_subset_subsumed:                 18
% 1.42/1.04  sim_bw_subset_subsumed:                 5
% 1.42/1.04  sim_fw_subsumed:                        5
% 1.42/1.04  sim_bw_subsumed:                        0
% 1.42/1.04  sim_fw_subsumption_res:                 0
% 1.42/1.04  sim_bw_subsumption_res:                 0
% 1.42/1.04  sim_tautology_del:                      1
% 1.42/1.04  sim_eq_tautology_del:                   13
% 1.42/1.04  sim_eq_res_simp:                        2
% 1.42/1.04  sim_fw_demodulated:                     11
% 1.42/1.04  sim_bw_demodulated:                     26
% 1.42/1.04  sim_light_normalised:                   51
% 1.42/1.04  sim_joinable_taut:                      0
% 1.42/1.04  sim_joinable_simp:                      0
% 1.42/1.04  sim_ac_normalised:                      0
% 1.42/1.04  sim_smt_subsumption:                    0
% 1.42/1.04  
%------------------------------------------------------------------------------
