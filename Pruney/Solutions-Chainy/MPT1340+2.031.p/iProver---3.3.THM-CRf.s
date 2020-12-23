%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:27 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :  167 (1351 expanded)
%              Number of clauses        :   95 ( 359 expanded)
%              Number of leaves         :   19 ( 411 expanded)
%              Depth                    :   20
%              Number of atoms          :  600 (9174 expanded)
%              Number of equality atoms :  243 (1588 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f45,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f44,f43,f42])).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f68,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f74,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f78,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f77,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
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

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f75,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f72,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f51,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f49,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
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

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f64])).

fof(f79,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1075,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_22,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_31,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_406,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_31])).

cnf(c_407,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_33,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_411,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_412,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_1113,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1075,c_407,c_412])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1090,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1441,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1113,c_1090])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1092,plain,
    ( k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2557,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0)
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1441,c_1092])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_26,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1330,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1398,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3418,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2557,c_30,c_28,c_26,c_1330,c_1398])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1110,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_27,c_407,c_412])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1079,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2927,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1110,c_1079])).

cnf(c_37,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_40,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1074,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1107,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1074,c_407,c_412])).

cnf(c_3025,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2927,c_37,c_40,c_1107,c_1113])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1086,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3032,plain,
    ( k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),k2_struct_0(sK1)) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3025,c_1086])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1089,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3033,plain,
    ( k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X0) = k9_relat_1(k2_funct_1(sK2),X0) ),
    inference(superposition,[status(thm)],[c_3025,c_1089])).

cnf(c_3047,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k9_relat_1(k2_funct_1(sK2),k2_struct_0(sK1)) ),
    inference(demodulation,[status(thm)],[c_3032,c_3033])).

cnf(c_3423,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k10_relat_1(sK2,k2_struct_0(sK1)) ),
    inference(demodulation,[status(thm)],[c_3418,c_3047])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1080,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2687,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1113,c_1080])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1087,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2032,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(superposition,[status(thm)],[c_1113,c_1087])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1088,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1534,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1113,c_1088])).

cnf(c_2033,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k10_relat_1(sK2,k2_struct_0(sK1)) ),
    inference(demodulation,[status(thm)],[c_2032,c_1534])).

cnf(c_2688,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) = k2_struct_0(sK0)
    | k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2687,c_2033])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_23,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_379,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_23])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_397,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_379,c_32])).

cnf(c_398,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_400,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_398,c_31])).

cnf(c_1104,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_400,c_407])).

cnf(c_3906,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2688,c_1107,c_1104])).

cnf(c_4100,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_3423,c_3906])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1077,plain,
    ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4104,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4100,c_1077])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1091,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2039,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1441,c_1091])).

cnf(c_1399,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2344,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2039,c_30,c_28,c_26,c_1330,c_1399])).

cnf(c_4110,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4104,c_2344])).

cnf(c_39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1331,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1330])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1403,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1404,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1403])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1402,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1406,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1402])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1078,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2634,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1110,c_1078])).

cnf(c_4636,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4110,c_37,c_39,c_40,c_1107,c_1113,c_1331,c_1404,c_1406,c_2634,c_2927])).

cnf(c_1953,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1110,c_1077])).

cnf(c_2239,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1953,c_37,c_40,c_1107,c_1113])).

cnf(c_17,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_25,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_420,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_421,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_1071,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_421])).

cnf(c_1262,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1071,c_407,c_412])).

cnf(c_2242,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2239,c_1262])).

cnf(c_4639,plain,
    ( sK2 != sK2
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4636,c_2242])).

cnf(c_614,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1498,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_614])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4639,c_1498,c_1113,c_1107,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:21:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.67/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/0.98  
% 2.67/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.67/0.98  
% 2.67/0.98  ------  iProver source info
% 2.67/0.98  
% 2.67/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.67/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.67/0.98  git: non_committed_changes: false
% 2.67/0.98  git: last_make_outside_of_git: false
% 2.67/0.98  
% 2.67/0.98  ------ 
% 2.67/0.98  
% 2.67/0.98  ------ Input Options
% 2.67/0.98  
% 2.67/0.98  --out_options                           all
% 2.67/0.98  --tptp_safe_out                         true
% 2.67/0.98  --problem_path                          ""
% 2.67/0.98  --include_path                          ""
% 2.67/0.98  --clausifier                            res/vclausify_rel
% 2.67/0.98  --clausifier_options                    --mode clausify
% 2.67/0.98  --stdin                                 false
% 2.67/0.98  --stats_out                             all
% 2.67/0.98  
% 2.67/0.98  ------ General Options
% 2.67/0.98  
% 2.67/0.98  --fof                                   false
% 2.67/0.98  --time_out_real                         305.
% 2.67/0.98  --time_out_virtual                      -1.
% 2.67/0.98  --symbol_type_check                     false
% 2.67/0.98  --clausify_out                          false
% 2.67/0.98  --sig_cnt_out                           false
% 2.67/0.98  --trig_cnt_out                          false
% 2.67/0.98  --trig_cnt_out_tolerance                1.
% 2.67/0.98  --trig_cnt_out_sk_spl                   false
% 2.67/0.98  --abstr_cl_out                          false
% 2.67/0.98  
% 2.67/0.98  ------ Global Options
% 2.67/0.98  
% 2.67/0.98  --schedule                              default
% 2.67/0.98  --add_important_lit                     false
% 2.67/0.98  --prop_solver_per_cl                    1000
% 2.67/0.98  --min_unsat_core                        false
% 2.67/0.98  --soft_assumptions                      false
% 2.67/0.98  --soft_lemma_size                       3
% 2.67/0.98  --prop_impl_unit_size                   0
% 2.67/0.98  --prop_impl_unit                        []
% 2.67/0.98  --share_sel_clauses                     true
% 2.67/0.98  --reset_solvers                         false
% 2.67/0.98  --bc_imp_inh                            [conj_cone]
% 2.67/0.98  --conj_cone_tolerance                   3.
% 2.67/0.98  --extra_neg_conj                        none
% 2.67/0.98  --large_theory_mode                     true
% 2.67/0.98  --prolific_symb_bound                   200
% 2.67/0.98  --lt_threshold                          2000
% 2.67/0.98  --clause_weak_htbl                      true
% 2.67/0.98  --gc_record_bc_elim                     false
% 2.67/0.98  
% 2.67/0.98  ------ Preprocessing Options
% 2.67/0.98  
% 2.67/0.98  --preprocessing_flag                    true
% 2.67/0.98  --time_out_prep_mult                    0.1
% 2.67/0.98  --splitting_mode                        input
% 2.67/0.98  --splitting_grd                         true
% 2.67/0.98  --splitting_cvd                         false
% 2.67/0.98  --splitting_cvd_svl                     false
% 2.67/0.98  --splitting_nvd                         32
% 2.67/0.98  --sub_typing                            true
% 2.67/0.98  --prep_gs_sim                           true
% 2.67/0.98  --prep_unflatten                        true
% 2.67/0.98  --prep_res_sim                          true
% 2.67/0.98  --prep_upred                            true
% 2.67/0.98  --prep_sem_filter                       exhaustive
% 2.67/0.98  --prep_sem_filter_out                   false
% 2.67/0.98  --pred_elim                             true
% 2.67/0.98  --res_sim_input                         true
% 2.67/0.98  --eq_ax_congr_red                       true
% 2.67/0.98  --pure_diseq_elim                       true
% 2.67/0.98  --brand_transform                       false
% 2.67/0.98  --non_eq_to_eq                          false
% 2.67/0.98  --prep_def_merge                        true
% 2.67/0.98  --prep_def_merge_prop_impl              false
% 2.67/0.98  --prep_def_merge_mbd                    true
% 2.67/0.98  --prep_def_merge_tr_red                 false
% 2.67/0.98  --prep_def_merge_tr_cl                  false
% 2.67/0.98  --smt_preprocessing                     true
% 2.67/0.98  --smt_ac_axioms                         fast
% 2.67/0.98  --preprocessed_out                      false
% 2.67/0.98  --preprocessed_stats                    false
% 2.67/0.98  
% 2.67/0.98  ------ Abstraction refinement Options
% 2.67/0.98  
% 2.67/0.98  --abstr_ref                             []
% 2.67/0.98  --abstr_ref_prep                        false
% 2.67/0.98  --abstr_ref_until_sat                   false
% 2.67/0.98  --abstr_ref_sig_restrict                funpre
% 2.67/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/0.98  --abstr_ref_under                       []
% 2.67/0.98  
% 2.67/0.98  ------ SAT Options
% 2.67/0.98  
% 2.67/0.98  --sat_mode                              false
% 2.67/0.98  --sat_fm_restart_options                ""
% 2.67/0.98  --sat_gr_def                            false
% 2.67/0.98  --sat_epr_types                         true
% 2.67/0.98  --sat_non_cyclic_types                  false
% 2.67/0.98  --sat_finite_models                     false
% 2.67/0.98  --sat_fm_lemmas                         false
% 2.67/0.98  --sat_fm_prep                           false
% 2.67/0.98  --sat_fm_uc_incr                        true
% 2.67/0.98  --sat_out_model                         small
% 2.67/0.98  --sat_out_clauses                       false
% 2.67/0.98  
% 2.67/0.98  ------ QBF Options
% 2.67/0.98  
% 2.67/0.98  --qbf_mode                              false
% 2.67/0.98  --qbf_elim_univ                         false
% 2.67/0.98  --qbf_dom_inst                          none
% 2.67/0.98  --qbf_dom_pre_inst                      false
% 2.67/0.98  --qbf_sk_in                             false
% 2.67/0.98  --qbf_pred_elim                         true
% 2.67/0.98  --qbf_split                             512
% 2.67/0.98  
% 2.67/0.98  ------ BMC1 Options
% 2.67/0.98  
% 2.67/0.98  --bmc1_incremental                      false
% 2.67/0.98  --bmc1_axioms                           reachable_all
% 2.67/0.98  --bmc1_min_bound                        0
% 2.67/0.98  --bmc1_max_bound                        -1
% 2.67/0.98  --bmc1_max_bound_default                -1
% 2.67/0.98  --bmc1_symbol_reachability              true
% 2.67/0.98  --bmc1_property_lemmas                  false
% 2.67/0.98  --bmc1_k_induction                      false
% 2.67/0.98  --bmc1_non_equiv_states                 false
% 2.67/0.98  --bmc1_deadlock                         false
% 2.67/0.98  --bmc1_ucm                              false
% 2.67/0.98  --bmc1_add_unsat_core                   none
% 2.67/0.98  --bmc1_unsat_core_children              false
% 2.67/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/0.98  --bmc1_out_stat                         full
% 2.67/0.98  --bmc1_ground_init                      false
% 2.67/0.98  --bmc1_pre_inst_next_state              false
% 2.67/0.98  --bmc1_pre_inst_state                   false
% 2.67/0.98  --bmc1_pre_inst_reach_state             false
% 2.67/0.98  --bmc1_out_unsat_core                   false
% 2.67/0.98  --bmc1_aig_witness_out                  false
% 2.67/0.98  --bmc1_verbose                          false
% 2.67/0.98  --bmc1_dump_clauses_tptp                false
% 2.67/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.67/0.98  --bmc1_dump_file                        -
% 2.67/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.67/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.67/0.98  --bmc1_ucm_extend_mode                  1
% 2.67/0.98  --bmc1_ucm_init_mode                    2
% 2.67/0.98  --bmc1_ucm_cone_mode                    none
% 2.67/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.67/0.98  --bmc1_ucm_relax_model                  4
% 2.67/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.67/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/0.98  --bmc1_ucm_layered_model                none
% 2.67/0.98  --bmc1_ucm_max_lemma_size               10
% 2.67/0.98  
% 2.67/0.98  ------ AIG Options
% 2.67/0.98  
% 2.67/0.98  --aig_mode                              false
% 2.67/0.98  
% 2.67/0.98  ------ Instantiation Options
% 2.67/0.98  
% 2.67/0.98  --instantiation_flag                    true
% 2.67/0.98  --inst_sos_flag                         false
% 2.67/0.98  --inst_sos_phase                        true
% 2.67/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/0.98  --inst_lit_sel_side                     num_symb
% 2.67/0.98  --inst_solver_per_active                1400
% 2.67/0.98  --inst_solver_calls_frac                1.
% 2.67/0.98  --inst_passive_queue_type               priority_queues
% 2.67/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/0.98  --inst_passive_queues_freq              [25;2]
% 2.67/0.98  --inst_dismatching                      true
% 2.67/0.98  --inst_eager_unprocessed_to_passive     true
% 2.67/0.98  --inst_prop_sim_given                   true
% 2.67/0.98  --inst_prop_sim_new                     false
% 2.67/0.98  --inst_subs_new                         false
% 2.67/0.98  --inst_eq_res_simp                      false
% 2.67/0.98  --inst_subs_given                       false
% 2.67/0.98  --inst_orphan_elimination               true
% 2.67/0.98  --inst_learning_loop_flag               true
% 2.67/0.98  --inst_learning_start                   3000
% 2.67/0.98  --inst_learning_factor                  2
% 2.67/0.98  --inst_start_prop_sim_after_learn       3
% 2.67/0.98  --inst_sel_renew                        solver
% 2.67/0.98  --inst_lit_activity_flag                true
% 2.67/0.98  --inst_restr_to_given                   false
% 2.67/0.98  --inst_activity_threshold               500
% 2.67/0.98  --inst_out_proof                        true
% 2.67/0.98  
% 2.67/0.98  ------ Resolution Options
% 2.67/0.98  
% 2.67/0.98  --resolution_flag                       true
% 2.67/0.98  --res_lit_sel                           adaptive
% 2.67/0.98  --res_lit_sel_side                      none
% 2.67/0.98  --res_ordering                          kbo
% 2.67/0.98  --res_to_prop_solver                    active
% 2.67/0.98  --res_prop_simpl_new                    false
% 2.67/0.98  --res_prop_simpl_given                  true
% 2.67/0.98  --res_passive_queue_type                priority_queues
% 2.67/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/0.98  --res_passive_queues_freq               [15;5]
% 2.67/0.98  --res_forward_subs                      full
% 2.67/0.98  --res_backward_subs                     full
% 2.67/0.98  --res_forward_subs_resolution           true
% 2.67/0.98  --res_backward_subs_resolution          true
% 2.67/0.98  --res_orphan_elimination                true
% 2.67/0.98  --res_time_limit                        2.
% 2.67/0.98  --res_out_proof                         true
% 2.67/0.98  
% 2.67/0.98  ------ Superposition Options
% 2.67/0.98  
% 2.67/0.98  --superposition_flag                    true
% 2.67/0.98  --sup_passive_queue_type                priority_queues
% 2.67/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.67/0.98  --demod_completeness_check              fast
% 2.67/0.98  --demod_use_ground                      true
% 2.67/0.98  --sup_to_prop_solver                    passive
% 2.67/0.98  --sup_prop_simpl_new                    true
% 2.67/0.98  --sup_prop_simpl_given                  true
% 2.67/0.98  --sup_fun_splitting                     false
% 2.67/0.98  --sup_smt_interval                      50000
% 2.67/0.98  
% 2.67/0.98  ------ Superposition Simplification Setup
% 2.67/0.98  
% 2.67/0.98  --sup_indices_passive                   []
% 2.67/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.98  --sup_full_bw                           [BwDemod]
% 2.67/0.98  --sup_immed_triv                        [TrivRules]
% 2.67/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.98  --sup_immed_bw_main                     []
% 2.67/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/0.98  
% 2.67/0.98  ------ Combination Options
% 2.67/0.98  
% 2.67/0.98  --comb_res_mult                         3
% 2.67/0.98  --comb_sup_mult                         2
% 2.67/0.98  --comb_inst_mult                        10
% 2.67/0.98  
% 2.67/0.98  ------ Debug Options
% 2.67/0.98  
% 2.67/0.98  --dbg_backtrace                         false
% 2.67/0.98  --dbg_dump_prop_clauses                 false
% 2.67/0.98  --dbg_dump_prop_clauses_file            -
% 2.67/0.98  --dbg_out_stat                          false
% 2.67/0.98  ------ Parsing...
% 2.67/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.67/0.98  
% 2.67/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.67/0.98  
% 2.67/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.67/0.98  
% 2.67/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.67/0.98  ------ Proving...
% 2.67/0.98  ------ Problem Properties 
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  clauses                                 29
% 2.67/0.98  conjectures                             5
% 2.67/0.98  EPR                                     2
% 2.67/0.98  Horn                                    25
% 2.67/0.98  unary                                   8
% 2.67/0.98  binary                                  5
% 2.67/0.98  lits                                    85
% 2.67/0.98  lits eq                                 24
% 2.67/0.98  fd_pure                                 0
% 2.67/0.98  fd_pseudo                               0
% 2.67/0.98  fd_cond                                 3
% 2.67/0.98  fd_pseudo_cond                          0
% 2.67/0.98  AC symbols                              0
% 2.67/0.98  
% 2.67/0.98  ------ Schedule dynamic 5 is on 
% 2.67/0.98  
% 2.67/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  ------ 
% 2.67/0.98  Current options:
% 2.67/0.98  ------ 
% 2.67/0.98  
% 2.67/0.98  ------ Input Options
% 2.67/0.98  
% 2.67/0.98  --out_options                           all
% 2.67/0.98  --tptp_safe_out                         true
% 2.67/0.98  --problem_path                          ""
% 2.67/0.98  --include_path                          ""
% 2.67/0.98  --clausifier                            res/vclausify_rel
% 2.67/0.98  --clausifier_options                    --mode clausify
% 2.67/0.98  --stdin                                 false
% 2.67/0.98  --stats_out                             all
% 2.67/0.98  
% 2.67/0.98  ------ General Options
% 2.67/0.98  
% 2.67/0.98  --fof                                   false
% 2.67/0.98  --time_out_real                         305.
% 2.67/0.98  --time_out_virtual                      -1.
% 2.67/0.98  --symbol_type_check                     false
% 2.67/0.98  --clausify_out                          false
% 2.67/0.98  --sig_cnt_out                           false
% 2.67/0.98  --trig_cnt_out                          false
% 2.67/0.98  --trig_cnt_out_tolerance                1.
% 2.67/0.98  --trig_cnt_out_sk_spl                   false
% 2.67/0.98  --abstr_cl_out                          false
% 2.67/0.98  
% 2.67/0.98  ------ Global Options
% 2.67/0.98  
% 2.67/0.98  --schedule                              default
% 2.67/0.98  --add_important_lit                     false
% 2.67/0.98  --prop_solver_per_cl                    1000
% 2.67/0.98  --min_unsat_core                        false
% 2.67/0.98  --soft_assumptions                      false
% 2.67/0.98  --soft_lemma_size                       3
% 2.67/0.98  --prop_impl_unit_size                   0
% 2.67/0.98  --prop_impl_unit                        []
% 2.67/0.98  --share_sel_clauses                     true
% 2.67/0.98  --reset_solvers                         false
% 2.67/0.98  --bc_imp_inh                            [conj_cone]
% 2.67/0.98  --conj_cone_tolerance                   3.
% 2.67/0.98  --extra_neg_conj                        none
% 2.67/0.98  --large_theory_mode                     true
% 2.67/0.98  --prolific_symb_bound                   200
% 2.67/0.98  --lt_threshold                          2000
% 2.67/0.98  --clause_weak_htbl                      true
% 2.67/0.98  --gc_record_bc_elim                     false
% 2.67/0.98  
% 2.67/0.98  ------ Preprocessing Options
% 2.67/0.98  
% 2.67/0.98  --preprocessing_flag                    true
% 2.67/0.98  --time_out_prep_mult                    0.1
% 2.67/0.98  --splitting_mode                        input
% 2.67/0.98  --splitting_grd                         true
% 2.67/0.98  --splitting_cvd                         false
% 2.67/0.98  --splitting_cvd_svl                     false
% 2.67/0.98  --splitting_nvd                         32
% 2.67/0.98  --sub_typing                            true
% 2.67/0.98  --prep_gs_sim                           true
% 2.67/0.98  --prep_unflatten                        true
% 2.67/0.98  --prep_res_sim                          true
% 2.67/0.98  --prep_upred                            true
% 2.67/0.98  --prep_sem_filter                       exhaustive
% 2.67/0.98  --prep_sem_filter_out                   false
% 2.67/0.98  --pred_elim                             true
% 2.67/0.98  --res_sim_input                         true
% 2.67/0.98  --eq_ax_congr_red                       true
% 2.67/0.98  --pure_diseq_elim                       true
% 2.67/0.98  --brand_transform                       false
% 2.67/0.98  --non_eq_to_eq                          false
% 2.67/0.98  --prep_def_merge                        true
% 2.67/0.98  --prep_def_merge_prop_impl              false
% 2.67/0.98  --prep_def_merge_mbd                    true
% 2.67/0.98  --prep_def_merge_tr_red                 false
% 2.67/0.98  --prep_def_merge_tr_cl                  false
% 2.67/0.98  --smt_preprocessing                     true
% 2.67/0.98  --smt_ac_axioms                         fast
% 2.67/0.98  --preprocessed_out                      false
% 2.67/0.98  --preprocessed_stats                    false
% 2.67/0.98  
% 2.67/0.98  ------ Abstraction refinement Options
% 2.67/0.98  
% 2.67/0.98  --abstr_ref                             []
% 2.67/0.98  --abstr_ref_prep                        false
% 2.67/0.98  --abstr_ref_until_sat                   false
% 2.67/0.98  --abstr_ref_sig_restrict                funpre
% 2.67/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/0.98  --abstr_ref_under                       []
% 2.67/0.98  
% 2.67/0.98  ------ SAT Options
% 2.67/0.98  
% 2.67/0.98  --sat_mode                              false
% 2.67/0.98  --sat_fm_restart_options                ""
% 2.67/0.98  --sat_gr_def                            false
% 2.67/0.98  --sat_epr_types                         true
% 2.67/0.98  --sat_non_cyclic_types                  false
% 2.67/0.98  --sat_finite_models                     false
% 2.67/0.98  --sat_fm_lemmas                         false
% 2.67/0.98  --sat_fm_prep                           false
% 2.67/0.98  --sat_fm_uc_incr                        true
% 2.67/0.98  --sat_out_model                         small
% 2.67/0.98  --sat_out_clauses                       false
% 2.67/0.98  
% 2.67/0.98  ------ QBF Options
% 2.67/0.98  
% 2.67/0.98  --qbf_mode                              false
% 2.67/0.98  --qbf_elim_univ                         false
% 2.67/0.98  --qbf_dom_inst                          none
% 2.67/0.98  --qbf_dom_pre_inst                      false
% 2.67/0.98  --qbf_sk_in                             false
% 2.67/0.98  --qbf_pred_elim                         true
% 2.67/0.98  --qbf_split                             512
% 2.67/0.98  
% 2.67/0.98  ------ BMC1 Options
% 2.67/0.98  
% 2.67/0.98  --bmc1_incremental                      false
% 2.67/0.98  --bmc1_axioms                           reachable_all
% 2.67/0.98  --bmc1_min_bound                        0
% 2.67/0.98  --bmc1_max_bound                        -1
% 2.67/0.98  --bmc1_max_bound_default                -1
% 2.67/0.98  --bmc1_symbol_reachability              true
% 2.67/0.98  --bmc1_property_lemmas                  false
% 2.67/0.98  --bmc1_k_induction                      false
% 2.67/0.98  --bmc1_non_equiv_states                 false
% 2.67/0.98  --bmc1_deadlock                         false
% 2.67/0.98  --bmc1_ucm                              false
% 2.67/0.98  --bmc1_add_unsat_core                   none
% 2.67/0.98  --bmc1_unsat_core_children              false
% 2.67/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/0.98  --bmc1_out_stat                         full
% 2.67/0.98  --bmc1_ground_init                      false
% 2.67/0.98  --bmc1_pre_inst_next_state              false
% 2.67/0.98  --bmc1_pre_inst_state                   false
% 2.67/0.98  --bmc1_pre_inst_reach_state             false
% 2.67/0.98  --bmc1_out_unsat_core                   false
% 2.67/0.98  --bmc1_aig_witness_out                  false
% 2.67/0.98  --bmc1_verbose                          false
% 2.67/0.98  --bmc1_dump_clauses_tptp                false
% 2.67/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.67/0.98  --bmc1_dump_file                        -
% 2.67/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.67/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.67/0.98  --bmc1_ucm_extend_mode                  1
% 2.67/0.98  --bmc1_ucm_init_mode                    2
% 2.67/0.98  --bmc1_ucm_cone_mode                    none
% 2.67/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.67/0.98  --bmc1_ucm_relax_model                  4
% 2.67/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.67/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/0.98  --bmc1_ucm_layered_model                none
% 2.67/0.98  --bmc1_ucm_max_lemma_size               10
% 2.67/0.98  
% 2.67/0.98  ------ AIG Options
% 2.67/0.98  
% 2.67/0.98  --aig_mode                              false
% 2.67/0.98  
% 2.67/0.98  ------ Instantiation Options
% 2.67/0.98  
% 2.67/0.98  --instantiation_flag                    true
% 2.67/0.98  --inst_sos_flag                         false
% 2.67/0.98  --inst_sos_phase                        true
% 2.67/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/0.98  --inst_lit_sel_side                     none
% 2.67/0.98  --inst_solver_per_active                1400
% 2.67/0.98  --inst_solver_calls_frac                1.
% 2.67/0.98  --inst_passive_queue_type               priority_queues
% 2.67/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/0.98  --inst_passive_queues_freq              [25;2]
% 2.67/0.98  --inst_dismatching                      true
% 2.67/0.98  --inst_eager_unprocessed_to_passive     true
% 2.67/0.98  --inst_prop_sim_given                   true
% 2.67/0.98  --inst_prop_sim_new                     false
% 2.67/0.98  --inst_subs_new                         false
% 2.67/0.98  --inst_eq_res_simp                      false
% 2.67/0.98  --inst_subs_given                       false
% 2.67/0.98  --inst_orphan_elimination               true
% 2.67/0.98  --inst_learning_loop_flag               true
% 2.67/0.98  --inst_learning_start                   3000
% 2.67/0.98  --inst_learning_factor                  2
% 2.67/0.98  --inst_start_prop_sim_after_learn       3
% 2.67/0.98  --inst_sel_renew                        solver
% 2.67/0.98  --inst_lit_activity_flag                true
% 2.67/0.98  --inst_restr_to_given                   false
% 2.67/0.98  --inst_activity_threshold               500
% 2.67/0.98  --inst_out_proof                        true
% 2.67/0.98  
% 2.67/0.98  ------ Resolution Options
% 2.67/0.98  
% 2.67/0.98  --resolution_flag                       false
% 2.67/0.98  --res_lit_sel                           adaptive
% 2.67/0.98  --res_lit_sel_side                      none
% 2.67/0.98  --res_ordering                          kbo
% 2.67/0.98  --res_to_prop_solver                    active
% 2.67/0.98  --res_prop_simpl_new                    false
% 2.67/0.98  --res_prop_simpl_given                  true
% 2.67/0.98  --res_passive_queue_type                priority_queues
% 2.67/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/0.98  --res_passive_queues_freq               [15;5]
% 2.67/0.98  --res_forward_subs                      full
% 2.67/0.98  --res_backward_subs                     full
% 2.67/0.98  --res_forward_subs_resolution           true
% 2.67/0.98  --res_backward_subs_resolution          true
% 2.67/0.98  --res_orphan_elimination                true
% 2.67/0.98  --res_time_limit                        2.
% 2.67/0.98  --res_out_proof                         true
% 2.67/0.98  
% 2.67/0.98  ------ Superposition Options
% 2.67/0.98  
% 2.67/0.98  --superposition_flag                    true
% 2.67/0.98  --sup_passive_queue_type                priority_queues
% 2.67/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.67/0.98  --demod_completeness_check              fast
% 2.67/0.98  --demod_use_ground                      true
% 2.67/0.98  --sup_to_prop_solver                    passive
% 2.67/0.98  --sup_prop_simpl_new                    true
% 2.67/0.98  --sup_prop_simpl_given                  true
% 2.67/0.98  --sup_fun_splitting                     false
% 2.67/0.98  --sup_smt_interval                      50000
% 2.67/0.98  
% 2.67/0.98  ------ Superposition Simplification Setup
% 2.67/0.98  
% 2.67/0.98  --sup_indices_passive                   []
% 2.67/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.98  --sup_full_bw                           [BwDemod]
% 2.67/0.98  --sup_immed_triv                        [TrivRules]
% 2.67/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.98  --sup_immed_bw_main                     []
% 2.67/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/0.98  
% 2.67/0.98  ------ Combination Options
% 2.67/0.98  
% 2.67/0.98  --comb_res_mult                         3
% 2.67/0.98  --comb_sup_mult                         2
% 2.67/0.98  --comb_inst_mult                        10
% 2.67/0.98  
% 2.67/0.98  ------ Debug Options
% 2.67/0.98  
% 2.67/0.98  --dbg_backtrace                         false
% 2.67/0.98  --dbg_dump_prop_clauses                 false
% 2.67/0.98  --dbg_dump_prop_clauses_file            -
% 2.67/0.98  --dbg_out_stat                          false
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  ------ Proving...
% 2.67/0.98  
% 2.67/0.98  
% 2.67/0.98  % SZS status Theorem for theBenchmark.p
% 2.67/0.98  
% 2.67/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.67/0.98  
% 2.67/0.98  fof(f15,conjecture,(
% 2.67/0.98    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f16,negated_conjecture,(
% 2.67/0.98    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.67/0.98    inference(negated_conjecture,[],[f15])).
% 2.67/0.98  
% 2.67/0.98  fof(f38,plain,(
% 2.67/0.98    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.67/0.98    inference(ennf_transformation,[],[f16])).
% 2.67/0.98  
% 2.67/0.98  fof(f39,plain,(
% 2.67/0.98    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.67/0.98    inference(flattening,[],[f38])).
% 2.67/0.98  
% 2.67/0.98  fof(f44,plain,(
% 2.67/0.98    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.67/0.98    introduced(choice_axiom,[])).
% 2.67/0.98  
% 2.67/0.98  fof(f43,plain,(
% 2.67/0.98    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.67/0.98    introduced(choice_axiom,[])).
% 2.67/0.98  
% 2.67/0.98  fof(f42,plain,(
% 2.67/0.98    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.67/0.98    introduced(choice_axiom,[])).
% 2.67/0.98  
% 2.67/0.98  fof(f45,plain,(
% 2.67/0.98    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.67/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f44,f43,f42])).
% 2.67/0.98  
% 2.67/0.98  fof(f76,plain,(
% 2.67/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.67/0.98    inference(cnf_transformation,[],[f45])).
% 2.67/0.98  
% 2.67/0.98  fof(f12,axiom,(
% 2.67/0.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.67/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/0.98  
% 2.67/0.98  fof(f33,plain,(
% 2.67/0.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.67/0.98    inference(ennf_transformation,[],[f12])).
% 2.67/0.98  
% 2.67/0.98  fof(f68,plain,(
% 2.67/0.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.67/0.98    inference(cnf_transformation,[],[f33])).
% 2.67/0.98  
% 2.67/0.98  fof(f73,plain,(
% 2.67/0.98    l1_struct_0(sK1)),
% 2.67/0.98    inference(cnf_transformation,[],[f45])).
% 2.67/0.98  
% 2.67/0.98  fof(f71,plain,(
% 2.67/0.98    l1_struct_0(sK0)),
% 2.67/0.98    inference(cnf_transformation,[],[f45])).
% 2.67/0.98  
% 2.67/0.98  fof(f5,axiom,(
% 2.67/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.67/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f23,plain,(
% 2.67/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/0.99    inference(ennf_transformation,[],[f5])).
% 2.67/0.99  
% 2.67/0.99  fof(f52,plain,(
% 2.67/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/0.99    inference(cnf_transformation,[],[f23])).
% 2.67/0.99  
% 2.67/0.99  fof(f3,axiom,(
% 2.67/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 2.67/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f19,plain,(
% 2.67/0.99    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.67/0.99    inference(ennf_transformation,[],[f3])).
% 2.67/0.99  
% 2.67/0.99  fof(f20,plain,(
% 2.67/0.99    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.67/0.99    inference(flattening,[],[f19])).
% 2.67/0.99  
% 2.67/0.99  fof(f50,plain,(
% 2.67/0.99    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f20])).
% 2.67/0.99  
% 2.67/0.99  fof(f74,plain,(
% 2.67/0.99    v1_funct_1(sK2)),
% 2.67/0.99    inference(cnf_transformation,[],[f45])).
% 2.67/0.99  
% 2.67/0.99  fof(f78,plain,(
% 2.67/0.99    v2_funct_1(sK2)),
% 2.67/0.99    inference(cnf_transformation,[],[f45])).
% 2.67/0.99  
% 2.67/0.99  fof(f77,plain,(
% 2.67/0.99    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.67/0.99    inference(cnf_transformation,[],[f45])).
% 2.67/0.99  
% 2.67/0.99  fof(f11,axiom,(
% 2.67/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.67/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f31,plain,(
% 2.67/0.99    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.67/0.99    inference(ennf_transformation,[],[f11])).
% 2.67/0.99  
% 2.67/0.99  fof(f32,plain,(
% 2.67/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.67/0.99    inference(flattening,[],[f31])).
% 2.67/0.99  
% 2.67/0.99  fof(f67,plain,(
% 2.67/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f32])).
% 2.67/0.99  
% 2.67/0.99  fof(f75,plain,(
% 2.67/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.67/0.99    inference(cnf_transformation,[],[f45])).
% 2.67/0.99  
% 2.67/0.99  fof(f8,axiom,(
% 2.67/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 2.67/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f26,plain,(
% 2.67/0.99    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/0.99    inference(ennf_transformation,[],[f8])).
% 2.67/0.99  
% 2.67/0.99  fof(f55,plain,(
% 2.67/0.99    ( ! [X2,X0,X1] : (k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/0.99    inference(cnf_transformation,[],[f26])).
% 2.67/0.99  
% 2.67/0.99  fof(f6,axiom,(
% 2.67/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.67/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f24,plain,(
% 2.67/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/0.99    inference(ennf_transformation,[],[f6])).
% 2.67/0.99  
% 2.67/0.99  fof(f53,plain,(
% 2.67/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/0.99    inference(cnf_transformation,[],[f24])).
% 2.67/0.99  
% 2.67/0.99  fof(f9,axiom,(
% 2.67/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.67/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f27,plain,(
% 2.67/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/0.99    inference(ennf_transformation,[],[f9])).
% 2.67/0.99  
% 2.67/0.99  fof(f28,plain,(
% 2.67/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/0.99    inference(flattening,[],[f27])).
% 2.67/0.99  
% 2.67/0.99  fof(f40,plain,(
% 2.67/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/0.99    inference(nnf_transformation,[],[f28])).
% 2.67/0.99  
% 2.67/0.99  fof(f57,plain,(
% 2.67/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/0.99    inference(cnf_transformation,[],[f40])).
% 2.67/0.99  
% 2.67/0.99  fof(f56,plain,(
% 2.67/0.99    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/0.99    inference(cnf_transformation,[],[f26])).
% 2.67/0.99  
% 2.67/0.99  fof(f7,axiom,(
% 2.67/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.67/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f25,plain,(
% 2.67/0.99    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/0.99    inference(ennf_transformation,[],[f7])).
% 2.67/0.99  
% 2.67/0.99  fof(f54,plain,(
% 2.67/0.99    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/0.99    inference(cnf_transformation,[],[f25])).
% 2.67/0.99  
% 2.67/0.99  fof(f1,axiom,(
% 2.67/0.99    v1_xboole_0(k1_xboole_0)),
% 2.67/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f46,plain,(
% 2.67/0.99    v1_xboole_0(k1_xboole_0)),
% 2.67/0.99    inference(cnf_transformation,[],[f1])).
% 2.67/0.99  
% 2.67/0.99  fof(f13,axiom,(
% 2.67/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.67/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f34,plain,(
% 2.67/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.67/0.99    inference(ennf_transformation,[],[f13])).
% 2.67/0.99  
% 2.67/0.99  fof(f35,plain,(
% 2.67/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.67/0.99    inference(flattening,[],[f34])).
% 2.67/0.99  
% 2.67/0.99  fof(f69,plain,(
% 2.67/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f35])).
% 2.67/0.99  
% 2.67/0.99  fof(f72,plain,(
% 2.67/0.99    ~v2_struct_0(sK1)),
% 2.67/0.99    inference(cnf_transformation,[],[f45])).
% 2.67/0.99  
% 2.67/0.99  fof(f14,axiom,(
% 2.67/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.67/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f36,plain,(
% 2.67/0.99    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.67/0.99    inference(ennf_transformation,[],[f14])).
% 2.67/0.99  
% 2.67/0.99  fof(f37,plain,(
% 2.67/0.99    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.67/0.99    inference(flattening,[],[f36])).
% 2.67/0.99  
% 2.67/0.99  fof(f70,plain,(
% 2.67/0.99    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f37])).
% 2.67/0.99  
% 2.67/0.99  fof(f4,axiom,(
% 2.67/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.67/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f21,plain,(
% 2.67/0.99    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.67/0.99    inference(ennf_transformation,[],[f4])).
% 2.67/0.99  
% 2.67/0.99  fof(f22,plain,(
% 2.67/0.99    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.67/0.99    inference(flattening,[],[f21])).
% 2.67/0.99  
% 2.67/0.99  fof(f51,plain,(
% 2.67/0.99    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f22])).
% 2.67/0.99  
% 2.67/0.99  fof(f2,axiom,(
% 2.67/0.99    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.67/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f17,plain,(
% 2.67/0.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.67/0.99    inference(ennf_transformation,[],[f2])).
% 2.67/0.99  
% 2.67/0.99  fof(f18,plain,(
% 2.67/0.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.67/0.99    inference(flattening,[],[f17])).
% 2.67/0.99  
% 2.67/0.99  fof(f49,plain,(
% 2.67/0.99    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f18])).
% 2.67/0.99  
% 2.67/0.99  fof(f48,plain,(
% 2.67/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f18])).
% 2.67/0.99  
% 2.67/0.99  fof(f66,plain,(
% 2.67/0.99    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f32])).
% 2.67/0.99  
% 2.67/0.99  fof(f10,axiom,(
% 2.67/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.67/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/0.99  
% 2.67/0.99  fof(f29,plain,(
% 2.67/0.99    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.67/0.99    inference(ennf_transformation,[],[f10])).
% 2.67/0.99  
% 2.67/0.99  fof(f30,plain,(
% 2.67/0.99    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.67/0.99    inference(flattening,[],[f29])).
% 2.67/0.99  
% 2.67/0.99  fof(f41,plain,(
% 2.67/0.99    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.67/0.99    inference(nnf_transformation,[],[f30])).
% 2.67/0.99  
% 2.67/0.99  fof(f64,plain,(
% 2.67/0.99    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.67/0.99    inference(cnf_transformation,[],[f41])).
% 2.67/0.99  
% 2.67/0.99  fof(f85,plain,(
% 2.67/0.99    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.67/0.99    inference(equality_resolution,[],[f64])).
% 2.67/0.99  
% 2.67/0.99  fof(f79,plain,(
% 2.67/0.99    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 2.67/0.99    inference(cnf_transformation,[],[f45])).
% 2.67/0.99  
% 2.67/0.99  cnf(c_28,negated_conjecture,
% 2.67/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.67/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1075,plain,
% 2.67/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_22,plain,
% 2.67/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.67/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_31,negated_conjecture,
% 2.67/0.99      ( l1_struct_0(sK1) ),
% 2.67/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_406,plain,
% 2.67/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_31]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_407,plain,
% 2.67/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_406]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_33,negated_conjecture,
% 2.67/0.99      ( l1_struct_0(sK0) ),
% 2.67/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_411,plain,
% 2.67/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_412,plain,
% 2.67/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_411]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1113,plain,
% 2.67/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.67/0.99      inference(light_normalisation,[status(thm)],[c_1075,c_407,c_412]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_6,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/0.99      | v1_relat_1(X0) ),
% 2.67/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1090,plain,
% 2.67/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.67/0.99      | v1_relat_1(X0) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1441,plain,
% 2.67/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_1113,c_1090]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_4,plain,
% 2.67/0.99      ( ~ v1_relat_1(X0)
% 2.67/0.99      | ~ v1_funct_1(X0)
% 2.67/0.99      | ~ v2_funct_1(X0)
% 2.67/0.99      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
% 2.67/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1092,plain,
% 2.67/0.99      ( k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
% 2.67/0.99      | v1_relat_1(X0) != iProver_top
% 2.67/0.99      | v1_funct_1(X0) != iProver_top
% 2.67/0.99      | v2_funct_1(X0) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2557,plain,
% 2.67/0.99      ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0)
% 2.67/0.99      | v1_funct_1(sK2) != iProver_top
% 2.67/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_1441,c_1092]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_30,negated_conjecture,
% 2.67/0.99      ( v1_funct_1(sK2) ),
% 2.67/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_26,negated_conjecture,
% 2.67/0.99      ( v2_funct_1(sK2) ),
% 2.67/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1330,plain,
% 2.67/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.67/0.99      | v1_relat_1(sK2) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1398,plain,
% 2.67/0.99      ( ~ v1_relat_1(sK2)
% 2.67/0.99      | ~ v1_funct_1(sK2)
% 2.67/0.99      | ~ v2_funct_1(sK2)
% 2.67/0.99      | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_3418,plain,
% 2.67/0.99      ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_2557,c_30,c_28,c_26,c_1330,c_1398]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_27,negated_conjecture,
% 2.67/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.67/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1110,plain,
% 2.67/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.67/0.99      inference(light_normalisation,[status(thm)],[c_27,c_407,c_412]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_19,plain,
% 2.67/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.67/0.99      | ~ v1_funct_1(X0)
% 2.67/0.99      | ~ v2_funct_1(X0)
% 2.67/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.67/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1079,plain,
% 2.67/0.99      ( k2_relset_1(X0,X1,X2) != X1
% 2.67/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.67/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.67/0.99      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 2.67/0.99      | v1_funct_1(X2) != iProver_top
% 2.67/0.99      | v2_funct_1(X2) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2927,plain,
% 2.67/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.67/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 2.67/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.67/0.99      | v1_funct_1(sK2) != iProver_top
% 2.67/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_1110,c_1079]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_37,plain,
% 2.67/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_40,plain,
% 2.67/0.99      ( v2_funct_1(sK2) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_29,negated_conjecture,
% 2.67/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.67/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1074,plain,
% 2.67/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1107,plain,
% 2.67/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.67/0.99      inference(light_normalisation,[status(thm)],[c_1074,c_407,c_412]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_3025,plain,
% 2.67/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_2927,c_37,c_40,c_1107,c_1113]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_10,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/0.99      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 2.67/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1086,plain,
% 2.67/0.99      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 2.67/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_3032,plain,
% 2.67/0.99      ( k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),k2_struct_0(sK1)) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_3025,c_1086]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_7,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.67/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1089,plain,
% 2.67/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.67/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_3033,plain,
% 2.67/0.99      ( k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X0) = k9_relat_1(k2_funct_1(sK2),X0) ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_3025,c_1089]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_3047,plain,
% 2.67/0.99      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k9_relat_1(k2_funct_1(sK2),k2_struct_0(sK1)) ),
% 2.67/0.99      inference(demodulation,[status(thm)],[c_3032,c_3033]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_3423,plain,
% 2.67/0.99      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k10_relat_1(sK2,k2_struct_0(sK1)) ),
% 2.67/0.99      inference(demodulation,[status(thm)],[c_3418,c_3047]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_16,plain,
% 2.67/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.67/0.99      | k1_xboole_0 = X2 ),
% 2.67/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1080,plain,
% 2.67/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 2.67/0.99      | k1_xboole_0 = X1
% 2.67/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.67/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2687,plain,
% 2.67/0.99      ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK0)
% 2.67/0.99      | k2_struct_0(sK1) = k1_xboole_0
% 2.67/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_1113,c_1080]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_9,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/0.99      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 2.67/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1087,plain,
% 2.67/0.99      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 2.67/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2032,plain,
% 2.67/0.99      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_1113,c_1087]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_8,plain,
% 2.67/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/0.99      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.67/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1088,plain,
% 2.67/0.99      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 2.67/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1534,plain,
% 2.67/0.99      ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0) ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_1113,c_1088]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2033,plain,
% 2.67/0.99      ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k10_relat_1(sK2,k2_struct_0(sK1)) ),
% 2.67/0.99      inference(demodulation,[status(thm)],[c_2032,c_1534]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2688,plain,
% 2.67/0.99      ( k10_relat_1(sK2,k2_struct_0(sK1)) = k2_struct_0(sK0)
% 2.67/0.99      | k2_struct_0(sK1) = k1_xboole_0
% 2.67/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top ),
% 2.67/0.99      inference(demodulation,[status(thm)],[c_2687,c_2033]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_0,plain,
% 2.67/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.67/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_23,plain,
% 2.67/0.99      ( v2_struct_0(X0)
% 2.67/0.99      | ~ l1_struct_0(X0)
% 2.67/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.67/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_379,plain,
% 2.67/0.99      ( v2_struct_0(X0)
% 2.67/0.99      | ~ l1_struct_0(X0)
% 2.67/0.99      | u1_struct_0(X0) != k1_xboole_0 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_23]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_32,negated_conjecture,
% 2.67/0.99      ( ~ v2_struct_0(sK1) ),
% 2.67/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_397,plain,
% 2.67/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_379,c_32]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_398,plain,
% 2.67/0.99      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_397]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_400,plain,
% 2.67/0.99      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_398,c_31]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1104,plain,
% 2.67/0.99      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 2.67/0.99      inference(light_normalisation,[status(thm)],[c_400,c_407]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_3906,plain,
% 2.67/0.99      ( k10_relat_1(sK2,k2_struct_0(sK1)) = k2_struct_0(sK0) ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_2688,c_1107,c_1104]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_4100,plain,
% 2.67/0.99      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
% 2.67/0.99      inference(light_normalisation,[status(thm)],[c_3423,c_3906]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_24,plain,
% 2.67/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/0.99      | ~ v1_funct_1(X0)
% 2.67/0.99      | ~ v2_funct_1(X0)
% 2.67/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.67/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.67/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1077,plain,
% 2.67/0.99      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
% 2.67/0.99      | k2_relset_1(X0,X1,X2) != X1
% 2.67/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.67/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.67/0.99      | v1_funct_1(X2) != iProver_top
% 2.67/0.99      | v2_funct_1(X2) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_4104,plain,
% 2.67/0.99      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.67/0.99      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 2.67/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 2.67/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.67/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_4100,c_1077]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_5,plain,
% 2.67/0.99      ( ~ v1_relat_1(X0)
% 2.67/0.99      | ~ v1_funct_1(X0)
% 2.67/0.99      | ~ v2_funct_1(X0)
% 2.67/0.99      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.67/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1091,plain,
% 2.67/0.99      ( k2_funct_1(k2_funct_1(X0)) = X0
% 2.67/0.99      | v1_relat_1(X0) != iProver_top
% 2.67/0.99      | v1_funct_1(X0) != iProver_top
% 2.67/0.99      | v2_funct_1(X0) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2039,plain,
% 2.67/0.99      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.67/0.99      | v1_funct_1(sK2) != iProver_top
% 2.67/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_1441,c_1091]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1399,plain,
% 2.67/0.99      ( ~ v1_relat_1(sK2)
% 2.67/0.99      | ~ v1_funct_1(sK2)
% 2.67/0.99      | ~ v2_funct_1(sK2)
% 2.67/0.99      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2344,plain,
% 2.67/0.99      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_2039,c_30,c_28,c_26,c_1330,c_1399]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_4110,plain,
% 2.67/0.99      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 2.67/0.99      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 2.67/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 2.67/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.67/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.67/0.99      inference(light_normalisation,[status(thm)],[c_4104,c_2344]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_39,plain,
% 2.67/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1331,plain,
% 2.67/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.67/0.99      | v1_relat_1(sK2) = iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_1330]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1,plain,
% 2.67/0.99      ( ~ v1_relat_1(X0)
% 2.67/0.99      | ~ v1_funct_1(X0)
% 2.67/0.99      | ~ v2_funct_1(X0)
% 2.67/0.99      | v2_funct_1(k2_funct_1(X0)) ),
% 2.67/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1403,plain,
% 2.67/0.99      ( ~ v1_relat_1(sK2)
% 2.67/0.99      | ~ v1_funct_1(sK2)
% 2.67/0.99      | v2_funct_1(k2_funct_1(sK2))
% 2.67/0.99      | ~ v2_funct_1(sK2) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1404,plain,
% 2.67/0.99      ( v1_relat_1(sK2) != iProver_top
% 2.67/0.99      | v1_funct_1(sK2) != iProver_top
% 2.67/0.99      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.67/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_1403]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2,plain,
% 2.67/0.99      ( ~ v1_relat_1(X0)
% 2.67/0.99      | ~ v1_funct_1(X0)
% 2.67/0.99      | v1_funct_1(k2_funct_1(X0))
% 2.67/0.99      | ~ v2_funct_1(X0) ),
% 2.67/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1402,plain,
% 2.67/0.99      ( ~ v1_relat_1(sK2)
% 2.67/0.99      | v1_funct_1(k2_funct_1(sK2))
% 2.67/0.99      | ~ v1_funct_1(sK2)
% 2.67/0.99      | ~ v2_funct_1(sK2) ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1406,plain,
% 2.67/0.99      ( v1_relat_1(sK2) != iProver_top
% 2.67/0.99      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.67/0.99      | v1_funct_1(sK2) != iProver_top
% 2.67/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_1402]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_20,plain,
% 2.67/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.67/0.99      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/0.99      | ~ v1_funct_1(X0)
% 2.67/0.99      | ~ v2_funct_1(X0)
% 2.67/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.67/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1078,plain,
% 2.67/0.99      ( k2_relset_1(X0,X1,X2) != X1
% 2.67/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.67/0.99      | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
% 2.67/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.67/0.99      | v1_funct_1(X2) != iProver_top
% 2.67/0.99      | v2_funct_1(X2) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2634,plain,
% 2.67/0.99      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
% 2.67/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.67/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.67/0.99      | v1_funct_1(sK2) != iProver_top
% 2.67/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_1110,c_1078]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_4636,plain,
% 2.67/0.99      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_4110,c_37,c_39,c_40,c_1107,c_1113,c_1331,c_1404,
% 2.67/0.99                 c_1406,c_2634,c_2927]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1953,plain,
% 2.67/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.67/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.67/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.67/0.99      | v1_funct_1(sK2) != iProver_top
% 2.67/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.67/0.99      inference(superposition,[status(thm)],[c_1110,c_1077]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2239,plain,
% 2.67/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.67/0.99      inference(global_propositional_subsumption,
% 2.67/0.99                [status(thm)],
% 2.67/0.99                [c_1953,c_37,c_40,c_1107,c_1113]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_17,plain,
% 2.67/0.99      ( r2_funct_2(X0,X1,X2,X2)
% 2.67/0.99      | ~ v1_funct_2(X2,X0,X1)
% 2.67/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.67/0.99      | ~ v1_funct_1(X2) ),
% 2.67/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_25,negated_conjecture,
% 2.67/0.99      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 2.67/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_420,plain,
% 2.67/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.67/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/0.99      | ~ v1_funct_1(X0)
% 2.67/0.99      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 2.67/0.99      | u1_struct_0(sK1) != X2
% 2.67/0.99      | u1_struct_0(sK0) != X1
% 2.67/0.99      | sK2 != X0 ),
% 2.67/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_421,plain,
% 2.67/0.99      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.67/0.99      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.67/0.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.67/0.99      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.67/0.99      inference(unflattening,[status(thm)],[c_420]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1071,plain,
% 2.67/0.99      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.67/0.99      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.67/0.99      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.67/0.99      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 2.67/0.99      inference(predicate_to_equality,[status(thm)],[c_421]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1262,plain,
% 2.67/0.99      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.67/0.99      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.67/0.99      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.67/0.99      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.67/0.99      inference(light_normalisation,[status(thm)],[c_1071,c_407,c_412]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_2242,plain,
% 2.67/0.99      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 2.67/0.99      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.67/0.99      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.67/0.99      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 2.67/0.99      inference(demodulation,[status(thm)],[c_2239,c_1262]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_4639,plain,
% 2.67/0.99      ( sK2 != sK2
% 2.67/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.67/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.67/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.67/0.99      inference(demodulation,[status(thm)],[c_4636,c_2242]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_614,plain,( X0 = X0 ),theory(equality) ).
% 2.67/0.99  
% 2.67/0.99  cnf(c_1498,plain,
% 2.67/0.99      ( sK2 = sK2 ),
% 2.67/0.99      inference(instantiation,[status(thm)],[c_614]) ).
% 2.67/0.99  
% 2.67/0.99  cnf(contradiction,plain,
% 2.67/0.99      ( $false ),
% 2.67/0.99      inference(minisat,[status(thm)],[c_4639,c_1498,c_1113,c_1107,c_37]) ).
% 2.67/0.99  
% 2.67/0.99  
% 2.67/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.67/0.99  
% 2.67/0.99  ------                               Statistics
% 2.67/0.99  
% 2.67/0.99  ------ General
% 2.67/0.99  
% 2.67/0.99  abstr_ref_over_cycles:                  0
% 2.67/0.99  abstr_ref_under_cycles:                 0
% 2.67/0.99  gc_basic_clause_elim:                   0
% 2.67/0.99  forced_gc_time:                         0
% 2.67/0.99  parsing_time:                           0.009
% 2.67/0.99  unif_index_cands_time:                  0.
% 2.67/0.99  unif_index_add_time:                    0.
% 2.67/0.99  orderings_time:                         0.
% 2.67/0.99  out_proof_time:                         0.014
% 2.67/0.99  total_time:                             0.132
% 2.67/0.99  num_of_symbols:                         56
% 2.67/0.99  num_of_terms:                           4072
% 2.67/0.99  
% 2.67/0.99  ------ Preprocessing
% 2.67/0.99  
% 2.67/0.99  num_of_splits:                          0
% 2.67/0.99  num_of_split_atoms:                     0
% 2.67/0.99  num_of_reused_defs:                     0
% 2.67/0.99  num_eq_ax_congr_red:                    39
% 2.67/0.99  num_of_sem_filtered_clauses:            1
% 2.67/0.99  num_of_subtypes:                        0
% 2.67/0.99  monotx_restored_types:                  0
% 2.67/0.99  sat_num_of_epr_types:                   0
% 2.67/0.99  sat_num_of_non_cyclic_types:            0
% 2.67/0.99  sat_guarded_non_collapsed_types:        0
% 2.67/0.99  num_pure_diseq_elim:                    0
% 2.67/0.99  simp_replaced_by:                       0
% 2.67/0.99  res_preprocessed:                       154
% 2.67/0.99  prep_upred:                             0
% 2.67/0.99  prep_unflattend:                        10
% 2.67/0.99  smt_new_axioms:                         0
% 2.67/0.99  pred_elim_cands:                        5
% 2.67/0.99  pred_elim:                              4
% 2.67/0.99  pred_elim_cl:                           5
% 2.67/0.99  pred_elim_cycles:                       6
% 2.67/0.99  merged_defs:                            0
% 2.67/0.99  merged_defs_ncl:                        0
% 2.67/0.99  bin_hyper_res:                          0
% 2.67/0.99  prep_cycles:                            4
% 2.67/0.99  pred_elim_time:                         0.001
% 2.67/0.99  splitting_time:                         0.
% 2.67/0.99  sem_filter_time:                        0.
% 2.67/0.99  monotx_time:                            0.
% 2.67/0.99  subtype_inf_time:                       0.
% 2.67/0.99  
% 2.67/0.99  ------ Problem properties
% 2.67/0.99  
% 2.67/0.99  clauses:                                29
% 2.67/0.99  conjectures:                            5
% 2.67/0.99  epr:                                    2
% 2.67/0.99  horn:                                   25
% 2.67/0.99  ground:                                 9
% 2.67/0.99  unary:                                  8
% 2.67/0.99  binary:                                 5
% 2.67/0.99  lits:                                   85
% 2.67/0.99  lits_eq:                                24
% 2.67/0.99  fd_pure:                                0
% 2.67/0.99  fd_pseudo:                              0
% 2.67/0.99  fd_cond:                                3
% 2.67/0.99  fd_pseudo_cond:                         0
% 2.67/0.99  ac_symbols:                             0
% 2.67/0.99  
% 2.67/0.99  ------ Propositional Solver
% 2.67/0.99  
% 2.67/0.99  prop_solver_calls:                      28
% 2.67/0.99  prop_fast_solver_calls:                 1155
% 2.67/0.99  smt_solver_calls:                       0
% 2.67/0.99  smt_fast_solver_calls:                  0
% 2.67/0.99  prop_num_of_clauses:                    1458
% 2.67/0.99  prop_preprocess_simplified:             5563
% 2.67/0.99  prop_fo_subsumed:                       48
% 2.67/0.99  prop_solver_time:                       0.
% 2.67/0.99  smt_solver_time:                        0.
% 2.67/0.99  smt_fast_solver_time:                   0.
% 2.67/0.99  prop_fast_solver_time:                  0.
% 2.67/0.99  prop_unsat_core_time:                   0.
% 2.67/0.99  
% 2.67/0.99  ------ QBF
% 2.67/0.99  
% 2.67/0.99  qbf_q_res:                              0
% 2.67/0.99  qbf_num_tautologies:                    0
% 2.67/0.99  qbf_prep_cycles:                        0
% 2.67/0.99  
% 2.67/0.99  ------ BMC1
% 2.67/0.99  
% 2.67/0.99  bmc1_current_bound:                     -1
% 2.67/0.99  bmc1_last_solved_bound:                 -1
% 2.67/0.99  bmc1_unsat_core_size:                   -1
% 2.67/0.99  bmc1_unsat_core_parents_size:           -1
% 2.67/0.99  bmc1_merge_next_fun:                    0
% 2.67/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.67/0.99  
% 2.67/0.99  ------ Instantiation
% 2.67/0.99  
% 2.67/0.99  inst_num_of_clauses:                    510
% 2.67/0.99  inst_num_in_passive:                    86
% 2.67/0.99  inst_num_in_active:                     315
% 2.67/0.99  inst_num_in_unprocessed:                109
% 2.67/0.99  inst_num_of_loops:                      330
% 2.67/0.99  inst_num_of_learning_restarts:          0
% 2.67/0.99  inst_num_moves_active_passive:          11
% 2.67/0.99  inst_lit_activity:                      0
% 2.67/0.99  inst_lit_activity_moves:                0
% 2.67/0.99  inst_num_tautologies:                   0
% 2.67/0.99  inst_num_prop_implied:                  0
% 2.67/0.99  inst_num_existing_simplified:           0
% 2.67/0.99  inst_num_eq_res_simplified:             0
% 2.67/0.99  inst_num_child_elim:                    0
% 2.67/0.99  inst_num_of_dismatching_blockings:      81
% 2.67/0.99  inst_num_of_non_proper_insts:           408
% 2.67/0.99  inst_num_of_duplicates:                 0
% 2.67/0.99  inst_inst_num_from_inst_to_res:         0
% 2.67/0.99  inst_dismatching_checking_time:         0.
% 2.67/0.99  
% 2.67/0.99  ------ Resolution
% 2.67/0.99  
% 2.67/0.99  res_num_of_clauses:                     0
% 2.67/0.99  res_num_in_passive:                     0
% 2.67/0.99  res_num_in_active:                      0
% 2.67/0.99  res_num_of_loops:                       158
% 2.67/0.99  res_forward_subset_subsumed:            33
% 2.67/0.99  res_backward_subset_subsumed:           4
% 2.67/0.99  res_forward_subsumed:                   0
% 2.67/0.99  res_backward_subsumed:                  0
% 2.67/0.99  res_forward_subsumption_resolution:     0
% 2.67/0.99  res_backward_subsumption_resolution:    0
% 2.67/0.99  res_clause_to_clause_subsumption:       172
% 2.67/0.99  res_orphan_elimination:                 0
% 2.67/0.99  res_tautology_del:                      45
% 2.67/0.99  res_num_eq_res_simplified:              0
% 2.67/0.99  res_num_sel_changes:                    0
% 2.67/0.99  res_moves_from_active_to_pass:          0
% 2.67/0.99  
% 2.67/0.99  ------ Superposition
% 2.67/0.99  
% 2.67/0.99  sup_time_total:                         0.
% 2.67/0.99  sup_time_generating:                    0.
% 2.67/0.99  sup_time_sim_full:                      0.
% 2.67/0.99  sup_time_sim_immed:                     0.
% 2.67/0.99  
% 2.67/0.99  sup_num_of_clauses:                     61
% 2.67/0.99  sup_num_in_active:                      57
% 2.67/0.99  sup_num_in_passive:                     4
% 2.67/0.99  sup_num_of_loops:                       64
% 2.67/0.99  sup_fw_superposition:                   44
% 2.67/0.99  sup_bw_superposition:                   23
% 2.67/0.99  sup_immediate_simplified:               42
% 2.67/0.99  sup_given_eliminated:                   0
% 2.67/0.99  comparisons_done:                       0
% 2.67/0.99  comparisons_avoided:                    3
% 2.67/0.99  
% 2.67/0.99  ------ Simplifications
% 2.67/0.99  
% 2.67/0.99  
% 2.67/0.99  sim_fw_subset_subsumed:                 8
% 2.67/0.99  sim_bw_subset_subsumed:                 2
% 2.67/0.99  sim_fw_subsumed:                        5
% 2.67/0.99  sim_bw_subsumed:                        0
% 2.67/0.99  sim_fw_subsumption_res:                 0
% 2.67/0.99  sim_bw_subsumption_res:                 0
% 2.67/0.99  sim_tautology_del:                      0
% 2.67/0.99  sim_eq_tautology_del:                   17
% 2.67/0.99  sim_eq_res_simp:                        0
% 2.67/0.99  sim_fw_demodulated:                     5
% 2.67/0.99  sim_bw_demodulated:                     7
% 2.67/0.99  sim_light_normalised:                   35
% 2.67/0.99  sim_joinable_taut:                      0
% 2.67/0.99  sim_joinable_simp:                      0
% 2.67/0.99  sim_ac_normalised:                      0
% 2.67/0.99  sim_smt_subsumption:                    0
% 2.67/0.99  
%------------------------------------------------------------------------------
