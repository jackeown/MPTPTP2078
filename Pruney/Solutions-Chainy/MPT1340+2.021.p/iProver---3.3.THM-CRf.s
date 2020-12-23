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
% DateTime   : Thu Dec  3 12:17:25 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :  192 (4463 expanded)
%              Number of clauses        :  119 (1417 expanded)
%              Number of leaves         :   18 (1245 expanded)
%              Depth                    :   26
%              Number of atoms          :  698 (27368 expanded)
%              Number of equality atoms :  261 (4896 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,
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

fof(f47,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f46,f45,f44])).

fof(f75,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f76,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

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

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

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

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f77,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f53,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f54,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f51,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

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

fof(f43,plain,(
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

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f61])).

fof(f78,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_653,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1076,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_653])).

cnf(c_19,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_30,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_378,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_379,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_647,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_379])).

cnf(c_28,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_373,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_374,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_648,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_374])).

cnf(c_1099,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1076,c_647,c_648])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_659,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1071,plain,
    ( k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_659])).

cnf(c_1376,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1099,c_1071])).

cnf(c_24,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_654,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1096,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_654,c_647,c_648])).

cnf(c_1503,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1376,c_1096])).

cnf(c_1556,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1503,c_1099])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_8,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_11,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_385,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_8,c_11])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_389,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_385,c_11,c_8,c_7])).

cnf(c_390,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_389])).

cnf(c_452,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_15,c_390])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_452,c_15,c_7,c_385])).

cnf(c_457,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_456])).

cnf(c_645,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X1_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | k1_relat_1(X0_52) = X0_53
    | k1_xboole_0 = X1_53 ),
    inference(subtyping,[status(esa)],[c_457])).

cnf(c_1081,plain,
    ( k1_relat_1(X0_52) = X0_53
    | k1_xboole_0 = X1_53
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_645])).

cnf(c_3178,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1556,c_1081])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_652,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1077,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_652])).

cnf(c_1093,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1077,c_647,c_648])).

cnf(c_1557,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1503,c_1093])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_20,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_346,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_20])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_364,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_346,c_29])).

cnf(c_365,plain,
    ( ~ l1_struct_0(sK1)
    | k2_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_348,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | k2_struct_0(sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_367,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_365,c_29,c_28,c_348])).

cnf(c_649,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_367])).

cnf(c_1558,plain,
    ( k2_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1503,c_649])).

cnf(c_3547,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3178,c_34,c_1557,c_1558])).

cnf(c_1554,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1503,c_1376])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_658,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X1_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | m1_subset_1(k2_funct_1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | k2_relset_1(X0_53,X1_53,X0_52) != X1_53 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1072,plain,
    ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_658])).

cnf(c_2333,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1554,c_1072])).

cnf(c_23,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_37,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2585,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2333,c_34,c_37,c_1556,c_1557])).

cnf(c_2590,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2585,c_1071])).

cnf(c_660,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | v1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1070,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_relat_1(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_660])).

cnf(c_1359,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1099,c_1070])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_663,plain,
    ( ~ v1_relat_1(X0_52)
    | ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | k2_relat_1(k2_funct_1(X0_52)) = k1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1067,plain,
    ( k2_relat_1(k2_funct_1(X0_52)) = k1_relat_1(X0_52)
    | v1_relat_1(X0_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_663])).

cnf(c_1696,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1359,c_1067])).

cnf(c_713,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_663])).

cnf(c_1278,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_660])).

cnf(c_2105,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1696,c_27,c_25,c_23,c_713,c_1278])).

cnf(c_2595,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2590,c_2105])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_656,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X1_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | k2_relset_1(X0_53,X1_53,X0_52) != X1_53
    | k2_tops_2(X0_53,X1_53,X0_52) = k2_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1074,plain,
    ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
    | k2_tops_2(X0_53,X1_53,X0_52) = k2_funct_1(X0_52)
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_656])).

cnf(c_2686,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2595,c_1074])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_661,plain,
    ( ~ v1_relat_1(X0_52)
    | ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | k2_funct_1(k2_funct_1(X0_52)) = X0_52 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1069,plain,
    ( k2_funct_1(k2_funct_1(X0_52)) = X0_52
    | v1_relat_1(X0_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_661])).

cnf(c_1792,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1359,c_1069])).

cnf(c_719,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_661])).

cnf(c_2098,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1792,c_27,c_25,c_23,c_719,c_1278])).

cnf(c_2701,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2686,c_2098])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_666,plain,
    ( ~ v1_relat_1(X0_52)
    | ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | v2_funct_1(k2_funct_1(X0_52)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_703,plain,
    ( v1_relat_1(X0_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top
    | v2_funct_1(k2_funct_1(X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_666])).

cnf(c_705,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_703])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_665,plain,
    ( ~ v1_relat_1(X0_52)
    | ~ v1_funct_1(X0_52)
    | v1_funct_1(k2_funct_1(X0_52))
    | ~ v2_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_706,plain,
    ( v1_relat_1(X0_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k2_funct_1(X0_52)) = iProver_top
    | v2_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_665])).

cnf(c_708,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_706])).

cnf(c_1279,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1278])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_657,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X1_53)
    | v1_funct_2(k2_funct_1(X0_52),X1_53,X0_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | k2_relset_1(X0_53,X1_53,X0_52) != X1_53 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1073,plain,
    ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | v1_funct_2(k2_funct_1(X0_52),X1_53,X0_53) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_657])).

cnf(c_1927,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1554,c_1073])).

cnf(c_2822,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2701,c_34,c_36,c_37,c_705,c_708,c_1279,c_1556,c_1557,c_1927,c_2333])).

cnf(c_3550,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_3547,c_2822])).

cnf(c_3584,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_3550])).

cnf(c_1936,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1554,c_1074])).

cnf(c_2245,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1936,c_34,c_37,c_1556,c_1557])).

cnf(c_12,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_22,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_431,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_432,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_646,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_432])).

cnf(c_1080,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_646])).

cnf(c_1222,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1080,c_647,c_648])).

cnf(c_1555,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1503,c_1222])).

cnf(c_2248,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2245,c_1555])).

cnf(c_3553,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3547,c_2248])).

cnf(c_3586,plain,
    ( sK2 != sK2
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3584,c_3553])).

cnf(c_3588,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3586])).

cnf(c_3556,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3547,c_1556])).

cnf(c_3558,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3547,c_1557])).

cnf(c_3592,plain,
    ( v1_funct_1(sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3588,c_3556,c_3558])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3592,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:10:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.65/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/0.98  
% 2.65/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.65/0.98  
% 2.65/0.98  ------  iProver source info
% 2.65/0.98  
% 2.65/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.65/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.65/0.98  git: non_committed_changes: false
% 2.65/0.98  git: last_make_outside_of_git: false
% 2.65/0.98  
% 2.65/0.98  ------ 
% 2.65/0.98  
% 2.65/0.98  ------ Input Options
% 2.65/0.98  
% 2.65/0.98  --out_options                           all
% 2.65/0.98  --tptp_safe_out                         true
% 2.65/0.98  --problem_path                          ""
% 2.65/0.98  --include_path                          ""
% 2.65/0.98  --clausifier                            res/vclausify_rel
% 2.65/0.98  --clausifier_options                    --mode clausify
% 2.65/0.98  --stdin                                 false
% 2.65/0.98  --stats_out                             all
% 2.65/0.98  
% 2.65/0.98  ------ General Options
% 2.65/0.98  
% 2.65/0.98  --fof                                   false
% 2.65/0.98  --time_out_real                         305.
% 2.65/0.98  --time_out_virtual                      -1.
% 2.65/0.98  --symbol_type_check                     false
% 2.65/0.98  --clausify_out                          false
% 2.65/0.98  --sig_cnt_out                           false
% 2.65/0.98  --trig_cnt_out                          false
% 2.65/0.98  --trig_cnt_out_tolerance                1.
% 2.65/0.98  --trig_cnt_out_sk_spl                   false
% 2.65/0.98  --abstr_cl_out                          false
% 2.65/0.98  
% 2.65/0.98  ------ Global Options
% 2.65/0.98  
% 2.65/0.98  --schedule                              default
% 2.65/0.98  --add_important_lit                     false
% 2.65/0.98  --prop_solver_per_cl                    1000
% 2.65/0.98  --min_unsat_core                        false
% 2.65/0.98  --soft_assumptions                      false
% 2.65/0.98  --soft_lemma_size                       3
% 2.65/0.98  --prop_impl_unit_size                   0
% 2.65/0.98  --prop_impl_unit                        []
% 2.65/0.98  --share_sel_clauses                     true
% 2.65/0.98  --reset_solvers                         false
% 2.65/0.98  --bc_imp_inh                            [conj_cone]
% 2.65/0.98  --conj_cone_tolerance                   3.
% 2.65/0.98  --extra_neg_conj                        none
% 2.65/0.98  --large_theory_mode                     true
% 2.65/0.98  --prolific_symb_bound                   200
% 2.65/0.98  --lt_threshold                          2000
% 2.65/0.98  --clause_weak_htbl                      true
% 2.65/0.98  --gc_record_bc_elim                     false
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing Options
% 2.65/0.98  
% 2.65/0.98  --preprocessing_flag                    true
% 2.65/0.98  --time_out_prep_mult                    0.1
% 2.65/0.98  --splitting_mode                        input
% 2.65/0.98  --splitting_grd                         true
% 2.65/0.98  --splitting_cvd                         false
% 2.65/0.98  --splitting_cvd_svl                     false
% 2.65/0.98  --splitting_nvd                         32
% 2.65/0.98  --sub_typing                            true
% 2.65/0.98  --prep_gs_sim                           true
% 2.65/0.98  --prep_unflatten                        true
% 2.65/0.98  --prep_res_sim                          true
% 2.65/0.98  --prep_upred                            true
% 2.65/0.98  --prep_sem_filter                       exhaustive
% 2.65/0.98  --prep_sem_filter_out                   false
% 2.65/0.98  --pred_elim                             true
% 2.65/0.98  --res_sim_input                         true
% 2.65/0.98  --eq_ax_congr_red                       true
% 2.65/0.98  --pure_diseq_elim                       true
% 2.65/0.98  --brand_transform                       false
% 2.65/0.98  --non_eq_to_eq                          false
% 2.65/0.98  --prep_def_merge                        true
% 2.65/0.98  --prep_def_merge_prop_impl              false
% 2.65/0.98  --prep_def_merge_mbd                    true
% 2.65/0.98  --prep_def_merge_tr_red                 false
% 2.65/0.98  --prep_def_merge_tr_cl                  false
% 2.65/0.98  --smt_preprocessing                     true
% 2.65/0.98  --smt_ac_axioms                         fast
% 2.65/0.98  --preprocessed_out                      false
% 2.65/0.98  --preprocessed_stats                    false
% 2.65/0.98  
% 2.65/0.98  ------ Abstraction refinement Options
% 2.65/0.98  
% 2.65/0.98  --abstr_ref                             []
% 2.65/0.98  --abstr_ref_prep                        false
% 2.65/0.98  --abstr_ref_until_sat                   false
% 2.65/0.98  --abstr_ref_sig_restrict                funpre
% 2.65/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.65/0.98  --abstr_ref_under                       []
% 2.65/0.98  
% 2.65/0.98  ------ SAT Options
% 2.65/0.98  
% 2.65/0.98  --sat_mode                              false
% 2.65/0.98  --sat_fm_restart_options                ""
% 2.65/0.98  --sat_gr_def                            false
% 2.65/0.98  --sat_epr_types                         true
% 2.65/0.98  --sat_non_cyclic_types                  false
% 2.65/0.98  --sat_finite_models                     false
% 2.65/0.98  --sat_fm_lemmas                         false
% 2.65/0.98  --sat_fm_prep                           false
% 2.65/0.98  --sat_fm_uc_incr                        true
% 2.65/0.98  --sat_out_model                         small
% 2.65/0.98  --sat_out_clauses                       false
% 2.65/0.98  
% 2.65/0.98  ------ QBF Options
% 2.65/0.98  
% 2.65/0.98  --qbf_mode                              false
% 2.65/0.98  --qbf_elim_univ                         false
% 2.65/0.98  --qbf_dom_inst                          none
% 2.65/0.98  --qbf_dom_pre_inst                      false
% 2.65/0.98  --qbf_sk_in                             false
% 2.65/0.98  --qbf_pred_elim                         true
% 2.65/0.98  --qbf_split                             512
% 2.65/0.98  
% 2.65/0.98  ------ BMC1 Options
% 2.65/0.98  
% 2.65/0.98  --bmc1_incremental                      false
% 2.65/0.98  --bmc1_axioms                           reachable_all
% 2.65/0.98  --bmc1_min_bound                        0
% 2.65/0.98  --bmc1_max_bound                        -1
% 2.65/0.98  --bmc1_max_bound_default                -1
% 2.65/0.98  --bmc1_symbol_reachability              true
% 2.65/0.98  --bmc1_property_lemmas                  false
% 2.65/0.98  --bmc1_k_induction                      false
% 2.65/0.98  --bmc1_non_equiv_states                 false
% 2.65/0.98  --bmc1_deadlock                         false
% 2.65/0.98  --bmc1_ucm                              false
% 2.65/0.98  --bmc1_add_unsat_core                   none
% 2.65/0.98  --bmc1_unsat_core_children              false
% 2.65/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.65/0.98  --bmc1_out_stat                         full
% 2.65/0.98  --bmc1_ground_init                      false
% 2.65/0.98  --bmc1_pre_inst_next_state              false
% 2.65/0.98  --bmc1_pre_inst_state                   false
% 2.65/0.98  --bmc1_pre_inst_reach_state             false
% 2.65/0.98  --bmc1_out_unsat_core                   false
% 2.65/0.98  --bmc1_aig_witness_out                  false
% 2.65/0.98  --bmc1_verbose                          false
% 2.65/0.98  --bmc1_dump_clauses_tptp                false
% 2.65/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.65/0.98  --bmc1_dump_file                        -
% 2.65/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.65/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.65/0.98  --bmc1_ucm_extend_mode                  1
% 2.65/0.98  --bmc1_ucm_init_mode                    2
% 2.65/0.98  --bmc1_ucm_cone_mode                    none
% 2.65/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.65/0.98  --bmc1_ucm_relax_model                  4
% 2.65/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.65/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.65/0.98  --bmc1_ucm_layered_model                none
% 2.65/0.98  --bmc1_ucm_max_lemma_size               10
% 2.65/0.98  
% 2.65/0.98  ------ AIG Options
% 2.65/0.98  
% 2.65/0.98  --aig_mode                              false
% 2.65/0.98  
% 2.65/0.98  ------ Instantiation Options
% 2.65/0.98  
% 2.65/0.98  --instantiation_flag                    true
% 2.65/0.98  --inst_sos_flag                         false
% 2.65/0.98  --inst_sos_phase                        true
% 2.65/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.65/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.65/0.98  --inst_lit_sel_side                     num_symb
% 2.65/0.98  --inst_solver_per_active                1400
% 2.65/0.98  --inst_solver_calls_frac                1.
% 2.65/0.98  --inst_passive_queue_type               priority_queues
% 2.65/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.65/0.98  --inst_passive_queues_freq              [25;2]
% 2.65/0.98  --inst_dismatching                      true
% 2.65/0.98  --inst_eager_unprocessed_to_passive     true
% 2.65/0.98  --inst_prop_sim_given                   true
% 2.65/0.98  --inst_prop_sim_new                     false
% 2.65/0.98  --inst_subs_new                         false
% 2.65/0.98  --inst_eq_res_simp                      false
% 2.65/0.98  --inst_subs_given                       false
% 2.65/0.98  --inst_orphan_elimination               true
% 2.65/0.98  --inst_learning_loop_flag               true
% 2.65/0.98  --inst_learning_start                   3000
% 2.65/0.98  --inst_learning_factor                  2
% 2.65/0.98  --inst_start_prop_sim_after_learn       3
% 2.65/0.98  --inst_sel_renew                        solver
% 2.65/0.98  --inst_lit_activity_flag                true
% 2.65/0.98  --inst_restr_to_given                   false
% 2.65/0.98  --inst_activity_threshold               500
% 2.65/0.98  --inst_out_proof                        true
% 2.65/0.98  
% 2.65/0.98  ------ Resolution Options
% 2.65/0.98  
% 2.65/0.98  --resolution_flag                       true
% 2.65/0.98  --res_lit_sel                           adaptive
% 2.65/0.98  --res_lit_sel_side                      none
% 2.65/0.98  --res_ordering                          kbo
% 2.65/0.98  --res_to_prop_solver                    active
% 2.65/0.98  --res_prop_simpl_new                    false
% 2.65/0.98  --res_prop_simpl_given                  true
% 2.65/0.98  --res_passive_queue_type                priority_queues
% 2.65/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.65/0.98  --res_passive_queues_freq               [15;5]
% 2.65/0.98  --res_forward_subs                      full
% 2.65/0.98  --res_backward_subs                     full
% 2.65/0.98  --res_forward_subs_resolution           true
% 2.65/0.98  --res_backward_subs_resolution          true
% 2.65/0.98  --res_orphan_elimination                true
% 2.65/0.98  --res_time_limit                        2.
% 2.65/0.98  --res_out_proof                         true
% 2.65/0.98  
% 2.65/0.98  ------ Superposition Options
% 2.65/0.98  
% 2.65/0.98  --superposition_flag                    true
% 2.65/0.98  --sup_passive_queue_type                priority_queues
% 2.65/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.65/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.65/0.98  --demod_completeness_check              fast
% 2.65/0.98  --demod_use_ground                      true
% 2.65/0.98  --sup_to_prop_solver                    passive
% 2.65/0.98  --sup_prop_simpl_new                    true
% 2.65/0.98  --sup_prop_simpl_given                  true
% 2.65/0.98  --sup_fun_splitting                     false
% 2.65/0.98  --sup_smt_interval                      50000
% 2.65/0.98  
% 2.65/0.98  ------ Superposition Simplification Setup
% 2.65/0.98  
% 2.65/0.98  --sup_indices_passive                   []
% 2.65/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.65/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_full_bw                           [BwDemod]
% 2.65/0.98  --sup_immed_triv                        [TrivRules]
% 2.65/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.65/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_immed_bw_main                     []
% 2.65/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.65/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.98  
% 2.65/0.98  ------ Combination Options
% 2.65/0.98  
% 2.65/0.98  --comb_res_mult                         3
% 2.65/0.98  --comb_sup_mult                         2
% 2.65/0.98  --comb_inst_mult                        10
% 2.65/0.98  
% 2.65/0.98  ------ Debug Options
% 2.65/0.98  
% 2.65/0.98  --dbg_backtrace                         false
% 2.65/0.98  --dbg_dump_prop_clauses                 false
% 2.65/0.98  --dbg_dump_prop_clauses_file            -
% 2.65/0.98  --dbg_out_stat                          false
% 2.65/0.98  ------ Parsing...
% 2.65/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.65/0.98  ------ Proving...
% 2.65/0.98  ------ Problem Properties 
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  clauses                                 23
% 2.65/0.98  conjectures                             5
% 2.65/0.98  EPR                                     2
% 2.65/0.98  Horn                                    22
% 2.65/0.98  unary                                   8
% 2.65/0.98  binary                                  2
% 2.65/0.98  lits                                    72
% 2.65/0.98  lits eq                                 16
% 2.65/0.98  fd_pure                                 0
% 2.65/0.98  fd_pseudo                               0
% 2.65/0.98  fd_cond                                 0
% 2.65/0.98  fd_pseudo_cond                          1
% 2.65/0.98  AC symbols                              0
% 2.65/0.98  
% 2.65/0.98  ------ Schedule dynamic 5 is on 
% 2.65/0.98  
% 2.65/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  ------ 
% 2.65/0.98  Current options:
% 2.65/0.98  ------ 
% 2.65/0.98  
% 2.65/0.98  ------ Input Options
% 2.65/0.98  
% 2.65/0.98  --out_options                           all
% 2.65/0.98  --tptp_safe_out                         true
% 2.65/0.98  --problem_path                          ""
% 2.65/0.98  --include_path                          ""
% 2.65/0.98  --clausifier                            res/vclausify_rel
% 2.65/0.98  --clausifier_options                    --mode clausify
% 2.65/0.98  --stdin                                 false
% 2.65/0.98  --stats_out                             all
% 2.65/0.98  
% 2.65/0.98  ------ General Options
% 2.65/0.98  
% 2.65/0.98  --fof                                   false
% 2.65/0.98  --time_out_real                         305.
% 2.65/0.98  --time_out_virtual                      -1.
% 2.65/0.98  --symbol_type_check                     false
% 2.65/0.98  --clausify_out                          false
% 2.65/0.98  --sig_cnt_out                           false
% 2.65/0.98  --trig_cnt_out                          false
% 2.65/0.98  --trig_cnt_out_tolerance                1.
% 2.65/0.98  --trig_cnt_out_sk_spl                   false
% 2.65/0.98  --abstr_cl_out                          false
% 2.65/0.98  
% 2.65/0.98  ------ Global Options
% 2.65/0.98  
% 2.65/0.98  --schedule                              default
% 2.65/0.98  --add_important_lit                     false
% 2.65/0.98  --prop_solver_per_cl                    1000
% 2.65/0.98  --min_unsat_core                        false
% 2.65/0.98  --soft_assumptions                      false
% 2.65/0.98  --soft_lemma_size                       3
% 2.65/0.98  --prop_impl_unit_size                   0
% 2.65/0.98  --prop_impl_unit                        []
% 2.65/0.98  --share_sel_clauses                     true
% 2.65/0.98  --reset_solvers                         false
% 2.65/0.98  --bc_imp_inh                            [conj_cone]
% 2.65/0.98  --conj_cone_tolerance                   3.
% 2.65/0.98  --extra_neg_conj                        none
% 2.65/0.98  --large_theory_mode                     true
% 2.65/0.98  --prolific_symb_bound                   200
% 2.65/0.98  --lt_threshold                          2000
% 2.65/0.98  --clause_weak_htbl                      true
% 2.65/0.98  --gc_record_bc_elim                     false
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing Options
% 2.65/0.98  
% 2.65/0.98  --preprocessing_flag                    true
% 2.65/0.98  --time_out_prep_mult                    0.1
% 2.65/0.98  --splitting_mode                        input
% 2.65/0.98  --splitting_grd                         true
% 2.65/0.98  --splitting_cvd                         false
% 2.65/0.98  --splitting_cvd_svl                     false
% 2.65/0.98  --splitting_nvd                         32
% 2.65/0.98  --sub_typing                            true
% 2.65/0.98  --prep_gs_sim                           true
% 2.65/0.98  --prep_unflatten                        true
% 2.65/0.98  --prep_res_sim                          true
% 2.65/0.98  --prep_upred                            true
% 2.65/0.98  --prep_sem_filter                       exhaustive
% 2.65/0.98  --prep_sem_filter_out                   false
% 2.65/0.98  --pred_elim                             true
% 2.65/0.98  --res_sim_input                         true
% 2.65/0.98  --eq_ax_congr_red                       true
% 2.65/0.98  --pure_diseq_elim                       true
% 2.65/0.98  --brand_transform                       false
% 2.65/0.98  --non_eq_to_eq                          false
% 2.65/0.98  --prep_def_merge                        true
% 2.65/0.98  --prep_def_merge_prop_impl              false
% 2.65/0.98  --prep_def_merge_mbd                    true
% 2.65/0.98  --prep_def_merge_tr_red                 false
% 2.65/0.98  --prep_def_merge_tr_cl                  false
% 2.65/0.98  --smt_preprocessing                     true
% 2.65/0.98  --smt_ac_axioms                         fast
% 2.65/0.98  --preprocessed_out                      false
% 2.65/0.98  --preprocessed_stats                    false
% 2.65/0.98  
% 2.65/0.98  ------ Abstraction refinement Options
% 2.65/0.98  
% 2.65/0.98  --abstr_ref                             []
% 2.65/0.98  --abstr_ref_prep                        false
% 2.65/0.98  --abstr_ref_until_sat                   false
% 2.65/0.98  --abstr_ref_sig_restrict                funpre
% 2.65/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.65/0.98  --abstr_ref_under                       []
% 2.65/0.98  
% 2.65/0.98  ------ SAT Options
% 2.65/0.98  
% 2.65/0.98  --sat_mode                              false
% 2.65/0.98  --sat_fm_restart_options                ""
% 2.65/0.98  --sat_gr_def                            false
% 2.65/0.98  --sat_epr_types                         true
% 2.65/0.98  --sat_non_cyclic_types                  false
% 2.65/0.98  --sat_finite_models                     false
% 2.65/0.98  --sat_fm_lemmas                         false
% 2.65/0.98  --sat_fm_prep                           false
% 2.65/0.98  --sat_fm_uc_incr                        true
% 2.65/0.98  --sat_out_model                         small
% 2.65/0.98  --sat_out_clauses                       false
% 2.65/0.98  
% 2.65/0.98  ------ QBF Options
% 2.65/0.98  
% 2.65/0.98  --qbf_mode                              false
% 2.65/0.98  --qbf_elim_univ                         false
% 2.65/0.98  --qbf_dom_inst                          none
% 2.65/0.98  --qbf_dom_pre_inst                      false
% 2.65/0.98  --qbf_sk_in                             false
% 2.65/0.98  --qbf_pred_elim                         true
% 2.65/0.98  --qbf_split                             512
% 2.65/0.98  
% 2.65/0.98  ------ BMC1 Options
% 2.65/0.98  
% 2.65/0.98  --bmc1_incremental                      false
% 2.65/0.98  --bmc1_axioms                           reachable_all
% 2.65/0.98  --bmc1_min_bound                        0
% 2.65/0.98  --bmc1_max_bound                        -1
% 2.65/0.98  --bmc1_max_bound_default                -1
% 2.65/0.98  --bmc1_symbol_reachability              true
% 2.65/0.98  --bmc1_property_lemmas                  false
% 2.65/0.98  --bmc1_k_induction                      false
% 2.65/0.98  --bmc1_non_equiv_states                 false
% 2.65/0.98  --bmc1_deadlock                         false
% 2.65/0.98  --bmc1_ucm                              false
% 2.65/0.98  --bmc1_add_unsat_core                   none
% 2.65/0.98  --bmc1_unsat_core_children              false
% 2.65/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.65/0.98  --bmc1_out_stat                         full
% 2.65/0.98  --bmc1_ground_init                      false
% 2.65/0.98  --bmc1_pre_inst_next_state              false
% 2.65/0.98  --bmc1_pre_inst_state                   false
% 2.65/0.98  --bmc1_pre_inst_reach_state             false
% 2.65/0.98  --bmc1_out_unsat_core                   false
% 2.65/0.98  --bmc1_aig_witness_out                  false
% 2.65/0.98  --bmc1_verbose                          false
% 2.65/0.98  --bmc1_dump_clauses_tptp                false
% 2.65/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.65/0.98  --bmc1_dump_file                        -
% 2.65/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.65/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.65/0.98  --bmc1_ucm_extend_mode                  1
% 2.65/0.98  --bmc1_ucm_init_mode                    2
% 2.65/0.98  --bmc1_ucm_cone_mode                    none
% 2.65/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.65/0.98  --bmc1_ucm_relax_model                  4
% 2.65/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.65/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.65/0.98  --bmc1_ucm_layered_model                none
% 2.65/0.98  --bmc1_ucm_max_lemma_size               10
% 2.65/0.98  
% 2.65/0.98  ------ AIG Options
% 2.65/0.98  
% 2.65/0.98  --aig_mode                              false
% 2.65/0.98  
% 2.65/0.98  ------ Instantiation Options
% 2.65/0.98  
% 2.65/0.98  --instantiation_flag                    true
% 2.65/0.98  --inst_sos_flag                         false
% 2.65/0.98  --inst_sos_phase                        true
% 2.65/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.65/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.65/0.98  --inst_lit_sel_side                     none
% 2.65/0.98  --inst_solver_per_active                1400
% 2.65/0.98  --inst_solver_calls_frac                1.
% 2.65/0.98  --inst_passive_queue_type               priority_queues
% 2.65/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.65/0.98  --inst_passive_queues_freq              [25;2]
% 2.65/0.98  --inst_dismatching                      true
% 2.65/0.98  --inst_eager_unprocessed_to_passive     true
% 2.65/0.98  --inst_prop_sim_given                   true
% 2.65/0.98  --inst_prop_sim_new                     false
% 2.65/0.98  --inst_subs_new                         false
% 2.65/0.98  --inst_eq_res_simp                      false
% 2.65/0.98  --inst_subs_given                       false
% 2.65/0.98  --inst_orphan_elimination               true
% 2.65/0.98  --inst_learning_loop_flag               true
% 2.65/0.98  --inst_learning_start                   3000
% 2.65/0.98  --inst_learning_factor                  2
% 2.65/0.98  --inst_start_prop_sim_after_learn       3
% 2.65/0.98  --inst_sel_renew                        solver
% 2.65/0.98  --inst_lit_activity_flag                true
% 2.65/0.98  --inst_restr_to_given                   false
% 2.65/0.98  --inst_activity_threshold               500
% 2.65/0.98  --inst_out_proof                        true
% 2.65/0.98  
% 2.65/0.98  ------ Resolution Options
% 2.65/0.98  
% 2.65/0.98  --resolution_flag                       false
% 2.65/0.98  --res_lit_sel                           adaptive
% 2.65/0.98  --res_lit_sel_side                      none
% 2.65/0.98  --res_ordering                          kbo
% 2.65/0.98  --res_to_prop_solver                    active
% 2.65/0.98  --res_prop_simpl_new                    false
% 2.65/0.98  --res_prop_simpl_given                  true
% 2.65/0.98  --res_passive_queue_type                priority_queues
% 2.65/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.65/0.98  --res_passive_queues_freq               [15;5]
% 2.65/0.98  --res_forward_subs                      full
% 2.65/0.98  --res_backward_subs                     full
% 2.65/0.98  --res_forward_subs_resolution           true
% 2.65/0.98  --res_backward_subs_resolution          true
% 2.65/0.98  --res_orphan_elimination                true
% 2.65/0.98  --res_time_limit                        2.
% 2.65/0.98  --res_out_proof                         true
% 2.65/0.98  
% 2.65/0.98  ------ Superposition Options
% 2.65/0.98  
% 2.65/0.98  --superposition_flag                    true
% 2.65/0.98  --sup_passive_queue_type                priority_queues
% 2.65/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.65/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.65/0.98  --demod_completeness_check              fast
% 2.65/0.98  --demod_use_ground                      true
% 2.65/0.98  --sup_to_prop_solver                    passive
% 2.65/0.98  --sup_prop_simpl_new                    true
% 2.65/0.98  --sup_prop_simpl_given                  true
% 2.65/0.98  --sup_fun_splitting                     false
% 2.65/0.98  --sup_smt_interval                      50000
% 2.65/0.98  
% 2.65/0.98  ------ Superposition Simplification Setup
% 2.65/0.98  
% 2.65/0.98  --sup_indices_passive                   []
% 2.65/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.65/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_full_bw                           [BwDemod]
% 2.65/0.98  --sup_immed_triv                        [TrivRules]
% 2.65/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.65/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_immed_bw_main                     []
% 2.65/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.65/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.98  
% 2.65/0.98  ------ Combination Options
% 2.65/0.98  
% 2.65/0.98  --comb_res_mult                         3
% 2.65/0.98  --comb_sup_mult                         2
% 2.65/0.98  --comb_inst_mult                        10
% 2.65/0.98  
% 2.65/0.98  ------ Debug Options
% 2.65/0.98  
% 2.65/0.98  --dbg_backtrace                         false
% 2.65/0.98  --dbg_dump_prop_clauses                 false
% 2.65/0.98  --dbg_dump_prop_clauses_file            -
% 2.65/0.98  --dbg_out_stat                          false
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  ------ Proving...
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  % SZS status Theorem for theBenchmark.p
% 2.65/0.98  
% 2.65/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.65/0.98  
% 2.65/0.98  fof(f15,conjecture,(
% 2.65/0.98    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f16,negated_conjecture,(
% 2.65/0.98    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.65/0.98    inference(negated_conjecture,[],[f15])).
% 2.65/0.98  
% 2.65/0.98  fof(f40,plain,(
% 2.65/0.98    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.65/0.98    inference(ennf_transformation,[],[f16])).
% 2.65/0.98  
% 2.65/0.98  fof(f41,plain,(
% 2.65/0.98    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.65/0.98    inference(flattening,[],[f40])).
% 2.65/0.98  
% 2.65/0.98  fof(f46,plain,(
% 2.65/0.98    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.65/0.98    introduced(choice_axiom,[])).
% 2.65/0.98  
% 2.65/0.98  fof(f45,plain,(
% 2.65/0.98    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.65/0.98    introduced(choice_axiom,[])).
% 2.65/0.98  
% 2.65/0.98  fof(f44,plain,(
% 2.65/0.98    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.65/0.98    introduced(choice_axiom,[])).
% 2.65/0.98  
% 2.65/0.98  fof(f47,plain,(
% 2.65/0.98    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.65/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f46,f45,f44])).
% 2.65/0.98  
% 2.65/0.98  fof(f75,plain,(
% 2.65/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.65/0.98    inference(cnf_transformation,[],[f47])).
% 2.65/0.98  
% 2.65/0.98  fof(f12,axiom,(
% 2.65/0.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f35,plain,(
% 2.65/0.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.65/0.98    inference(ennf_transformation,[],[f12])).
% 2.65/0.98  
% 2.65/0.98  fof(f67,plain,(
% 2.65/0.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f35])).
% 2.65/0.98  
% 2.65/0.98  fof(f70,plain,(
% 2.65/0.98    l1_struct_0(sK0)),
% 2.65/0.98    inference(cnf_transformation,[],[f47])).
% 2.65/0.98  
% 2.65/0.98  fof(f72,plain,(
% 2.65/0.98    l1_struct_0(sK1)),
% 2.65/0.98    inference(cnf_transformation,[],[f47])).
% 2.65/0.98  
% 2.65/0.98  fof(f7,axiom,(
% 2.65/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f26,plain,(
% 2.65/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.65/0.98    inference(ennf_transformation,[],[f7])).
% 2.65/0.98  
% 2.65/0.98  fof(f57,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.65/0.98    inference(cnf_transformation,[],[f26])).
% 2.65/0.98  
% 2.65/0.98  fof(f76,plain,(
% 2.65/0.98    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.65/0.98    inference(cnf_transformation,[],[f47])).
% 2.65/0.98  
% 2.65/0.98  fof(f10,axiom,(
% 2.65/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f31,plain,(
% 2.65/0.98    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.65/0.98    inference(ennf_transformation,[],[f10])).
% 2.65/0.98  
% 2.65/0.98  fof(f32,plain,(
% 2.65/0.98    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.65/0.98    inference(flattening,[],[f31])).
% 2.65/0.98  
% 2.65/0.98  fof(f62,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f32])).
% 2.65/0.98  
% 2.65/0.98  fof(f6,axiom,(
% 2.65/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f17,plain,(
% 2.65/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.65/0.98    inference(pure_predicate_removal,[],[f6])).
% 2.65/0.98  
% 2.65/0.98  fof(f25,plain,(
% 2.65/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.65/0.98    inference(ennf_transformation,[],[f17])).
% 2.65/0.98  
% 2.65/0.98  fof(f56,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.65/0.98    inference(cnf_transformation,[],[f25])).
% 2.65/0.98  
% 2.65/0.98  fof(f8,axiom,(
% 2.65/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f27,plain,(
% 2.65/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.65/0.98    inference(ennf_transformation,[],[f8])).
% 2.65/0.98  
% 2.65/0.98  fof(f28,plain,(
% 2.65/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.65/0.98    inference(flattening,[],[f27])).
% 2.65/0.98  
% 2.65/0.98  fof(f42,plain,(
% 2.65/0.98    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.65/0.98    inference(nnf_transformation,[],[f28])).
% 2.65/0.98  
% 2.65/0.98  fof(f58,plain,(
% 2.65/0.98    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f42])).
% 2.65/0.98  
% 2.65/0.98  fof(f5,axiom,(
% 2.65/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f24,plain,(
% 2.65/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.65/0.98    inference(ennf_transformation,[],[f5])).
% 2.65/0.98  
% 2.65/0.98  fof(f55,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.65/0.98    inference(cnf_transformation,[],[f24])).
% 2.65/0.98  
% 2.65/0.98  fof(f73,plain,(
% 2.65/0.98    v1_funct_1(sK2)),
% 2.65/0.98    inference(cnf_transformation,[],[f47])).
% 2.65/0.98  
% 2.65/0.98  fof(f74,plain,(
% 2.65/0.98    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.65/0.98    inference(cnf_transformation,[],[f47])).
% 2.65/0.98  
% 2.65/0.98  fof(f1,axiom,(
% 2.65/0.98    v1_xboole_0(k1_xboole_0)),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f48,plain,(
% 2.65/0.98    v1_xboole_0(k1_xboole_0)),
% 2.65/0.98    inference(cnf_transformation,[],[f1])).
% 2.65/0.98  
% 2.65/0.98  fof(f13,axiom,(
% 2.65/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f36,plain,(
% 2.65/0.98    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.65/0.98    inference(ennf_transformation,[],[f13])).
% 2.65/0.98  
% 2.65/0.98  fof(f37,plain,(
% 2.65/0.98    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.65/0.98    inference(flattening,[],[f36])).
% 2.65/0.98  
% 2.65/0.98  fof(f68,plain,(
% 2.65/0.98    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f37])).
% 2.65/0.98  
% 2.65/0.98  fof(f71,plain,(
% 2.65/0.98    ~v2_struct_0(sK1)),
% 2.65/0.98    inference(cnf_transformation,[],[f47])).
% 2.65/0.98  
% 2.65/0.98  fof(f11,axiom,(
% 2.65/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f33,plain,(
% 2.65/0.98    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.65/0.98    inference(ennf_transformation,[],[f11])).
% 2.65/0.98  
% 2.65/0.98  fof(f34,plain,(
% 2.65/0.98    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.65/0.98    inference(flattening,[],[f33])).
% 2.65/0.98  
% 2.65/0.98  fof(f66,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f34])).
% 2.65/0.98  
% 2.65/0.98  fof(f77,plain,(
% 2.65/0.98    v2_funct_1(sK2)),
% 2.65/0.98    inference(cnf_transformation,[],[f47])).
% 2.65/0.98  
% 2.65/0.98  fof(f3,axiom,(
% 2.65/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f20,plain,(
% 2.65/0.98    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.65/0.98    inference(ennf_transformation,[],[f3])).
% 2.65/0.98  
% 2.65/0.98  fof(f21,plain,(
% 2.65/0.98    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.65/0.98    inference(flattening,[],[f20])).
% 2.65/0.98  
% 2.65/0.98  fof(f53,plain,(
% 2.65/0.98    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f21])).
% 2.65/0.98  
% 2.65/0.98  fof(f14,axiom,(
% 2.65/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f38,plain,(
% 2.65/0.98    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.65/0.98    inference(ennf_transformation,[],[f14])).
% 2.65/0.98  
% 2.65/0.98  fof(f39,plain,(
% 2.65/0.98    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.65/0.98    inference(flattening,[],[f38])).
% 2.65/0.98  
% 2.65/0.98  fof(f69,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f39])).
% 2.65/0.98  
% 2.65/0.98  fof(f4,axiom,(
% 2.65/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f22,plain,(
% 2.65/0.98    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.65/0.98    inference(ennf_transformation,[],[f4])).
% 2.65/0.98  
% 2.65/0.98  fof(f23,plain,(
% 2.65/0.98    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.65/0.98    inference(flattening,[],[f22])).
% 2.65/0.98  
% 2.65/0.98  fof(f54,plain,(
% 2.65/0.98    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f23])).
% 2.65/0.98  
% 2.65/0.98  fof(f2,axiom,(
% 2.65/0.98    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f18,plain,(
% 2.65/0.98    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.65/0.98    inference(ennf_transformation,[],[f2])).
% 2.65/0.98  
% 2.65/0.98  fof(f19,plain,(
% 2.65/0.98    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.65/0.98    inference(flattening,[],[f18])).
% 2.65/0.98  
% 2.65/0.98  fof(f51,plain,(
% 2.65/0.98    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f19])).
% 2.65/0.98  
% 2.65/0.98  fof(f50,plain,(
% 2.65/0.98    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f19])).
% 2.65/0.98  
% 2.65/0.98  fof(f65,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f34])).
% 2.65/0.98  
% 2.65/0.98  fof(f9,axiom,(
% 2.65/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f29,plain,(
% 2.65/0.98    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.65/0.98    inference(ennf_transformation,[],[f9])).
% 2.65/0.98  
% 2.65/0.98  fof(f30,plain,(
% 2.65/0.98    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.65/0.98    inference(flattening,[],[f29])).
% 2.65/0.98  
% 2.65/0.98  fof(f43,plain,(
% 2.65/0.98    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.65/0.98    inference(nnf_transformation,[],[f30])).
% 2.65/0.98  
% 2.65/0.98  fof(f61,plain,(
% 2.65/0.98    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f43])).
% 2.65/0.98  
% 2.65/0.98  fof(f80,plain,(
% 2.65/0.98    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.65/0.98    inference(equality_resolution,[],[f61])).
% 2.65/0.98  
% 2.65/0.98  fof(f78,plain,(
% 2.65/0.98    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 2.65/0.98    inference(cnf_transformation,[],[f47])).
% 2.65/0.98  
% 2.65/0.98  cnf(c_25,negated_conjecture,
% 2.65/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.65/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_653,negated_conjecture,
% 2.65/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.65/0.98      inference(subtyping,[status(esa)],[c_25]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1076,plain,
% 2.65/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_653]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_19,plain,
% 2.65/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_30,negated_conjecture,
% 2.65/0.98      ( l1_struct_0(sK0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_378,plain,
% 2.65/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.65/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_379,plain,
% 2.65/0.98      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.65/0.98      inference(unflattening,[status(thm)],[c_378]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_647,plain,
% 2.65/0.98      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.65/0.98      inference(subtyping,[status(esa)],[c_379]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_28,negated_conjecture,
% 2.65/0.98      ( l1_struct_0(sK1) ),
% 2.65/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_373,plain,
% 2.65/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.65/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_374,plain,
% 2.65/0.98      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.65/0.98      inference(unflattening,[status(thm)],[c_373]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_648,plain,
% 2.65/0.98      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.65/0.98      inference(subtyping,[status(esa)],[c_374]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1099,plain,
% 2.65/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.65/0.98      inference(light_normalisation,[status(thm)],[c_1076,c_647,c_648]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_9,plain,
% 2.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_659,plain,
% 2.65/0.98      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.65/0.98      | k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52) ),
% 2.65/0.98      inference(subtyping,[status(esa)],[c_9]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1071,plain,
% 2.65/0.98      ( k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52)
% 2.65/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_659]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1376,plain,
% 2.65/0.98      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_1099,c_1071]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_24,negated_conjecture,
% 2.65/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.65/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_654,negated_conjecture,
% 2.65/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.65/0.98      inference(subtyping,[status(esa)],[c_24]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1096,plain,
% 2.65/0.98      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.65/0.98      inference(light_normalisation,[status(thm)],[c_654,c_647,c_648]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1503,plain,
% 2.65/0.98      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_1376,c_1096]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1556,plain,
% 2.65/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_1503,c_1099]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_15,plain,
% 2.65/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.65/0.98      | v1_partfun1(X0,X1)
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | k1_xboole_0 = X2 ),
% 2.65/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_8,plain,
% 2.65/0.98      ( v4_relat_1(X0,X1)
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.65/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_11,plain,
% 2.65/0.98      ( ~ v1_partfun1(X0,X1)
% 2.65/0.98      | ~ v4_relat_1(X0,X1)
% 2.65/0.98      | ~ v1_relat_1(X0)
% 2.65/0.98      | k1_relat_1(X0) = X1 ),
% 2.65/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_385,plain,
% 2.65/0.98      ( ~ v1_partfun1(X0,X1)
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | ~ v1_relat_1(X0)
% 2.65/0.98      | k1_relat_1(X0) = X1 ),
% 2.65/0.98      inference(resolution,[status(thm)],[c_8,c_11]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_7,plain,
% 2.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | v1_relat_1(X0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_389,plain,
% 2.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | ~ v1_partfun1(X0,X1)
% 2.65/0.98      | k1_relat_1(X0) = X1 ),
% 2.65/0.98      inference(global_propositional_subsumption,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_385,c_11,c_8,c_7]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_390,plain,
% 2.65/0.98      ( ~ v1_partfun1(X0,X1)
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | k1_relat_1(X0) = X1 ),
% 2.65/0.98      inference(renaming,[status(thm)],[c_389]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_452,plain,
% 2.65/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | k1_relat_1(X0) = X1
% 2.65/0.98      | k1_xboole_0 = X2 ),
% 2.65/0.98      inference(resolution,[status(thm)],[c_15,c_390]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_456,plain,
% 2.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | ~ v1_funct_2(X0,X1,X2)
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | k1_relat_1(X0) = X1
% 2.65/0.98      | k1_xboole_0 = X2 ),
% 2.65/0.98      inference(global_propositional_subsumption,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_452,c_15,c_7,c_385]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_457,plain,
% 2.65/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | k1_relat_1(X0) = X1
% 2.65/0.98      | k1_xboole_0 = X2 ),
% 2.65/0.98      inference(renaming,[status(thm)],[c_456]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_645,plain,
% 2.65/0.98      ( ~ v1_funct_2(X0_52,X0_53,X1_53)
% 2.65/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.65/0.98      | ~ v1_funct_1(X0_52)
% 2.65/0.98      | k1_relat_1(X0_52) = X0_53
% 2.65/0.98      | k1_xboole_0 = X1_53 ),
% 2.65/0.98      inference(subtyping,[status(esa)],[c_457]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1081,plain,
% 2.65/0.98      ( k1_relat_1(X0_52) = X0_53
% 2.65/0.98      | k1_xboole_0 = X1_53
% 2.65/0.98      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.65/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.65/0.98      | v1_funct_1(X0_52) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_645]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3178,plain,
% 2.65/0.98      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.65/0.98      | k2_relat_1(sK2) = k1_xboole_0
% 2.65/0.98      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.65/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_1556,c_1081]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_27,negated_conjecture,
% 2.65/0.98      ( v1_funct_1(sK2) ),
% 2.65/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_34,plain,
% 2.65/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_26,negated_conjecture,
% 2.65/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.65/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_652,negated_conjecture,
% 2.65/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.65/0.98      inference(subtyping,[status(esa)],[c_26]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1077,plain,
% 2.65/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_652]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1093,plain,
% 2.65/0.98      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.65/0.98      inference(light_normalisation,[status(thm)],[c_1077,c_647,c_648]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1557,plain,
% 2.65/0.98      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_1503,c_1093]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_0,plain,
% 2.65/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_20,plain,
% 2.65/0.98      ( v2_struct_0(X0)
% 2.65/0.98      | ~ l1_struct_0(X0)
% 2.65/0.98      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 2.65/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_346,plain,
% 2.65/0.98      ( v2_struct_0(X0)
% 2.65/0.98      | ~ l1_struct_0(X0)
% 2.65/0.98      | k2_struct_0(X0) != k1_xboole_0 ),
% 2.65/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_20]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_29,negated_conjecture,
% 2.65/0.98      ( ~ v2_struct_0(sK1) ),
% 2.65/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_364,plain,
% 2.65/0.98      ( ~ l1_struct_0(X0) | k2_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 2.65/0.98      inference(resolution_lifted,[status(thm)],[c_346,c_29]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_365,plain,
% 2.65/0.98      ( ~ l1_struct_0(sK1) | k2_struct_0(sK1) != k1_xboole_0 ),
% 2.65/0.98      inference(unflattening,[status(thm)],[c_364]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_348,plain,
% 2.65/0.98      ( v2_struct_0(sK1)
% 2.65/0.98      | ~ l1_struct_0(sK1)
% 2.65/0.98      | k2_struct_0(sK1) != k1_xboole_0 ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_346]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_367,plain,
% 2.65/0.98      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 2.65/0.98      inference(global_propositional_subsumption,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_365,c_29,c_28,c_348]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_649,plain,
% 2.65/0.98      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 2.65/0.98      inference(subtyping,[status(esa)],[c_367]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1558,plain,
% 2.65/0.98      ( k2_relat_1(sK2) != k1_xboole_0 ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_1503,c_649]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3547,plain,
% 2.65/0.98      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.65/0.98      inference(global_propositional_subsumption,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_3178,c_34,c_1557,c_1558]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1554,plain,
% 2.65/0.98      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_1503,c_1376]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_16,plain,
% 2.65/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | ~ v2_funct_1(X0)
% 2.65/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.65/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_658,plain,
% 2.65/0.98      ( ~ v1_funct_2(X0_52,X0_53,X1_53)
% 2.65/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.65/0.98      | m1_subset_1(k2_funct_1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53)))
% 2.65/0.98      | ~ v1_funct_1(X0_52)
% 2.65/0.98      | ~ v2_funct_1(X0_52)
% 2.65/0.98      | k2_relset_1(X0_53,X1_53,X0_52) != X1_53 ),
% 2.65/0.98      inference(subtyping,[status(esa)],[c_16]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1072,plain,
% 2.65/0.98      ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
% 2.65/0.98      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.65/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.65/0.98      | m1_subset_1(k2_funct_1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) = iProver_top
% 2.65/0.98      | v1_funct_1(X0_52) != iProver_top
% 2.65/0.98      | v2_funct_1(X0_52) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_658]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2333,plain,
% 2.65/0.98      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.65/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 2.65/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.65/0.98      | v1_funct_1(sK2) != iProver_top
% 2.65/0.98      | v2_funct_1(sK2) != iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_1554,c_1072]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_23,negated_conjecture,
% 2.65/0.98      ( v2_funct_1(sK2) ),
% 2.65/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_37,plain,
% 2.65/0.98      ( v2_funct_1(sK2) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2585,plain,
% 2.65/0.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 2.65/0.98      inference(global_propositional_subsumption,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_2333,c_34,c_37,c_1556,c_1557]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2590,plain,
% 2.65/0.98      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_2585,c_1071]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_660,plain,
% 2.65/0.98      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.65/0.98      | v1_relat_1(X0_52) ),
% 2.65/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1070,plain,
% 2.65/0.98      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.65/0.98      | v1_relat_1(X0_52) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_660]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1359,plain,
% 2.65/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_1099,c_1070]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_4,plain,
% 2.65/0.98      ( ~ v1_relat_1(X0)
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | ~ v2_funct_1(X0)
% 2.65/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_663,plain,
% 2.65/0.98      ( ~ v1_relat_1(X0_52)
% 2.65/0.98      | ~ v1_funct_1(X0_52)
% 2.65/0.98      | ~ v2_funct_1(X0_52)
% 2.65/0.98      | k2_relat_1(k2_funct_1(X0_52)) = k1_relat_1(X0_52) ),
% 2.65/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1067,plain,
% 2.65/0.98      ( k2_relat_1(k2_funct_1(X0_52)) = k1_relat_1(X0_52)
% 2.65/0.98      | v1_relat_1(X0_52) != iProver_top
% 2.65/0.98      | v1_funct_1(X0_52) != iProver_top
% 2.65/0.98      | v2_funct_1(X0_52) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_663]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1696,plain,
% 2.65/0.98      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.65/0.98      | v1_funct_1(sK2) != iProver_top
% 2.65/0.98      | v2_funct_1(sK2) != iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_1359,c_1067]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_713,plain,
% 2.65/0.98      ( ~ v1_relat_1(sK2)
% 2.65/0.98      | ~ v1_funct_1(sK2)
% 2.65/0.98      | ~ v2_funct_1(sK2)
% 2.65/0.98      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_663]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1278,plain,
% 2.65/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.65/0.98      | v1_relat_1(sK2) ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_660]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2105,plain,
% 2.65/0.98      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.65/0.98      inference(global_propositional_subsumption,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_1696,c_27,c_25,c_23,c_713,c_1278]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2595,plain,
% 2.65/0.98      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.65/0.98      inference(light_normalisation,[status(thm)],[c_2590,c_2105]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_21,plain,
% 2.65/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | ~ v2_funct_1(X0)
% 2.65/0.98      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.65/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.65/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_656,plain,
% 2.65/0.98      ( ~ v1_funct_2(X0_52,X0_53,X1_53)
% 2.65/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.65/0.98      | ~ v1_funct_1(X0_52)
% 2.65/0.98      | ~ v2_funct_1(X0_52)
% 2.65/0.98      | k2_relset_1(X0_53,X1_53,X0_52) != X1_53
% 2.65/0.98      | k2_tops_2(X0_53,X1_53,X0_52) = k2_funct_1(X0_52) ),
% 2.65/0.98      inference(subtyping,[status(esa)],[c_21]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1074,plain,
% 2.65/0.98      ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
% 2.65/0.98      | k2_tops_2(X0_53,X1_53,X0_52) = k2_funct_1(X0_52)
% 2.65/0.98      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.65/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.65/0.98      | v1_funct_1(X0_52) != iProver_top
% 2.65/0.98      | v2_funct_1(X0_52) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_656]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2686,plain,
% 2.65/0.98      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 2.65/0.98      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.65/0.98      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 2.65/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 2.65/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.65/0.98      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_2595,c_1074]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_6,plain,
% 2.65/0.98      ( ~ v1_relat_1(X0)
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | ~ v2_funct_1(X0)
% 2.65/0.98      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.65/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_661,plain,
% 2.65/0.98      ( ~ v1_relat_1(X0_52)
% 2.65/0.98      | ~ v1_funct_1(X0_52)
% 2.65/0.98      | ~ v2_funct_1(X0_52)
% 2.65/0.98      | k2_funct_1(k2_funct_1(X0_52)) = X0_52 ),
% 2.65/0.98      inference(subtyping,[status(esa)],[c_6]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1069,plain,
% 2.65/0.98      ( k2_funct_1(k2_funct_1(X0_52)) = X0_52
% 2.65/0.98      | v1_relat_1(X0_52) != iProver_top
% 2.65/0.98      | v1_funct_1(X0_52) != iProver_top
% 2.65/0.98      | v2_funct_1(X0_52) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_661]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1792,plain,
% 2.65/0.98      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.65/0.98      | v1_funct_1(sK2) != iProver_top
% 2.65/0.98      | v2_funct_1(sK2) != iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_1359,c_1069]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_719,plain,
% 2.65/0.98      ( ~ v1_relat_1(sK2)
% 2.65/0.98      | ~ v1_funct_1(sK2)
% 2.65/0.98      | ~ v2_funct_1(sK2)
% 2.65/0.98      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_661]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2098,plain,
% 2.65/0.98      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.65/0.98      inference(global_propositional_subsumption,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_1792,c_27,c_25,c_23,c_719,c_1278]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2701,plain,
% 2.65/0.98      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 2.65/0.98      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 2.65/0.98      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 2.65/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 2.65/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.65/0.98      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.65/0.98      inference(light_normalisation,[status(thm)],[c_2686,c_2098]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_36,plain,
% 2.65/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1,plain,
% 2.65/0.98      ( ~ v1_relat_1(X0)
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | ~ v2_funct_1(X0)
% 2.65/0.98      | v2_funct_1(k2_funct_1(X0)) ),
% 2.65/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_666,plain,
% 2.65/0.98      ( ~ v1_relat_1(X0_52)
% 2.65/0.98      | ~ v1_funct_1(X0_52)
% 2.65/0.98      | ~ v2_funct_1(X0_52)
% 2.65/0.98      | v2_funct_1(k2_funct_1(X0_52)) ),
% 2.65/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_703,plain,
% 2.65/0.98      ( v1_relat_1(X0_52) != iProver_top
% 2.65/0.98      | v1_funct_1(X0_52) != iProver_top
% 2.65/0.98      | v2_funct_1(X0_52) != iProver_top
% 2.65/0.98      | v2_funct_1(k2_funct_1(X0_52)) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_666]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_705,plain,
% 2.65/0.98      ( v1_relat_1(sK2) != iProver_top
% 2.65/0.98      | v1_funct_1(sK2) != iProver_top
% 2.65/0.98      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.65/0.98      | v2_funct_1(sK2) != iProver_top ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_703]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2,plain,
% 2.65/0.98      ( ~ v1_relat_1(X0)
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | v1_funct_1(k2_funct_1(X0))
% 2.65/0.98      | ~ v2_funct_1(X0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_665,plain,
% 2.65/0.98      ( ~ v1_relat_1(X0_52)
% 2.65/0.98      | ~ v1_funct_1(X0_52)
% 2.65/0.98      | v1_funct_1(k2_funct_1(X0_52))
% 2.65/0.98      | ~ v2_funct_1(X0_52) ),
% 2.65/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_706,plain,
% 2.65/0.98      ( v1_relat_1(X0_52) != iProver_top
% 2.65/0.98      | v1_funct_1(X0_52) != iProver_top
% 2.65/0.98      | v1_funct_1(k2_funct_1(X0_52)) = iProver_top
% 2.65/0.98      | v2_funct_1(X0_52) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_665]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_708,plain,
% 2.65/0.98      ( v1_relat_1(sK2) != iProver_top
% 2.65/0.98      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.65/0.98      | v1_funct_1(sK2) != iProver_top
% 2.65/0.98      | v2_funct_1(sK2) != iProver_top ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_706]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1279,plain,
% 2.65/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.65/0.98      | v1_relat_1(sK2) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_1278]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_17,plain,
% 2.65/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.65/0.98      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | ~ v2_funct_1(X0)
% 2.65/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.65/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_657,plain,
% 2.65/0.98      ( ~ v1_funct_2(X0_52,X0_53,X1_53)
% 2.65/0.98      | v1_funct_2(k2_funct_1(X0_52),X1_53,X0_53)
% 2.65/0.98      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.65/0.98      | ~ v1_funct_1(X0_52)
% 2.65/0.98      | ~ v2_funct_1(X0_52)
% 2.65/0.98      | k2_relset_1(X0_53,X1_53,X0_52) != X1_53 ),
% 2.65/0.98      inference(subtyping,[status(esa)],[c_17]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1073,plain,
% 2.65/0.98      ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
% 2.65/0.98      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.65/0.98      | v1_funct_2(k2_funct_1(X0_52),X1_53,X0_53) = iProver_top
% 2.65/0.98      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.65/0.98      | v1_funct_1(X0_52) != iProver_top
% 2.65/0.98      | v2_funct_1(X0_52) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_657]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1927,plain,
% 2.65/0.98      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
% 2.65/0.98      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.65/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.65/0.98      | v1_funct_1(sK2) != iProver_top
% 2.65/0.98      | v2_funct_1(sK2) != iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_1554,c_1073]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2822,plain,
% 2.65/0.98      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 2.65/0.98      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
% 2.65/0.98      inference(global_propositional_subsumption,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_2701,c_34,c_36,c_37,c_705,c_708,c_1279,c_1556,c_1557,
% 2.65/0.98                 c_1927,c_2333]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3550,plain,
% 2.65/0.98      ( k1_relat_1(sK2) != k1_relat_1(sK2)
% 2.65/0.98      | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_3547,c_2822]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3584,plain,
% 2.65/0.98      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 2.65/0.98      inference(equality_resolution_simp,[status(thm)],[c_3550]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1936,plain,
% 2.65/0.98      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 2.65/0.98      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.65/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.65/0.98      | v1_funct_1(sK2) != iProver_top
% 2.65/0.98      | v2_funct_1(sK2) != iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_1554,c_1074]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2245,plain,
% 2.65/0.98      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.65/0.98      inference(global_propositional_subsumption,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_1936,c_34,c_37,c_1556,c_1557]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_12,plain,
% 2.65/0.98      ( r2_funct_2(X0,X1,X2,X2)
% 2.65/0.98      | ~ v1_funct_2(X2,X0,X1)
% 2.65/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.65/0.98      | ~ v1_funct_1(X2) ),
% 2.65/0.98      inference(cnf_transformation,[],[f80]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_22,negated_conjecture,
% 2.65/0.98      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 2.65/0.98      inference(cnf_transformation,[],[f78]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_431,plain,
% 2.65/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 2.65/0.98      | u1_struct_0(sK1) != X2
% 2.65/0.98      | u1_struct_0(sK0) != X1
% 2.65/0.98      | sK2 != X0 ),
% 2.65/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_432,plain,
% 2.65/0.98      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.65/0.98      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.65/0.98      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.65/0.98      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.65/0.98      inference(unflattening,[status(thm)],[c_431]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_646,plain,
% 2.65/0.98      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.65/0.98      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.65/0.98      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.65/0.98      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.65/0.98      inference(subtyping,[status(esa)],[c_432]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1080,plain,
% 2.65/0.98      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.65/0.98      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.65/0.98      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.65/0.98      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_646]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1222,plain,
% 2.65/0.98      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.65/0.98      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.65/0.98      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.65/0.98      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.65/0.98      inference(light_normalisation,[status(thm)],[c_1080,c_647,c_648]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1555,plain,
% 2.65/0.98      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
% 2.65/0.98      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.65/0.98      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.65/0.98      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_1503,c_1222]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2248,plain,
% 2.65/0.98      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 2.65/0.98      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.65/0.98      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.65/0.98      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_2245,c_1555]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3553,plain,
% 2.65/0.98      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 2.65/0.98      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.65/0.98      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.65/0.98      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_3547,c_2248]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3586,plain,
% 2.65/0.98      ( sK2 != sK2
% 2.65/0.98      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.65/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.65/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_3584,c_3553]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3588,plain,
% 2.65/0.98      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.65/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.65/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.65/0.98      inference(equality_resolution_simp,[status(thm)],[c_3586]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3556,plain,
% 2.65/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_3547,c_1556]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3558,plain,
% 2.65/0.98      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_3547,c_1557]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3592,plain,
% 2.65/0.98      ( v1_funct_1(sK2) != iProver_top ),
% 2.65/0.98      inference(forward_subsumption_resolution,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_3588,c_3556,c_3558]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(contradiction,plain,
% 2.65/0.98      ( $false ),
% 2.65/0.98      inference(minisat,[status(thm)],[c_3592,c_34]) ).
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.65/0.98  
% 2.65/0.98  ------                               Statistics
% 2.65/0.98  
% 2.65/0.98  ------ General
% 2.65/0.98  
% 2.65/0.98  abstr_ref_over_cycles:                  0
% 2.65/0.98  abstr_ref_under_cycles:                 0
% 2.65/0.98  gc_basic_clause_elim:                   0
% 2.65/0.98  forced_gc_time:                         0
% 2.65/0.98  parsing_time:                           0.009
% 2.65/0.98  unif_index_cands_time:                  0.
% 2.65/0.98  unif_index_add_time:                    0.
% 2.65/0.98  orderings_time:                         0.
% 2.65/0.98  out_proof_time:                         0.015
% 2.65/0.98  total_time:                             0.157
% 2.65/0.98  num_of_symbols:                         57
% 2.65/0.98  num_of_terms:                           3053
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing
% 2.65/0.98  
% 2.65/0.98  num_of_splits:                          0
% 2.65/0.98  num_of_split_atoms:                     0
% 2.65/0.98  num_of_reused_defs:                     0
% 2.65/0.98  num_eq_ax_congr_red:                    4
% 2.65/0.98  num_of_sem_filtered_clauses:            1
% 2.65/0.98  num_of_subtypes:                        5
% 2.65/0.98  monotx_restored_types:                  1
% 2.65/0.98  sat_num_of_epr_types:                   0
% 2.65/0.98  sat_num_of_non_cyclic_types:            0
% 2.65/0.98  sat_guarded_non_collapsed_types:        1
% 2.65/0.98  num_pure_diseq_elim:                    0
% 2.65/0.98  simp_replaced_by:                       0
% 2.65/0.98  res_preprocessed:                       137
% 2.65/0.98  prep_upred:                             0
% 2.65/0.98  prep_unflattend:                        16
% 2.65/0.98  smt_new_axioms:                         0
% 2.65/0.98  pred_elim_cands:                        5
% 2.65/0.98  pred_elim:                              6
% 2.65/0.98  pred_elim_cl:                           8
% 2.65/0.98  pred_elim_cycles:                       8
% 2.65/0.98  merged_defs:                            0
% 2.65/0.98  merged_defs_ncl:                        0
% 2.65/0.98  bin_hyper_res:                          0
% 2.65/0.98  prep_cycles:                            4
% 2.65/0.98  pred_elim_time:                         0.005
% 2.65/0.98  splitting_time:                         0.
% 2.65/0.98  sem_filter_time:                        0.
% 2.65/0.98  monotx_time:                            0.001
% 2.65/0.98  subtype_inf_time:                       0.001
% 2.65/0.98  
% 2.65/0.98  ------ Problem properties
% 2.65/0.98  
% 2.65/0.98  clauses:                                23
% 2.65/0.98  conjectures:                            5
% 2.65/0.98  epr:                                    2
% 2.65/0.98  horn:                                   22
% 2.65/0.98  ground:                                 9
% 2.65/0.98  unary:                                  8
% 2.65/0.98  binary:                                 2
% 2.65/0.98  lits:                                   72
% 2.65/0.98  lits_eq:                                16
% 2.65/0.98  fd_pure:                                0
% 2.65/0.98  fd_pseudo:                              0
% 2.65/0.98  fd_cond:                                0
% 2.65/0.98  fd_pseudo_cond:                         1
% 2.65/0.98  ac_symbols:                             0
% 2.65/0.98  
% 2.65/0.98  ------ Propositional Solver
% 2.65/0.98  
% 2.65/0.98  prop_solver_calls:                      29
% 2.65/0.98  prop_fast_solver_calls:                 1083
% 2.65/0.98  smt_solver_calls:                       0
% 2.65/0.98  smt_fast_solver_calls:                  0
% 2.65/0.98  prop_num_of_clauses:                    1209
% 2.65/0.98  prop_preprocess_simplified:             4595
% 2.65/0.98  prop_fo_subsumed:                       50
% 2.65/0.98  prop_solver_time:                       0.
% 2.65/0.98  smt_solver_time:                        0.
% 2.65/0.98  smt_fast_solver_time:                   0.
% 2.65/0.98  prop_fast_solver_time:                  0.
% 2.65/0.98  prop_unsat_core_time:                   0.
% 2.65/0.98  
% 2.65/0.98  ------ QBF
% 2.65/0.98  
% 2.65/0.98  qbf_q_res:                              0
% 2.65/0.98  qbf_num_tautologies:                    0
% 2.65/0.98  qbf_prep_cycles:                        0
% 2.65/0.98  
% 2.65/0.98  ------ BMC1
% 2.65/0.98  
% 2.65/0.98  bmc1_current_bound:                     -1
% 2.65/0.98  bmc1_last_solved_bound:                 -1
% 2.65/0.98  bmc1_unsat_core_size:                   -1
% 2.65/0.98  bmc1_unsat_core_parents_size:           -1
% 2.65/0.98  bmc1_merge_next_fun:                    0
% 2.65/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.65/0.98  
% 2.65/0.98  ------ Instantiation
% 2.65/0.98  
% 2.65/0.98  inst_num_of_clauses:                    404
% 2.65/0.98  inst_num_in_passive:                    123
% 2.65/0.98  inst_num_in_active:                     221
% 2.65/0.98  inst_num_in_unprocessed:                60
% 2.65/0.98  inst_num_of_loops:                      270
% 2.65/0.98  inst_num_of_learning_restarts:          0
% 2.65/0.98  inst_num_moves_active_passive:          45
% 2.65/0.98  inst_lit_activity:                      0
% 2.65/0.98  inst_lit_activity_moves:                0
% 2.65/0.98  inst_num_tautologies:                   0
% 2.65/0.98  inst_num_prop_implied:                  0
% 2.65/0.98  inst_num_existing_simplified:           0
% 2.65/0.98  inst_num_eq_res_simplified:             0
% 2.65/0.98  inst_num_child_elim:                    0
% 2.65/0.98  inst_num_of_dismatching_blockings:      70
% 2.65/0.98  inst_num_of_non_proper_insts:           350
% 2.65/0.98  inst_num_of_duplicates:                 0
% 2.65/0.98  inst_inst_num_from_inst_to_res:         0
% 2.65/0.98  inst_dismatching_checking_time:         0.
% 2.65/0.98  
% 2.65/0.98  ------ Resolution
% 2.65/0.98  
% 2.65/0.98  res_num_of_clauses:                     0
% 2.65/0.98  res_num_in_passive:                     0
% 2.65/0.98  res_num_in_active:                      0
% 2.65/0.98  res_num_of_loops:                       141
% 2.65/0.98  res_forward_subset_subsumed:            48
% 2.65/0.98  res_backward_subset_subsumed:           0
% 2.65/0.98  res_forward_subsumed:                   0
% 2.65/0.98  res_backward_subsumed:                  0
% 2.65/0.98  res_forward_subsumption_resolution:     1
% 2.65/0.98  res_backward_subsumption_resolution:    0
% 2.65/0.98  res_clause_to_clause_subsumption:       210
% 2.65/0.98  res_orphan_elimination:                 0
% 2.65/0.98  res_tautology_del:                      30
% 2.65/0.98  res_num_eq_res_simplified:              0
% 2.65/0.98  res_num_sel_changes:                    0
% 2.65/0.98  res_moves_from_active_to_pass:          0
% 2.65/0.98  
% 2.65/0.98  ------ Superposition
% 2.65/0.98  
% 2.65/0.98  sup_time_total:                         0.
% 2.65/0.98  sup_time_generating:                    0.
% 2.65/0.98  sup_time_sim_full:                      0.
% 2.65/0.98  sup_time_sim_immed:                     0.
% 2.65/0.98  
% 2.65/0.98  sup_num_of_clauses:                     48
% 2.65/0.98  sup_num_in_active:                      34
% 2.65/0.98  sup_num_in_passive:                     14
% 2.65/0.98  sup_num_of_loops:                       52
% 2.65/0.98  sup_fw_superposition:                   38
% 2.65/0.98  sup_bw_superposition:                   17
% 2.65/0.98  sup_immediate_simplified:               32
% 2.65/0.98  sup_given_eliminated:                   0
% 2.65/0.98  comparisons_done:                       0
% 2.65/0.98  comparisons_avoided:                    0
% 2.65/0.98  
% 2.65/0.98  ------ Simplifications
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  sim_fw_subset_subsumed:                 4
% 2.65/0.98  sim_bw_subset_subsumed:                 0
% 2.65/0.98  sim_fw_subsumed:                        3
% 2.65/0.98  sim_bw_subsumed:                        0
% 2.65/0.98  sim_fw_subsumption_res:                 2
% 2.65/0.98  sim_bw_subsumption_res:                 0
% 2.65/0.98  sim_tautology_del:                      0
% 2.65/0.98  sim_eq_tautology_del:                   21
% 2.65/0.98  sim_eq_res_simp:                        2
% 2.65/0.98  sim_fw_demodulated:                     0
% 2.65/0.98  sim_bw_demodulated:                     19
% 2.65/0.98  sim_light_normalised:                   30
% 2.65/0.98  sim_joinable_taut:                      0
% 2.65/0.98  sim_joinable_simp:                      0
% 2.65/0.98  sim_ac_normalised:                      0
% 2.65/0.98  sim_smt_subsumption:                    0
% 2.65/0.98  
%------------------------------------------------------------------------------
