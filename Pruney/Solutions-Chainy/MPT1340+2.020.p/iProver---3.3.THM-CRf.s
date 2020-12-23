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
% DateTime   : Thu Dec  3 12:17:25 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :  196 (4590 expanded)
%              Number of clauses        :  125 (1461 expanded)
%              Number of leaves         :   18 (1280 expanded)
%              Depth                    :   26
%              Number of atoms          :  713 (28168 expanded)
%              Number of equality atoms :  271 (5040 expanded)
%              Maximal formula depth    :   12 (   5 average)
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

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f46,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f45,f44,f43])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f65,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f60,plain,(
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

fof(f55,plain,(
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

fof(f57,plain,(
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

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f52,plain,(
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

fof(f67,plain,(
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

fof(f53,plain,(
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

fof(f50,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f63,plain,(
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
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_654,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1095,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_654])).

cnf(c_18,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_29,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_367,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_368,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_648,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_368])).

cnf(c_27,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_362,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_363,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_649,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_363])).

cnf(c_1122,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1095,c_648,c_649])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_660,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1090,plain,
    ( k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_660])).

cnf(c_1409,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1122,c_1090])).

cnf(c_23,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_655,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1119,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_655,c_648,c_649])).

cnf(c_1549,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1409,c_1119])).

cnf(c_1592,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1549,c_1122])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_8,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_11,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_409,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_8,c_11])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_413,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_409,c_11,c_8,c_7])).

cnf(c_414,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_413])).

cnf(c_453,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_14,c_414])).

cnf(c_457,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_453,c_14,c_7,c_409])).

cnf(c_458,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_457])).

cnf(c_646,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X1_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | k1_relat_1(X0_52) = X0_53
    | k1_xboole_0 = X1_53 ),
    inference(subtyping,[status(esa)],[c_458])).

cnf(c_1101,plain,
    ( k1_relat_1(X0_52) = X0_53
    | k1_xboole_0 = X1_53
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_646])).

cnf(c_3177,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1592,c_1101])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_33,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_653,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1096,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_653])).

cnf(c_1116,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1096,c_648,c_649])).

cnf(c_1593,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1549,c_1116])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_19,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_335,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_19])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_353,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_335,c_28])).

cnf(c_354,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_337,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_335])).

cnf(c_356,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_354,c_28,c_27,c_337])).

cnf(c_650,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_356])).

cnf(c_1110,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_649,c_650])).

cnf(c_1594,plain,
    ( k2_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1549,c_1110])).

cnf(c_3562,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3177,c_33,c_1593,c_1594])).

cnf(c_1591,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1549,c_1409])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_659,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X1_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | m1_subset_1(k2_funct_1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | k2_relset_1(X0_53,X1_53,X0_52) != X1_53 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1091,plain,
    ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_659])).

cnf(c_2387,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1591,c_1091])).

cnf(c_22,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_36,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2658,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2387,c_33,c_36,c_1592,c_1593])).

cnf(c_2663,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2658,c_1090])).

cnf(c_661,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | v1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1089,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_relat_1(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_661])).

cnf(c_1392,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1122,c_1089])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_664,plain,
    ( ~ v1_relat_1(X0_52)
    | ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | k2_relat_1(k2_funct_1(X0_52)) = k1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1086,plain,
    ( k2_relat_1(k2_funct_1(X0_52)) = k1_relat_1(X0_52)
    | v1_relat_1(X0_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_1756,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1392,c_1086])).

cnf(c_716,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_664])).

cnf(c_1313,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_661])).

cnf(c_2156,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1756,c_26,c_24,c_22,c_716,c_1313])).

cnf(c_2668,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2663,c_2156])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_657,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X1_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | k2_relset_1(X0_53,X1_53,X0_52) != X1_53
    | k2_tops_2(X0_53,X1_53,X0_52) = k2_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1093,plain,
    ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
    | k2_tops_2(X0_53,X1_53,X0_52) = k2_funct_1(X0_52)
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_657])).

cnf(c_2756,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2668,c_1093])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_662,plain,
    ( ~ v1_relat_1(X0_52)
    | ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | k2_funct_1(k2_funct_1(X0_52)) = X0_52 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1088,plain,
    ( k2_funct_1(k2_funct_1(X0_52)) = X0_52
    | v1_relat_1(X0_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_662])).

cnf(c_1872,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1392,c_1088])).

cnf(c_722,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_662])).

cnf(c_2149,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1872,c_26,c_24,c_22,c_722,c_1313])).

cnf(c_2771,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2756,c_2149])).

cnf(c_35,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_667,plain,
    ( ~ v1_relat_1(X0_52)
    | ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | v2_funct_1(k2_funct_1(X0_52)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_706,plain,
    ( v1_relat_1(X0_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top
    | v2_funct_1(k2_funct_1(X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_667])).

cnf(c_708,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_706])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_666,plain,
    ( ~ v1_relat_1(X0_52)
    | ~ v1_funct_1(X0_52)
    | v1_funct_1(k2_funct_1(X0_52))
    | ~ v2_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_709,plain,
    ( v1_relat_1(X0_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k2_funct_1(X0_52)) = iProver_top
    | v2_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_666])).

cnf(c_711,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_709])).

cnf(c_1314,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1313])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_658,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X1_53)
    | v1_funct_2(k2_funct_1(X0_52),X1_53,X0_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | k2_relset_1(X0_53,X1_53,X0_52) != X1_53 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1092,plain,
    ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | v1_funct_2(k2_funct_1(X0_52),X1_53,X0_53) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_658])).

cnf(c_2019,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1591,c_1092])).

cnf(c_2922,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2771,c_33,c_35,c_36,c_708,c_711,c_1314,c_1592,c_1593,c_2019,c_2387])).

cnf(c_3565,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_3562,c_2922])).

cnf(c_3599,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_3565])).

cnf(c_2028,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1591,c_1093])).

cnf(c_2326,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2028,c_33,c_36,c_1592,c_1593])).

cnf(c_12,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_21,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_374,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X3
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_375,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_647,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_375])).

cnf(c_669,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sP0_iProver_split
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_647])).

cnf(c_1099,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_669])).

cnf(c_1254,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1099,c_648,c_649])).

cnf(c_668,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_52)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_647])).

cnf(c_1100,plain,
    ( v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_668])).

cnf(c_1189,plain,
    ( v1_funct_2(X0_52,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1100,c_648,c_649])).

cnf(c_1260,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1254,c_1189])).

cnf(c_2111,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1260,c_1549])).

cnf(c_2329,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2326,c_2111])).

cnf(c_3568,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3562,c_2329])).

cnf(c_3601,plain,
    ( sK2 != sK2
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3599,c_3568])).

cnf(c_3603,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3601])).

cnf(c_3571,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3562,c_1592])).

cnf(c_3573,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3562,c_1593])).

cnf(c_3607,plain,
    ( v1_funct_1(sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3603,c_3571,c_3573])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3607,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:24:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.78/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.00  
% 2.78/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.78/1.00  
% 2.78/1.00  ------  iProver source info
% 2.78/1.00  
% 2.78/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.78/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.78/1.00  git: non_committed_changes: false
% 2.78/1.00  git: last_make_outside_of_git: false
% 2.78/1.00  
% 2.78/1.00  ------ 
% 2.78/1.00  
% 2.78/1.00  ------ Input Options
% 2.78/1.00  
% 2.78/1.00  --out_options                           all
% 2.78/1.00  --tptp_safe_out                         true
% 2.78/1.00  --problem_path                          ""
% 2.78/1.00  --include_path                          ""
% 2.78/1.00  --clausifier                            res/vclausify_rel
% 2.78/1.00  --clausifier_options                    --mode clausify
% 2.78/1.00  --stdin                                 false
% 2.78/1.00  --stats_out                             all
% 2.78/1.00  
% 2.78/1.00  ------ General Options
% 2.78/1.00  
% 2.78/1.00  --fof                                   false
% 2.78/1.00  --time_out_real                         305.
% 2.78/1.00  --time_out_virtual                      -1.
% 2.78/1.00  --symbol_type_check                     false
% 2.78/1.00  --clausify_out                          false
% 2.78/1.00  --sig_cnt_out                           false
% 2.78/1.00  --trig_cnt_out                          false
% 2.78/1.00  --trig_cnt_out_tolerance                1.
% 2.78/1.00  --trig_cnt_out_sk_spl                   false
% 2.78/1.00  --abstr_cl_out                          false
% 2.78/1.00  
% 2.78/1.00  ------ Global Options
% 2.78/1.00  
% 2.78/1.00  --schedule                              default
% 2.78/1.00  --add_important_lit                     false
% 2.78/1.00  --prop_solver_per_cl                    1000
% 2.78/1.00  --min_unsat_core                        false
% 2.78/1.00  --soft_assumptions                      false
% 2.78/1.00  --soft_lemma_size                       3
% 2.78/1.00  --prop_impl_unit_size                   0
% 2.78/1.00  --prop_impl_unit                        []
% 2.78/1.00  --share_sel_clauses                     true
% 2.78/1.00  --reset_solvers                         false
% 2.78/1.00  --bc_imp_inh                            [conj_cone]
% 2.78/1.00  --conj_cone_tolerance                   3.
% 2.78/1.00  --extra_neg_conj                        none
% 2.78/1.00  --large_theory_mode                     true
% 2.78/1.00  --prolific_symb_bound                   200
% 2.78/1.00  --lt_threshold                          2000
% 2.78/1.00  --clause_weak_htbl                      true
% 2.78/1.00  --gc_record_bc_elim                     false
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing Options
% 2.78/1.00  
% 2.78/1.00  --preprocessing_flag                    true
% 2.78/1.00  --time_out_prep_mult                    0.1
% 2.78/1.00  --splitting_mode                        input
% 2.78/1.00  --splitting_grd                         true
% 2.78/1.00  --splitting_cvd                         false
% 2.78/1.00  --splitting_cvd_svl                     false
% 2.78/1.00  --splitting_nvd                         32
% 2.78/1.00  --sub_typing                            true
% 2.78/1.00  --prep_gs_sim                           true
% 2.78/1.00  --prep_unflatten                        true
% 2.78/1.00  --prep_res_sim                          true
% 2.78/1.00  --prep_upred                            true
% 2.78/1.00  --prep_sem_filter                       exhaustive
% 2.78/1.00  --prep_sem_filter_out                   false
% 2.78/1.00  --pred_elim                             true
% 2.78/1.00  --res_sim_input                         true
% 2.78/1.00  --eq_ax_congr_red                       true
% 2.78/1.00  --pure_diseq_elim                       true
% 2.78/1.00  --brand_transform                       false
% 2.78/1.00  --non_eq_to_eq                          false
% 2.78/1.00  --prep_def_merge                        true
% 2.78/1.00  --prep_def_merge_prop_impl              false
% 2.78/1.00  --prep_def_merge_mbd                    true
% 2.78/1.00  --prep_def_merge_tr_red                 false
% 2.78/1.00  --prep_def_merge_tr_cl                  false
% 2.78/1.00  --smt_preprocessing                     true
% 2.78/1.00  --smt_ac_axioms                         fast
% 2.78/1.00  --preprocessed_out                      false
% 2.78/1.00  --preprocessed_stats                    false
% 2.78/1.00  
% 2.78/1.00  ------ Abstraction refinement Options
% 2.78/1.00  
% 2.78/1.00  --abstr_ref                             []
% 2.78/1.00  --abstr_ref_prep                        false
% 2.78/1.00  --abstr_ref_until_sat                   false
% 2.78/1.00  --abstr_ref_sig_restrict                funpre
% 2.78/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/1.00  --abstr_ref_under                       []
% 2.78/1.00  
% 2.78/1.00  ------ SAT Options
% 2.78/1.00  
% 2.78/1.00  --sat_mode                              false
% 2.78/1.00  --sat_fm_restart_options                ""
% 2.78/1.00  --sat_gr_def                            false
% 2.78/1.00  --sat_epr_types                         true
% 2.78/1.00  --sat_non_cyclic_types                  false
% 2.78/1.00  --sat_finite_models                     false
% 2.78/1.00  --sat_fm_lemmas                         false
% 2.78/1.00  --sat_fm_prep                           false
% 2.78/1.00  --sat_fm_uc_incr                        true
% 2.78/1.00  --sat_out_model                         small
% 2.78/1.00  --sat_out_clauses                       false
% 2.78/1.00  
% 2.78/1.00  ------ QBF Options
% 2.78/1.00  
% 2.78/1.00  --qbf_mode                              false
% 2.78/1.00  --qbf_elim_univ                         false
% 2.78/1.00  --qbf_dom_inst                          none
% 2.78/1.00  --qbf_dom_pre_inst                      false
% 2.78/1.00  --qbf_sk_in                             false
% 2.78/1.00  --qbf_pred_elim                         true
% 2.78/1.00  --qbf_split                             512
% 2.78/1.00  
% 2.78/1.00  ------ BMC1 Options
% 2.78/1.00  
% 2.78/1.00  --bmc1_incremental                      false
% 2.78/1.00  --bmc1_axioms                           reachable_all
% 2.78/1.00  --bmc1_min_bound                        0
% 2.78/1.00  --bmc1_max_bound                        -1
% 2.78/1.00  --bmc1_max_bound_default                -1
% 2.78/1.00  --bmc1_symbol_reachability              true
% 2.78/1.00  --bmc1_property_lemmas                  false
% 2.78/1.00  --bmc1_k_induction                      false
% 2.78/1.00  --bmc1_non_equiv_states                 false
% 2.78/1.00  --bmc1_deadlock                         false
% 2.78/1.00  --bmc1_ucm                              false
% 2.78/1.00  --bmc1_add_unsat_core                   none
% 2.78/1.00  --bmc1_unsat_core_children              false
% 2.78/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/1.00  --bmc1_out_stat                         full
% 2.78/1.00  --bmc1_ground_init                      false
% 2.78/1.00  --bmc1_pre_inst_next_state              false
% 2.78/1.00  --bmc1_pre_inst_state                   false
% 2.78/1.00  --bmc1_pre_inst_reach_state             false
% 2.78/1.00  --bmc1_out_unsat_core                   false
% 2.78/1.00  --bmc1_aig_witness_out                  false
% 2.78/1.00  --bmc1_verbose                          false
% 2.78/1.00  --bmc1_dump_clauses_tptp                false
% 2.78/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.78/1.00  --bmc1_dump_file                        -
% 2.78/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.78/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.78/1.00  --bmc1_ucm_extend_mode                  1
% 2.78/1.00  --bmc1_ucm_init_mode                    2
% 2.78/1.00  --bmc1_ucm_cone_mode                    none
% 2.78/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.78/1.00  --bmc1_ucm_relax_model                  4
% 2.78/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.78/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/1.00  --bmc1_ucm_layered_model                none
% 2.78/1.00  --bmc1_ucm_max_lemma_size               10
% 2.78/1.00  
% 2.78/1.00  ------ AIG Options
% 2.78/1.00  
% 2.78/1.00  --aig_mode                              false
% 2.78/1.00  
% 2.78/1.00  ------ Instantiation Options
% 2.78/1.00  
% 2.78/1.00  --instantiation_flag                    true
% 2.78/1.00  --inst_sos_flag                         false
% 2.78/1.00  --inst_sos_phase                        true
% 2.78/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/1.00  --inst_lit_sel_side                     num_symb
% 2.78/1.00  --inst_solver_per_active                1400
% 2.78/1.00  --inst_solver_calls_frac                1.
% 2.78/1.00  --inst_passive_queue_type               priority_queues
% 2.78/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/1.00  --inst_passive_queues_freq              [25;2]
% 2.78/1.00  --inst_dismatching                      true
% 2.78/1.00  --inst_eager_unprocessed_to_passive     true
% 2.78/1.00  --inst_prop_sim_given                   true
% 2.78/1.00  --inst_prop_sim_new                     false
% 2.78/1.00  --inst_subs_new                         false
% 2.78/1.00  --inst_eq_res_simp                      false
% 2.78/1.00  --inst_subs_given                       false
% 2.78/1.00  --inst_orphan_elimination               true
% 2.78/1.00  --inst_learning_loop_flag               true
% 2.78/1.00  --inst_learning_start                   3000
% 2.78/1.00  --inst_learning_factor                  2
% 2.78/1.00  --inst_start_prop_sim_after_learn       3
% 2.78/1.00  --inst_sel_renew                        solver
% 2.78/1.00  --inst_lit_activity_flag                true
% 2.78/1.00  --inst_restr_to_given                   false
% 2.78/1.00  --inst_activity_threshold               500
% 2.78/1.00  --inst_out_proof                        true
% 2.78/1.00  
% 2.78/1.00  ------ Resolution Options
% 2.78/1.00  
% 2.78/1.00  --resolution_flag                       true
% 2.78/1.00  --res_lit_sel                           adaptive
% 2.78/1.00  --res_lit_sel_side                      none
% 2.78/1.00  --res_ordering                          kbo
% 2.78/1.00  --res_to_prop_solver                    active
% 2.78/1.00  --res_prop_simpl_new                    false
% 2.78/1.00  --res_prop_simpl_given                  true
% 2.78/1.00  --res_passive_queue_type                priority_queues
% 2.78/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/1.00  --res_passive_queues_freq               [15;5]
% 2.78/1.00  --res_forward_subs                      full
% 2.78/1.00  --res_backward_subs                     full
% 2.78/1.00  --res_forward_subs_resolution           true
% 2.78/1.00  --res_backward_subs_resolution          true
% 2.78/1.00  --res_orphan_elimination                true
% 2.78/1.00  --res_time_limit                        2.
% 2.78/1.00  --res_out_proof                         true
% 2.78/1.00  
% 2.78/1.00  ------ Superposition Options
% 2.78/1.00  
% 2.78/1.00  --superposition_flag                    true
% 2.78/1.00  --sup_passive_queue_type                priority_queues
% 2.78/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.78/1.00  --demod_completeness_check              fast
% 2.78/1.00  --demod_use_ground                      true
% 2.78/1.00  --sup_to_prop_solver                    passive
% 2.78/1.00  --sup_prop_simpl_new                    true
% 2.78/1.00  --sup_prop_simpl_given                  true
% 2.78/1.00  --sup_fun_splitting                     false
% 2.78/1.00  --sup_smt_interval                      50000
% 2.78/1.00  
% 2.78/1.00  ------ Superposition Simplification Setup
% 2.78/1.00  
% 2.78/1.00  --sup_indices_passive                   []
% 2.78/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_full_bw                           [BwDemod]
% 2.78/1.00  --sup_immed_triv                        [TrivRules]
% 2.78/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_immed_bw_main                     []
% 2.78/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.00  
% 2.78/1.00  ------ Combination Options
% 2.78/1.00  
% 2.78/1.00  --comb_res_mult                         3
% 2.78/1.00  --comb_sup_mult                         2
% 2.78/1.00  --comb_inst_mult                        10
% 2.78/1.00  
% 2.78/1.00  ------ Debug Options
% 2.78/1.00  
% 2.78/1.00  --dbg_backtrace                         false
% 2.78/1.00  --dbg_dump_prop_clauses                 false
% 2.78/1.00  --dbg_dump_prop_clauses_file            -
% 2.78/1.00  --dbg_out_stat                          false
% 2.78/1.00  ------ Parsing...
% 2.78/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.78/1.00  ------ Proving...
% 2.78/1.00  ------ Problem Properties 
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  clauses                                 24
% 2.78/1.00  conjectures                             5
% 2.78/1.00  EPR                                     2
% 2.78/1.00  Horn                                    23
% 2.78/1.00  unary                                   8
% 2.78/1.00  binary                                  2
% 2.78/1.00  lits                                    77
% 2.78/1.00  lits eq                                 16
% 2.78/1.00  fd_pure                                 0
% 2.78/1.00  fd_pseudo                               0
% 2.78/1.00  fd_cond                                 0
% 2.78/1.00  fd_pseudo_cond                          1
% 2.78/1.00  AC symbols                              0
% 2.78/1.00  
% 2.78/1.00  ------ Schedule dynamic 5 is on 
% 2.78/1.00  
% 2.78/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  ------ 
% 2.78/1.00  Current options:
% 2.78/1.00  ------ 
% 2.78/1.00  
% 2.78/1.00  ------ Input Options
% 2.78/1.00  
% 2.78/1.00  --out_options                           all
% 2.78/1.00  --tptp_safe_out                         true
% 2.78/1.00  --problem_path                          ""
% 2.78/1.00  --include_path                          ""
% 2.78/1.00  --clausifier                            res/vclausify_rel
% 2.78/1.00  --clausifier_options                    --mode clausify
% 2.78/1.00  --stdin                                 false
% 2.78/1.00  --stats_out                             all
% 2.78/1.00  
% 2.78/1.00  ------ General Options
% 2.78/1.00  
% 2.78/1.00  --fof                                   false
% 2.78/1.00  --time_out_real                         305.
% 2.78/1.00  --time_out_virtual                      -1.
% 2.78/1.00  --symbol_type_check                     false
% 2.78/1.00  --clausify_out                          false
% 2.78/1.00  --sig_cnt_out                           false
% 2.78/1.00  --trig_cnt_out                          false
% 2.78/1.00  --trig_cnt_out_tolerance                1.
% 2.78/1.00  --trig_cnt_out_sk_spl                   false
% 2.78/1.00  --abstr_cl_out                          false
% 2.78/1.00  
% 2.78/1.00  ------ Global Options
% 2.78/1.00  
% 2.78/1.00  --schedule                              default
% 2.78/1.00  --add_important_lit                     false
% 2.78/1.00  --prop_solver_per_cl                    1000
% 2.78/1.00  --min_unsat_core                        false
% 2.78/1.00  --soft_assumptions                      false
% 2.78/1.00  --soft_lemma_size                       3
% 2.78/1.00  --prop_impl_unit_size                   0
% 2.78/1.00  --prop_impl_unit                        []
% 2.78/1.00  --share_sel_clauses                     true
% 2.78/1.00  --reset_solvers                         false
% 2.78/1.00  --bc_imp_inh                            [conj_cone]
% 2.78/1.00  --conj_cone_tolerance                   3.
% 2.78/1.00  --extra_neg_conj                        none
% 2.78/1.00  --large_theory_mode                     true
% 2.78/1.00  --prolific_symb_bound                   200
% 2.78/1.00  --lt_threshold                          2000
% 2.78/1.00  --clause_weak_htbl                      true
% 2.78/1.00  --gc_record_bc_elim                     false
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing Options
% 2.78/1.00  
% 2.78/1.00  --preprocessing_flag                    true
% 2.78/1.00  --time_out_prep_mult                    0.1
% 2.78/1.00  --splitting_mode                        input
% 2.78/1.00  --splitting_grd                         true
% 2.78/1.00  --splitting_cvd                         false
% 2.78/1.00  --splitting_cvd_svl                     false
% 2.78/1.00  --splitting_nvd                         32
% 2.78/1.00  --sub_typing                            true
% 2.78/1.00  --prep_gs_sim                           true
% 2.78/1.00  --prep_unflatten                        true
% 2.78/1.00  --prep_res_sim                          true
% 2.78/1.00  --prep_upred                            true
% 2.78/1.00  --prep_sem_filter                       exhaustive
% 2.78/1.00  --prep_sem_filter_out                   false
% 2.78/1.00  --pred_elim                             true
% 2.78/1.00  --res_sim_input                         true
% 2.78/1.00  --eq_ax_congr_red                       true
% 2.78/1.00  --pure_diseq_elim                       true
% 2.78/1.00  --brand_transform                       false
% 2.78/1.00  --non_eq_to_eq                          false
% 2.78/1.00  --prep_def_merge                        true
% 2.78/1.00  --prep_def_merge_prop_impl              false
% 2.78/1.00  --prep_def_merge_mbd                    true
% 2.78/1.00  --prep_def_merge_tr_red                 false
% 2.78/1.00  --prep_def_merge_tr_cl                  false
% 2.78/1.00  --smt_preprocessing                     true
% 2.78/1.00  --smt_ac_axioms                         fast
% 2.78/1.00  --preprocessed_out                      false
% 2.78/1.00  --preprocessed_stats                    false
% 2.78/1.00  
% 2.78/1.00  ------ Abstraction refinement Options
% 2.78/1.00  
% 2.78/1.00  --abstr_ref                             []
% 2.78/1.00  --abstr_ref_prep                        false
% 2.78/1.00  --abstr_ref_until_sat                   false
% 2.78/1.00  --abstr_ref_sig_restrict                funpre
% 2.78/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/1.00  --abstr_ref_under                       []
% 2.78/1.00  
% 2.78/1.00  ------ SAT Options
% 2.78/1.00  
% 2.78/1.00  --sat_mode                              false
% 2.78/1.00  --sat_fm_restart_options                ""
% 2.78/1.00  --sat_gr_def                            false
% 2.78/1.00  --sat_epr_types                         true
% 2.78/1.00  --sat_non_cyclic_types                  false
% 2.78/1.00  --sat_finite_models                     false
% 2.78/1.00  --sat_fm_lemmas                         false
% 2.78/1.00  --sat_fm_prep                           false
% 2.78/1.00  --sat_fm_uc_incr                        true
% 2.78/1.00  --sat_out_model                         small
% 2.78/1.00  --sat_out_clauses                       false
% 2.78/1.00  
% 2.78/1.00  ------ QBF Options
% 2.78/1.00  
% 2.78/1.00  --qbf_mode                              false
% 2.78/1.00  --qbf_elim_univ                         false
% 2.78/1.00  --qbf_dom_inst                          none
% 2.78/1.00  --qbf_dom_pre_inst                      false
% 2.78/1.00  --qbf_sk_in                             false
% 2.78/1.00  --qbf_pred_elim                         true
% 2.78/1.00  --qbf_split                             512
% 2.78/1.00  
% 2.78/1.00  ------ BMC1 Options
% 2.78/1.00  
% 2.78/1.00  --bmc1_incremental                      false
% 2.78/1.00  --bmc1_axioms                           reachable_all
% 2.78/1.00  --bmc1_min_bound                        0
% 2.78/1.00  --bmc1_max_bound                        -1
% 2.78/1.00  --bmc1_max_bound_default                -1
% 2.78/1.00  --bmc1_symbol_reachability              true
% 2.78/1.00  --bmc1_property_lemmas                  false
% 2.78/1.00  --bmc1_k_induction                      false
% 2.78/1.00  --bmc1_non_equiv_states                 false
% 2.78/1.00  --bmc1_deadlock                         false
% 2.78/1.00  --bmc1_ucm                              false
% 2.78/1.00  --bmc1_add_unsat_core                   none
% 2.78/1.00  --bmc1_unsat_core_children              false
% 2.78/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/1.00  --bmc1_out_stat                         full
% 2.78/1.00  --bmc1_ground_init                      false
% 2.78/1.00  --bmc1_pre_inst_next_state              false
% 2.78/1.00  --bmc1_pre_inst_state                   false
% 2.78/1.00  --bmc1_pre_inst_reach_state             false
% 2.78/1.00  --bmc1_out_unsat_core                   false
% 2.78/1.00  --bmc1_aig_witness_out                  false
% 2.78/1.00  --bmc1_verbose                          false
% 2.78/1.00  --bmc1_dump_clauses_tptp                false
% 2.78/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.78/1.00  --bmc1_dump_file                        -
% 2.78/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.78/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.78/1.00  --bmc1_ucm_extend_mode                  1
% 2.78/1.00  --bmc1_ucm_init_mode                    2
% 2.78/1.00  --bmc1_ucm_cone_mode                    none
% 2.78/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.78/1.00  --bmc1_ucm_relax_model                  4
% 2.78/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.78/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/1.00  --bmc1_ucm_layered_model                none
% 2.78/1.00  --bmc1_ucm_max_lemma_size               10
% 2.78/1.00  
% 2.78/1.00  ------ AIG Options
% 2.78/1.00  
% 2.78/1.00  --aig_mode                              false
% 2.78/1.00  
% 2.78/1.00  ------ Instantiation Options
% 2.78/1.00  
% 2.78/1.00  --instantiation_flag                    true
% 2.78/1.00  --inst_sos_flag                         false
% 2.78/1.00  --inst_sos_phase                        true
% 2.78/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/1.00  --inst_lit_sel_side                     none
% 2.78/1.00  --inst_solver_per_active                1400
% 2.78/1.00  --inst_solver_calls_frac                1.
% 2.78/1.00  --inst_passive_queue_type               priority_queues
% 2.78/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/1.00  --inst_passive_queues_freq              [25;2]
% 2.78/1.00  --inst_dismatching                      true
% 2.78/1.00  --inst_eager_unprocessed_to_passive     true
% 2.78/1.00  --inst_prop_sim_given                   true
% 2.78/1.00  --inst_prop_sim_new                     false
% 2.78/1.00  --inst_subs_new                         false
% 2.78/1.00  --inst_eq_res_simp                      false
% 2.78/1.00  --inst_subs_given                       false
% 2.78/1.00  --inst_orphan_elimination               true
% 2.78/1.00  --inst_learning_loop_flag               true
% 2.78/1.00  --inst_learning_start                   3000
% 2.78/1.00  --inst_learning_factor                  2
% 2.78/1.00  --inst_start_prop_sim_after_learn       3
% 2.78/1.00  --inst_sel_renew                        solver
% 2.78/1.00  --inst_lit_activity_flag                true
% 2.78/1.00  --inst_restr_to_given                   false
% 2.78/1.00  --inst_activity_threshold               500
% 2.78/1.00  --inst_out_proof                        true
% 2.78/1.00  
% 2.78/1.00  ------ Resolution Options
% 2.78/1.00  
% 2.78/1.00  --resolution_flag                       false
% 2.78/1.00  --res_lit_sel                           adaptive
% 2.78/1.00  --res_lit_sel_side                      none
% 2.78/1.00  --res_ordering                          kbo
% 2.78/1.00  --res_to_prop_solver                    active
% 2.78/1.00  --res_prop_simpl_new                    false
% 2.78/1.00  --res_prop_simpl_given                  true
% 2.78/1.00  --res_passive_queue_type                priority_queues
% 2.78/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/1.00  --res_passive_queues_freq               [15;5]
% 2.78/1.00  --res_forward_subs                      full
% 2.78/1.00  --res_backward_subs                     full
% 2.78/1.00  --res_forward_subs_resolution           true
% 2.78/1.00  --res_backward_subs_resolution          true
% 2.78/1.00  --res_orphan_elimination                true
% 2.78/1.00  --res_time_limit                        2.
% 2.78/1.00  --res_out_proof                         true
% 2.78/1.00  
% 2.78/1.00  ------ Superposition Options
% 2.78/1.00  
% 2.78/1.00  --superposition_flag                    true
% 2.78/1.00  --sup_passive_queue_type                priority_queues
% 2.78/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.78/1.00  --demod_completeness_check              fast
% 2.78/1.00  --demod_use_ground                      true
% 2.78/1.00  --sup_to_prop_solver                    passive
% 2.78/1.00  --sup_prop_simpl_new                    true
% 2.78/1.00  --sup_prop_simpl_given                  true
% 2.78/1.00  --sup_fun_splitting                     false
% 2.78/1.00  --sup_smt_interval                      50000
% 2.78/1.00  
% 2.78/1.00  ------ Superposition Simplification Setup
% 2.78/1.00  
% 2.78/1.00  --sup_indices_passive                   []
% 2.78/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_full_bw                           [BwDemod]
% 2.78/1.00  --sup_immed_triv                        [TrivRules]
% 2.78/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_immed_bw_main                     []
% 2.78/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.00  
% 2.78/1.00  ------ Combination Options
% 2.78/1.00  
% 2.78/1.00  --comb_res_mult                         3
% 2.78/1.00  --comb_sup_mult                         2
% 2.78/1.00  --comb_inst_mult                        10
% 2.78/1.00  
% 2.78/1.00  ------ Debug Options
% 2.78/1.00  
% 2.78/1.00  --dbg_backtrace                         false
% 2.78/1.00  --dbg_dump_prop_clauses                 false
% 2.78/1.00  --dbg_dump_prop_clauses_file            -
% 2.78/1.00  --dbg_out_stat                          false
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  ------ Proving...
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  % SZS status Theorem for theBenchmark.p
% 2.78/1.00  
% 2.78/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.78/1.00  
% 2.78/1.00  fof(f15,conjecture,(
% 2.78/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f16,negated_conjecture,(
% 2.78/1.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.78/1.00    inference(negated_conjecture,[],[f15])).
% 2.78/1.00  
% 2.78/1.00  fof(f40,plain,(
% 2.78/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.78/1.00    inference(ennf_transformation,[],[f16])).
% 2.78/1.00  
% 2.78/1.00  fof(f41,plain,(
% 2.78/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.78/1.00    inference(flattening,[],[f40])).
% 2.78/1.00  
% 2.78/1.00  fof(f45,plain,(
% 2.78/1.00    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.78/1.00    introduced(choice_axiom,[])).
% 2.78/1.00  
% 2.78/1.00  fof(f44,plain,(
% 2.78/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.78/1.00    introduced(choice_axiom,[])).
% 2.78/1.00  
% 2.78/1.00  fof(f43,plain,(
% 2.78/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.78/1.00    introduced(choice_axiom,[])).
% 2.78/1.00  
% 2.78/1.00  fof(f46,plain,(
% 2.78/1.00    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f45,f44,f43])).
% 2.78/1.00  
% 2.78/1.00  fof(f73,plain,(
% 2.78/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.78/1.00    inference(cnf_transformation,[],[f46])).
% 2.78/1.00  
% 2.78/1.00  fof(f12,axiom,(
% 2.78/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f35,plain,(
% 2.78/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.78/1.00    inference(ennf_transformation,[],[f12])).
% 2.78/1.00  
% 2.78/1.00  fof(f65,plain,(
% 2.78/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f35])).
% 2.78/1.00  
% 2.78/1.00  fof(f68,plain,(
% 2.78/1.00    l1_struct_0(sK0)),
% 2.78/1.00    inference(cnf_transformation,[],[f46])).
% 2.78/1.00  
% 2.78/1.00  fof(f70,plain,(
% 2.78/1.00    l1_struct_0(sK1)),
% 2.78/1.00    inference(cnf_transformation,[],[f46])).
% 2.78/1.00  
% 2.78/1.00  fof(f7,axiom,(
% 2.78/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f26,plain,(
% 2.78/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/1.00    inference(ennf_transformation,[],[f7])).
% 2.78/1.00  
% 2.78/1.00  fof(f56,plain,(
% 2.78/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.78/1.00    inference(cnf_transformation,[],[f26])).
% 2.78/1.00  
% 2.78/1.00  fof(f74,plain,(
% 2.78/1.00    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.78/1.00    inference(cnf_transformation,[],[f46])).
% 2.78/1.00  
% 2.78/1.00  fof(f10,axiom,(
% 2.78/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f31,plain,(
% 2.78/1.00    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.78/1.00    inference(ennf_transformation,[],[f10])).
% 2.78/1.00  
% 2.78/1.00  fof(f32,plain,(
% 2.78/1.00    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.78/1.00    inference(flattening,[],[f31])).
% 2.78/1.00  
% 2.78/1.00  fof(f60,plain,(
% 2.78/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f32])).
% 2.78/1.00  
% 2.78/1.00  fof(f6,axiom,(
% 2.78/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f17,plain,(
% 2.78/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.78/1.00    inference(pure_predicate_removal,[],[f6])).
% 2.78/1.00  
% 2.78/1.00  fof(f25,plain,(
% 2.78/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/1.00    inference(ennf_transformation,[],[f17])).
% 2.78/1.00  
% 2.78/1.00  fof(f55,plain,(
% 2.78/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.78/1.00    inference(cnf_transformation,[],[f25])).
% 2.78/1.00  
% 2.78/1.00  fof(f8,axiom,(
% 2.78/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f27,plain,(
% 2.78/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.78/1.00    inference(ennf_transformation,[],[f8])).
% 2.78/1.00  
% 2.78/1.00  fof(f28,plain,(
% 2.78/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.78/1.00    inference(flattening,[],[f27])).
% 2.78/1.00  
% 2.78/1.00  fof(f42,plain,(
% 2.78/1.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.78/1.00    inference(nnf_transformation,[],[f28])).
% 2.78/1.00  
% 2.78/1.00  fof(f57,plain,(
% 2.78/1.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f42])).
% 2.78/1.00  
% 2.78/1.00  fof(f5,axiom,(
% 2.78/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f24,plain,(
% 2.78/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/1.00    inference(ennf_transformation,[],[f5])).
% 2.78/1.00  
% 2.78/1.00  fof(f54,plain,(
% 2.78/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.78/1.00    inference(cnf_transformation,[],[f24])).
% 2.78/1.00  
% 2.78/1.00  fof(f71,plain,(
% 2.78/1.00    v1_funct_1(sK2)),
% 2.78/1.00    inference(cnf_transformation,[],[f46])).
% 2.78/1.00  
% 2.78/1.00  fof(f72,plain,(
% 2.78/1.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.78/1.00    inference(cnf_transformation,[],[f46])).
% 2.78/1.00  
% 2.78/1.00  fof(f1,axiom,(
% 2.78/1.00    v1_xboole_0(k1_xboole_0)),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f47,plain,(
% 2.78/1.00    v1_xboole_0(k1_xboole_0)),
% 2.78/1.00    inference(cnf_transformation,[],[f1])).
% 2.78/1.00  
% 2.78/1.00  fof(f13,axiom,(
% 2.78/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f36,plain,(
% 2.78/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.78/1.00    inference(ennf_transformation,[],[f13])).
% 2.78/1.00  
% 2.78/1.00  fof(f37,plain,(
% 2.78/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.78/1.00    inference(flattening,[],[f36])).
% 2.78/1.00  
% 2.78/1.00  fof(f66,plain,(
% 2.78/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f37])).
% 2.78/1.00  
% 2.78/1.00  fof(f69,plain,(
% 2.78/1.00    ~v2_struct_0(sK1)),
% 2.78/1.00    inference(cnf_transformation,[],[f46])).
% 2.78/1.00  
% 2.78/1.00  fof(f11,axiom,(
% 2.78/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f33,plain,(
% 2.78/1.00    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.78/1.00    inference(ennf_transformation,[],[f11])).
% 2.78/1.00  
% 2.78/1.00  fof(f34,plain,(
% 2.78/1.00    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.78/1.00    inference(flattening,[],[f33])).
% 2.78/1.00  
% 2.78/1.00  fof(f64,plain,(
% 2.78/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f34])).
% 2.78/1.00  
% 2.78/1.00  fof(f75,plain,(
% 2.78/1.00    v2_funct_1(sK2)),
% 2.78/1.00    inference(cnf_transformation,[],[f46])).
% 2.78/1.00  
% 2.78/1.00  fof(f3,axiom,(
% 2.78/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f20,plain,(
% 2.78/1.00    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.78/1.00    inference(ennf_transformation,[],[f3])).
% 2.78/1.00  
% 2.78/1.00  fof(f21,plain,(
% 2.78/1.00    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.78/1.00    inference(flattening,[],[f20])).
% 2.78/1.00  
% 2.78/1.00  fof(f52,plain,(
% 2.78/1.00    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f21])).
% 2.78/1.00  
% 2.78/1.00  fof(f14,axiom,(
% 2.78/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f38,plain,(
% 2.78/1.00    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.78/1.00    inference(ennf_transformation,[],[f14])).
% 2.78/1.00  
% 2.78/1.00  fof(f39,plain,(
% 2.78/1.00    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.78/1.00    inference(flattening,[],[f38])).
% 2.78/1.00  
% 2.78/1.00  fof(f67,plain,(
% 2.78/1.00    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f39])).
% 2.78/1.00  
% 2.78/1.00  fof(f4,axiom,(
% 2.78/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f22,plain,(
% 2.78/1.00    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.78/1.00    inference(ennf_transformation,[],[f4])).
% 2.78/1.00  
% 2.78/1.00  fof(f23,plain,(
% 2.78/1.00    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.78/1.00    inference(flattening,[],[f22])).
% 2.78/1.00  
% 2.78/1.00  fof(f53,plain,(
% 2.78/1.00    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f23])).
% 2.78/1.00  
% 2.78/1.00  fof(f2,axiom,(
% 2.78/1.00    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f18,plain,(
% 2.78/1.00    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.78/1.00    inference(ennf_transformation,[],[f2])).
% 2.78/1.00  
% 2.78/1.00  fof(f19,plain,(
% 2.78/1.00    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.78/1.00    inference(flattening,[],[f18])).
% 2.78/1.00  
% 2.78/1.00  fof(f50,plain,(
% 2.78/1.00    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f19])).
% 2.78/1.00  
% 2.78/1.00  fof(f49,plain,(
% 2.78/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f19])).
% 2.78/1.00  
% 2.78/1.00  fof(f63,plain,(
% 2.78/1.00    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f34])).
% 2.78/1.00  
% 2.78/1.00  fof(f9,axiom,(
% 2.78/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f29,plain,(
% 2.78/1.00    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.78/1.00    inference(ennf_transformation,[],[f9])).
% 2.78/1.00  
% 2.78/1.00  fof(f30,plain,(
% 2.78/1.00    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.78/1.00    inference(flattening,[],[f29])).
% 2.78/1.00  
% 2.78/1.00  fof(f59,plain,(
% 2.78/1.00    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f30])).
% 2.78/1.00  
% 2.78/1.00  fof(f76,plain,(
% 2.78/1.00    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 2.78/1.00    inference(cnf_transformation,[],[f46])).
% 2.78/1.00  
% 2.78/1.00  cnf(c_24,negated_conjecture,
% 2.78/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.78/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_654,negated_conjecture,
% 2.78/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.78/1.00      inference(subtyping,[status(esa)],[c_24]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1095,plain,
% 2.78/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_654]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_18,plain,
% 2.78/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.78/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_29,negated_conjecture,
% 2.78/1.00      ( l1_struct_0(sK0) ),
% 2.78/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_367,plain,
% 2.78/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.78/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_368,plain,
% 2.78/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.78/1.00      inference(unflattening,[status(thm)],[c_367]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_648,plain,
% 2.78/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.78/1.00      inference(subtyping,[status(esa)],[c_368]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_27,negated_conjecture,
% 2.78/1.00      ( l1_struct_0(sK1) ),
% 2.78/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_362,plain,
% 2.78/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.78/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_363,plain,
% 2.78/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.78/1.00      inference(unflattening,[status(thm)],[c_362]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_649,plain,
% 2.78/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.78/1.00      inference(subtyping,[status(esa)],[c_363]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1122,plain,
% 2.78/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.78/1.00      inference(light_normalisation,[status(thm)],[c_1095,c_648,c_649]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_9,plain,
% 2.78/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.78/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_660,plain,
% 2.78/1.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.78/1.00      | k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52) ),
% 2.78/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1090,plain,
% 2.78/1.00      ( k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52)
% 2.78/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_660]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1409,plain,
% 2.78/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_1122,c_1090]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_23,negated_conjecture,
% 2.78/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.78/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_655,negated_conjecture,
% 2.78/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.78/1.00      inference(subtyping,[status(esa)],[c_23]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1119,plain,
% 2.78/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.78/1.00      inference(light_normalisation,[status(thm)],[c_655,c_648,c_649]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1549,plain,
% 2.78/1.00      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.78/1.00      inference(demodulation,[status(thm)],[c_1409,c_1119]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1592,plain,
% 2.78/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.78/1.00      inference(demodulation,[status(thm)],[c_1549,c_1122]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_14,plain,
% 2.78/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.78/1.00      | v1_partfun1(X0,X1)
% 2.78/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.00      | ~ v1_funct_1(X0)
% 2.78/1.00      | k1_xboole_0 = X2 ),
% 2.78/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_8,plain,
% 2.78/1.00      ( v4_relat_1(X0,X1)
% 2.78/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.78/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_11,plain,
% 2.78/1.00      ( ~ v1_partfun1(X0,X1)
% 2.78/1.00      | ~ v4_relat_1(X0,X1)
% 2.78/1.00      | ~ v1_relat_1(X0)
% 2.78/1.00      | k1_relat_1(X0) = X1 ),
% 2.78/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_409,plain,
% 2.78/1.00      ( ~ v1_partfun1(X0,X1)
% 2.78/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.00      | ~ v1_relat_1(X0)
% 2.78/1.00      | k1_relat_1(X0) = X1 ),
% 2.78/1.00      inference(resolution,[status(thm)],[c_8,c_11]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_7,plain,
% 2.78/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.00      | v1_relat_1(X0) ),
% 2.78/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_413,plain,
% 2.78/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.00      | ~ v1_partfun1(X0,X1)
% 2.78/1.00      | k1_relat_1(X0) = X1 ),
% 2.78/1.00      inference(global_propositional_subsumption,
% 2.78/1.00                [status(thm)],
% 2.78/1.00                [c_409,c_11,c_8,c_7]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_414,plain,
% 2.78/1.00      ( ~ v1_partfun1(X0,X1)
% 2.78/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.00      | k1_relat_1(X0) = X1 ),
% 2.78/1.00      inference(renaming,[status(thm)],[c_413]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_453,plain,
% 2.78/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.78/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.78/1.00      | ~ v1_funct_1(X0)
% 2.78/1.00      | k1_relat_1(X0) = X1
% 2.78/1.00      | k1_xboole_0 = X2 ),
% 2.78/1.00      inference(resolution,[status(thm)],[c_14,c_414]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_457,plain,
% 2.78/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.00      | ~ v1_funct_2(X0,X1,X2)
% 2.78/1.00      | ~ v1_funct_1(X0)
% 2.78/1.00      | k1_relat_1(X0) = X1
% 2.78/1.00      | k1_xboole_0 = X2 ),
% 2.78/1.00      inference(global_propositional_subsumption,
% 2.78/1.00                [status(thm)],
% 2.78/1.00                [c_453,c_14,c_7,c_409]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_458,plain,
% 2.78/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.78/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.00      | ~ v1_funct_1(X0)
% 2.78/1.00      | k1_relat_1(X0) = X1
% 2.78/1.00      | k1_xboole_0 = X2 ),
% 2.78/1.00      inference(renaming,[status(thm)],[c_457]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_646,plain,
% 2.78/1.00      ( ~ v1_funct_2(X0_52,X0_53,X1_53)
% 2.78/1.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.78/1.00      | ~ v1_funct_1(X0_52)
% 2.78/1.00      | k1_relat_1(X0_52) = X0_53
% 2.78/1.00      | k1_xboole_0 = X1_53 ),
% 2.78/1.00      inference(subtyping,[status(esa)],[c_458]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1101,plain,
% 2.78/1.00      ( k1_relat_1(X0_52) = X0_53
% 2.78/1.00      | k1_xboole_0 = X1_53
% 2.78/1.00      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.78/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.78/1.00      | v1_funct_1(X0_52) != iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_646]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3177,plain,
% 2.78/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.78/1.00      | k2_relat_1(sK2) = k1_xboole_0
% 2.78/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.78/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_1592,c_1101]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_26,negated_conjecture,
% 2.78/1.00      ( v1_funct_1(sK2) ),
% 2.78/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_33,plain,
% 2.78/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_25,negated_conjecture,
% 2.78/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.78/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_653,negated_conjecture,
% 2.78/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.78/1.00      inference(subtyping,[status(esa)],[c_25]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1096,plain,
% 2.78/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_653]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1116,plain,
% 2.78/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.78/1.00      inference(light_normalisation,[status(thm)],[c_1096,c_648,c_649]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1593,plain,
% 2.78/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.78/1.00      inference(demodulation,[status(thm)],[c_1549,c_1116]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_0,plain,
% 2.78/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.78/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_19,plain,
% 2.78/1.00      ( v2_struct_0(X0)
% 2.78/1.00      | ~ l1_struct_0(X0)
% 2.78/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.78/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_335,plain,
% 2.78/1.00      ( v2_struct_0(X0)
% 2.78/1.00      | ~ l1_struct_0(X0)
% 2.78/1.00      | u1_struct_0(X0) != k1_xboole_0 ),
% 2.78/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_19]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_28,negated_conjecture,
% 2.78/1.00      ( ~ v2_struct_0(sK1) ),
% 2.78/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_353,plain,
% 2.78/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 2.78/1.00      inference(resolution_lifted,[status(thm)],[c_335,c_28]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_354,plain,
% 2.78/1.00      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.78/1.00      inference(unflattening,[status(thm)],[c_353]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_337,plain,
% 2.78/1.00      ( v2_struct_0(sK1)
% 2.78/1.00      | ~ l1_struct_0(sK1)
% 2.78/1.00      | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_335]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_356,plain,
% 2.78/1.00      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 2.78/1.00      inference(global_propositional_subsumption,
% 2.78/1.00                [status(thm)],
% 2.78/1.00                [c_354,c_28,c_27,c_337]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_650,plain,
% 2.78/1.00      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 2.78/1.00      inference(subtyping,[status(esa)],[c_356]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1110,plain,
% 2.78/1.00      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 2.78/1.00      inference(demodulation,[status(thm)],[c_649,c_650]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1594,plain,
% 2.78/1.00      ( k2_relat_1(sK2) != k1_xboole_0 ),
% 2.78/1.00      inference(demodulation,[status(thm)],[c_1549,c_1110]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3562,plain,
% 2.78/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.78/1.00      inference(global_propositional_subsumption,
% 2.78/1.00                [status(thm)],
% 2.78/1.00                [c_3177,c_33,c_1593,c_1594]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1591,plain,
% 2.78/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.78/1.00      inference(demodulation,[status(thm)],[c_1549,c_1409]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_15,plain,
% 2.78/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.78/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.00      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.78/1.00      | ~ v1_funct_1(X0)
% 2.78/1.00      | ~ v2_funct_1(X0)
% 2.78/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.78/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_659,plain,
% 2.78/1.00      ( ~ v1_funct_2(X0_52,X0_53,X1_53)
% 2.78/1.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.78/1.00      | m1_subset_1(k2_funct_1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53)))
% 2.78/1.00      | ~ v1_funct_1(X0_52)
% 2.78/1.00      | ~ v2_funct_1(X0_52)
% 2.78/1.00      | k2_relset_1(X0_53,X1_53,X0_52) != X1_53 ),
% 2.78/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1091,plain,
% 2.78/1.00      ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
% 2.78/1.00      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.78/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.78/1.00      | m1_subset_1(k2_funct_1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) = iProver_top
% 2.78/1.00      | v1_funct_1(X0_52) != iProver_top
% 2.78/1.00      | v2_funct_1(X0_52) != iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_659]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2387,plain,
% 2.78/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.78/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 2.78/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.78/1.00      | v1_funct_1(sK2) != iProver_top
% 2.78/1.00      | v2_funct_1(sK2) != iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_1591,c_1091]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_22,negated_conjecture,
% 2.78/1.00      ( v2_funct_1(sK2) ),
% 2.78/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_36,plain,
% 2.78/1.00      ( v2_funct_1(sK2) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2658,plain,
% 2.78/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 2.78/1.00      inference(global_propositional_subsumption,
% 2.78/1.00                [status(thm)],
% 2.78/1.00                [c_2387,c_33,c_36,c_1592,c_1593]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2663,plain,
% 2.78/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_2658,c_1090]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_661,plain,
% 2.78/1.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.78/1.00      | v1_relat_1(X0_52) ),
% 2.78/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1089,plain,
% 2.78/1.00      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.78/1.00      | v1_relat_1(X0_52) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_661]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1392,plain,
% 2.78/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_1122,c_1089]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_4,plain,
% 2.78/1.00      ( ~ v1_relat_1(X0)
% 2.78/1.00      | ~ v1_funct_1(X0)
% 2.78/1.00      | ~ v2_funct_1(X0)
% 2.78/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.78/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_664,plain,
% 2.78/1.00      ( ~ v1_relat_1(X0_52)
% 2.78/1.00      | ~ v1_funct_1(X0_52)
% 2.78/1.00      | ~ v2_funct_1(X0_52)
% 2.78/1.00      | k2_relat_1(k2_funct_1(X0_52)) = k1_relat_1(X0_52) ),
% 2.78/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1086,plain,
% 2.78/1.00      ( k2_relat_1(k2_funct_1(X0_52)) = k1_relat_1(X0_52)
% 2.78/1.00      | v1_relat_1(X0_52) != iProver_top
% 2.78/1.00      | v1_funct_1(X0_52) != iProver_top
% 2.78/1.00      | v2_funct_1(X0_52) != iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_664]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1756,plain,
% 2.78/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.78/1.00      | v1_funct_1(sK2) != iProver_top
% 2.78/1.00      | v2_funct_1(sK2) != iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_1392,c_1086]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_716,plain,
% 2.78/1.00      ( ~ v1_relat_1(sK2)
% 2.78/1.00      | ~ v1_funct_1(sK2)
% 2.78/1.00      | ~ v2_funct_1(sK2)
% 2.78/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_664]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1313,plain,
% 2.78/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.78/1.00      | v1_relat_1(sK2) ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_661]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2156,plain,
% 2.78/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.78/1.00      inference(global_propositional_subsumption,
% 2.78/1.00                [status(thm)],
% 2.78/1.00                [c_1756,c_26,c_24,c_22,c_716,c_1313]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2668,plain,
% 2.78/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.78/1.00      inference(light_normalisation,[status(thm)],[c_2663,c_2156]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_20,plain,
% 2.78/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.78/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.00      | ~ v1_funct_1(X0)
% 2.78/1.00      | ~ v2_funct_1(X0)
% 2.78/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.78/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.78/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_657,plain,
% 2.78/1.00      ( ~ v1_funct_2(X0_52,X0_53,X1_53)
% 2.78/1.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.78/1.00      | ~ v1_funct_1(X0_52)
% 2.78/1.00      | ~ v2_funct_1(X0_52)
% 2.78/1.00      | k2_relset_1(X0_53,X1_53,X0_52) != X1_53
% 2.78/1.00      | k2_tops_2(X0_53,X1_53,X0_52) = k2_funct_1(X0_52) ),
% 2.78/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1093,plain,
% 2.78/1.00      ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
% 2.78/1.00      | k2_tops_2(X0_53,X1_53,X0_52) = k2_funct_1(X0_52)
% 2.78/1.00      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.78/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.78/1.00      | v1_funct_1(X0_52) != iProver_top
% 2.78/1.00      | v2_funct_1(X0_52) != iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_657]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2756,plain,
% 2.78/1.00      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 2.78/1.00      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.78/1.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 2.78/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 2.78/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.78/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_2668,c_1093]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_6,plain,
% 2.78/1.00      ( ~ v1_relat_1(X0)
% 2.78/1.00      | ~ v1_funct_1(X0)
% 2.78/1.00      | ~ v2_funct_1(X0)
% 2.78/1.00      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.78/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_662,plain,
% 2.78/1.00      ( ~ v1_relat_1(X0_52)
% 2.78/1.00      | ~ v1_funct_1(X0_52)
% 2.78/1.00      | ~ v2_funct_1(X0_52)
% 2.78/1.00      | k2_funct_1(k2_funct_1(X0_52)) = X0_52 ),
% 2.78/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1088,plain,
% 2.78/1.00      ( k2_funct_1(k2_funct_1(X0_52)) = X0_52
% 2.78/1.00      | v1_relat_1(X0_52) != iProver_top
% 2.78/1.00      | v1_funct_1(X0_52) != iProver_top
% 2.78/1.00      | v2_funct_1(X0_52) != iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_662]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1872,plain,
% 2.78/1.00      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.78/1.00      | v1_funct_1(sK2) != iProver_top
% 2.78/1.00      | v2_funct_1(sK2) != iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_1392,c_1088]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_722,plain,
% 2.78/1.00      ( ~ v1_relat_1(sK2)
% 2.78/1.00      | ~ v1_funct_1(sK2)
% 2.78/1.00      | ~ v2_funct_1(sK2)
% 2.78/1.00      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_662]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2149,plain,
% 2.78/1.00      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.78/1.00      inference(global_propositional_subsumption,
% 2.78/1.00                [status(thm)],
% 2.78/1.00                [c_1872,c_26,c_24,c_22,c_722,c_1313]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2771,plain,
% 2.78/1.00      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 2.78/1.00      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 2.78/1.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 2.78/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 2.78/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.78/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.78/1.00      inference(light_normalisation,[status(thm)],[c_2756,c_2149]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_35,plain,
% 2.78/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1,plain,
% 2.78/1.00      ( ~ v1_relat_1(X0)
% 2.78/1.00      | ~ v1_funct_1(X0)
% 2.78/1.00      | ~ v2_funct_1(X0)
% 2.78/1.00      | v2_funct_1(k2_funct_1(X0)) ),
% 2.78/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_667,plain,
% 2.78/1.00      ( ~ v1_relat_1(X0_52)
% 2.78/1.00      | ~ v1_funct_1(X0_52)
% 2.78/1.00      | ~ v2_funct_1(X0_52)
% 2.78/1.00      | v2_funct_1(k2_funct_1(X0_52)) ),
% 2.78/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_706,plain,
% 2.78/1.00      ( v1_relat_1(X0_52) != iProver_top
% 2.78/1.00      | v1_funct_1(X0_52) != iProver_top
% 2.78/1.00      | v2_funct_1(X0_52) != iProver_top
% 2.78/1.00      | v2_funct_1(k2_funct_1(X0_52)) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_667]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_708,plain,
% 2.78/1.00      ( v1_relat_1(sK2) != iProver_top
% 2.78/1.00      | v1_funct_1(sK2) != iProver_top
% 2.78/1.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.78/1.00      | v2_funct_1(sK2) != iProver_top ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_706]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2,plain,
% 2.78/1.00      ( ~ v1_relat_1(X0)
% 2.78/1.00      | ~ v1_funct_1(X0)
% 2.78/1.00      | v1_funct_1(k2_funct_1(X0))
% 2.78/1.00      | ~ v2_funct_1(X0) ),
% 2.78/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_666,plain,
% 2.78/1.00      ( ~ v1_relat_1(X0_52)
% 2.78/1.00      | ~ v1_funct_1(X0_52)
% 2.78/1.00      | v1_funct_1(k2_funct_1(X0_52))
% 2.78/1.00      | ~ v2_funct_1(X0_52) ),
% 2.78/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_709,plain,
% 2.78/1.00      ( v1_relat_1(X0_52) != iProver_top
% 2.78/1.00      | v1_funct_1(X0_52) != iProver_top
% 2.78/1.00      | v1_funct_1(k2_funct_1(X0_52)) = iProver_top
% 2.78/1.00      | v2_funct_1(X0_52) != iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_666]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_711,plain,
% 2.78/1.00      ( v1_relat_1(sK2) != iProver_top
% 2.78/1.00      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.78/1.00      | v1_funct_1(sK2) != iProver_top
% 2.78/1.00      | v2_funct_1(sK2) != iProver_top ),
% 2.78/1.00      inference(instantiation,[status(thm)],[c_709]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1314,plain,
% 2.78/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.78/1.00      | v1_relat_1(sK2) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_1313]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_16,plain,
% 2.78/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.78/1.00      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.78/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.00      | ~ v1_funct_1(X0)
% 2.78/1.00      | ~ v2_funct_1(X0)
% 2.78/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.78/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_658,plain,
% 2.78/1.00      ( ~ v1_funct_2(X0_52,X0_53,X1_53)
% 2.78/1.00      | v1_funct_2(k2_funct_1(X0_52),X1_53,X0_53)
% 2.78/1.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.78/1.00      | ~ v1_funct_1(X0_52)
% 2.78/1.00      | ~ v2_funct_1(X0_52)
% 2.78/1.00      | k2_relset_1(X0_53,X1_53,X0_52) != X1_53 ),
% 2.78/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1092,plain,
% 2.78/1.00      ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
% 2.78/1.00      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.78/1.00      | v1_funct_2(k2_funct_1(X0_52),X1_53,X0_53) = iProver_top
% 2.78/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.78/1.00      | v1_funct_1(X0_52) != iProver_top
% 2.78/1.00      | v2_funct_1(X0_52) != iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_658]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2019,plain,
% 2.78/1.00      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
% 2.78/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.78/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.78/1.00      | v1_funct_1(sK2) != iProver_top
% 2.78/1.00      | v2_funct_1(sK2) != iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_1591,c_1092]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2922,plain,
% 2.78/1.00      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 2.78/1.00      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
% 2.78/1.00      inference(global_propositional_subsumption,
% 2.78/1.00                [status(thm)],
% 2.78/1.00                [c_2771,c_33,c_35,c_36,c_708,c_711,c_1314,c_1592,c_1593,
% 2.78/1.00                 c_2019,c_2387]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3565,plain,
% 2.78/1.00      ( k1_relat_1(sK2) != k1_relat_1(sK2)
% 2.78/1.00      | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 2.78/1.00      inference(demodulation,[status(thm)],[c_3562,c_2922]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3599,plain,
% 2.78/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 2.78/1.00      inference(equality_resolution_simp,[status(thm)],[c_3565]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2028,plain,
% 2.78/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 2.78/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.78/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.78/1.00      | v1_funct_1(sK2) != iProver_top
% 2.78/1.00      | v2_funct_1(sK2) != iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_1591,c_1093]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2326,plain,
% 2.78/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.78/1.00      inference(global_propositional_subsumption,
% 2.78/1.00                [status(thm)],
% 2.78/1.00                [c_2028,c_33,c_36,c_1592,c_1593]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_12,plain,
% 2.78/1.00      ( r2_funct_2(X0,X1,X2,X2)
% 2.78/1.00      | ~ v1_funct_2(X3,X0,X1)
% 2.78/1.00      | ~ v1_funct_2(X2,X0,X1)
% 2.78/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.78/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.78/1.00      | ~ v1_funct_1(X3)
% 2.78/1.00      | ~ v1_funct_1(X2) ),
% 2.78/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_21,negated_conjecture,
% 2.78/1.00      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 2.78/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_374,plain,
% 2.78/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.78/1.00      | ~ v1_funct_2(X3,X1,X2)
% 2.78/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.00      | ~ v1_funct_1(X0)
% 2.78/1.00      | ~ v1_funct_1(X3)
% 2.78/1.00      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X3
% 2.78/1.00      | u1_struct_0(sK1) != X2
% 2.78/1.00      | u1_struct_0(sK0) != X1
% 2.78/1.00      | sK2 != X3 ),
% 2.78/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_375,plain,
% 2.78/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.78/1.00      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.78/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.78/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.78/1.00      | ~ v1_funct_1(X0)
% 2.78/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.78/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.78/1.00      inference(unflattening,[status(thm)],[c_374]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_647,plain,
% 2.78/1.00      ( ~ v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.78/1.00      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.78/1.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.78/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.78/1.00      | ~ v1_funct_1(X0_52)
% 2.78/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.78/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.78/1.00      inference(subtyping,[status(esa)],[c_375]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_669,plain,
% 2.78/1.00      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.78/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.78/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.78/1.00      | sP0_iProver_split
% 2.78/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.78/1.00      inference(splitting,
% 2.78/1.00                [splitting(split),new_symbols(definition,[])],
% 2.78/1.00                [c_647]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1099,plain,
% 2.78/1.00      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.78/1.00      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.78/1.00      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.78/1.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
% 2.78/1.00      | sP0_iProver_split = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_669]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1254,plain,
% 2.78/1.00      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.78/1.00      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.78/1.00      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.78/1.00      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
% 2.78/1.00      | sP0_iProver_split = iProver_top ),
% 2.78/1.00      inference(light_normalisation,[status(thm)],[c_1099,c_648,c_649]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_668,plain,
% 2.78/1.00      ( ~ v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.78/1.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.78/1.00      | ~ v1_funct_1(X0_52)
% 2.78/1.00      | ~ sP0_iProver_split ),
% 2.78/1.00      inference(splitting,
% 2.78/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.78/1.00                [c_647]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1100,plain,
% 2.78/1.00      ( v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.78/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.78/1.00      | v1_funct_1(X0_52) != iProver_top
% 2.78/1.00      | sP0_iProver_split != iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_668]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1189,plain,
% 2.78/1.00      ( v1_funct_2(X0_52,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.78/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.78/1.00      | v1_funct_1(X0_52) != iProver_top
% 2.78/1.00      | sP0_iProver_split != iProver_top ),
% 2.78/1.00      inference(light_normalisation,[status(thm)],[c_1100,c_648,c_649]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1260,plain,
% 2.78/1.00      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.78/1.00      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.78/1.00      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.78/1.00      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.78/1.00      inference(forward_subsumption_resolution,
% 2.78/1.00                [status(thm)],
% 2.78/1.00                [c_1254,c_1189]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2111,plain,
% 2.78/1.00      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
% 2.78/1.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.78/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.78/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
% 2.78/1.00      inference(light_normalisation,[status(thm)],[c_1260,c_1549]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2329,plain,
% 2.78/1.00      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 2.78/1.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.78/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.78/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 2.78/1.00      inference(demodulation,[status(thm)],[c_2326,c_2111]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3568,plain,
% 2.78/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 2.78/1.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.78/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.78/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 2.78/1.00      inference(demodulation,[status(thm)],[c_3562,c_2329]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3601,plain,
% 2.78/1.00      ( sK2 != sK2
% 2.78/1.00      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.78/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.78/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.78/1.00      inference(demodulation,[status(thm)],[c_3599,c_3568]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3603,plain,
% 2.78/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.78/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.78/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.78/1.00      inference(equality_resolution_simp,[status(thm)],[c_3601]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3571,plain,
% 2.78/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 2.78/1.00      inference(demodulation,[status(thm)],[c_3562,c_1592]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3573,plain,
% 2.78/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 2.78/1.00      inference(demodulation,[status(thm)],[c_3562,c_1593]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_3607,plain,
% 2.78/1.00      ( v1_funct_1(sK2) != iProver_top ),
% 2.78/1.00      inference(forward_subsumption_resolution,
% 2.78/1.00                [status(thm)],
% 2.78/1.00                [c_3603,c_3571,c_3573]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(contradiction,plain,
% 2.78/1.00      ( $false ),
% 2.78/1.00      inference(minisat,[status(thm)],[c_3607,c_33]) ).
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.78/1.00  
% 2.78/1.00  ------                               Statistics
% 2.78/1.00  
% 2.78/1.00  ------ General
% 2.78/1.00  
% 2.78/1.00  abstr_ref_over_cycles:                  0
% 2.78/1.00  abstr_ref_under_cycles:                 0
% 2.78/1.00  gc_basic_clause_elim:                   0
% 2.78/1.00  forced_gc_time:                         0
% 2.78/1.00  parsing_time:                           0.021
% 2.78/1.00  unif_index_cands_time:                  0.
% 2.78/1.00  unif_index_add_time:                    0.
% 2.78/1.00  orderings_time:                         0.
% 2.78/1.00  out_proof_time:                         0.015
% 2.78/1.00  total_time:                             0.209
% 2.78/1.00  num_of_symbols:                         58
% 2.78/1.00  num_of_terms:                           3082
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing
% 2.78/1.00  
% 2.78/1.00  num_of_splits:                          1
% 2.78/1.00  num_of_split_atoms:                     1
% 2.78/1.00  num_of_reused_defs:                     0
% 2.78/1.00  num_eq_ax_congr_red:                    4
% 2.78/1.00  num_of_sem_filtered_clauses:            2
% 2.78/1.00  num_of_subtypes:                        5
% 2.78/1.00  monotx_restored_types:                  1
% 2.78/1.00  sat_num_of_epr_types:                   0
% 2.78/1.00  sat_num_of_non_cyclic_types:            0
% 2.78/1.00  sat_guarded_non_collapsed_types:        1
% 2.78/1.00  num_pure_diseq_elim:                    0
% 2.78/1.00  simp_replaced_by:                       0
% 2.78/1.00  res_preprocessed:                       137
% 2.78/1.00  prep_upred:                             0
% 2.78/1.00  prep_unflattend:                        12
% 2.78/1.00  smt_new_axioms:                         0
% 2.78/1.00  pred_elim_cands:                        5
% 2.78/1.00  pred_elim:                              6
% 2.78/1.00  pred_elim_cl:                           7
% 2.78/1.00  pred_elim_cycles:                       8
% 2.78/1.00  merged_defs:                            0
% 2.78/1.00  merged_defs_ncl:                        0
% 2.78/1.00  bin_hyper_res:                          0
% 2.78/1.00  prep_cycles:                            4
% 2.78/1.00  pred_elim_time:                         0.008
% 2.78/1.00  splitting_time:                         0.
% 2.78/1.00  sem_filter_time:                        0.
% 2.78/1.00  monotx_time:                            0.001
% 2.78/1.00  subtype_inf_time:                       0.002
% 2.78/1.00  
% 2.78/1.00  ------ Problem properties
% 2.78/1.00  
% 2.78/1.00  clauses:                                24
% 2.78/1.00  conjectures:                            5
% 2.78/1.00  epr:                                    2
% 2.78/1.00  horn:                                   23
% 2.78/1.00  ground:                                 9
% 2.78/1.00  unary:                                  8
% 2.78/1.00  binary:                                 2
% 2.78/1.00  lits:                                   77
% 2.78/1.00  lits_eq:                                16
% 2.78/1.00  fd_pure:                                0
% 2.78/1.00  fd_pseudo:                              0
% 2.78/1.00  fd_cond:                                0
% 2.78/1.00  fd_pseudo_cond:                         1
% 2.78/1.00  ac_symbols:                             0
% 2.78/1.00  
% 2.78/1.00  ------ Propositional Solver
% 2.78/1.00  
% 2.78/1.00  prop_solver_calls:                      28
% 2.78/1.00  prop_fast_solver_calls:                 1098
% 2.78/1.00  smt_solver_calls:                       0
% 2.78/1.00  smt_fast_solver_calls:                  0
% 2.78/1.00  prop_num_of_clauses:                    1233
% 2.78/1.00  prop_preprocess_simplified:             4650
% 2.78/1.00  prop_fo_subsumed:                       57
% 2.78/1.00  prop_solver_time:                       0.
% 2.78/1.00  smt_solver_time:                        0.
% 2.78/1.00  smt_fast_solver_time:                   0.
% 2.78/1.00  prop_fast_solver_time:                  0.
% 2.78/1.00  prop_unsat_core_time:                   0.
% 2.78/1.00  
% 2.78/1.00  ------ QBF
% 2.78/1.00  
% 2.78/1.00  qbf_q_res:                              0
% 2.78/1.00  qbf_num_tautologies:                    0
% 2.78/1.00  qbf_prep_cycles:                        0
% 2.78/1.00  
% 2.78/1.00  ------ BMC1
% 2.78/1.00  
% 2.78/1.00  bmc1_current_bound:                     -1
% 2.78/1.00  bmc1_last_solved_bound:                 -1
% 2.78/1.00  bmc1_unsat_core_size:                   -1
% 2.78/1.00  bmc1_unsat_core_parents_size:           -1
% 2.78/1.00  bmc1_merge_next_fun:                    0
% 2.78/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.78/1.00  
% 2.78/1.00  ------ Instantiation
% 2.78/1.00  
% 2.78/1.00  inst_num_of_clauses:                    411
% 2.78/1.00  inst_num_in_passive:                    123
% 2.78/1.00  inst_num_in_active:                     224
% 2.78/1.00  inst_num_in_unprocessed:                64
% 2.78/1.00  inst_num_of_loops:                      270
% 2.78/1.00  inst_num_of_learning_restarts:          0
% 2.78/1.00  inst_num_moves_active_passive:          42
% 2.78/1.00  inst_lit_activity:                      0
% 2.78/1.00  inst_lit_activity_moves:                0
% 2.78/1.00  inst_num_tautologies:                   0
% 2.78/1.00  inst_num_prop_implied:                  0
% 2.78/1.00  inst_num_existing_simplified:           0
% 2.78/1.00  inst_num_eq_res_simplified:             0
% 2.78/1.00  inst_num_child_elim:                    0
% 2.78/1.00  inst_num_of_dismatching_blockings:      74
% 2.78/1.00  inst_num_of_non_proper_insts:           358
% 2.78/1.00  inst_num_of_duplicates:                 0
% 2.78/1.00  inst_inst_num_from_inst_to_res:         0
% 2.78/1.00  inst_dismatching_checking_time:         0.
% 2.78/1.00  
% 2.78/1.00  ------ Resolution
% 2.78/1.00  
% 2.78/1.00  res_num_of_clauses:                     0
% 2.78/1.00  res_num_in_passive:                     0
% 2.78/1.00  res_num_in_active:                      0
% 2.78/1.00  res_num_of_loops:                       141
% 2.78/1.00  res_forward_subset_subsumed:            58
% 2.78/1.00  res_backward_subset_subsumed:           0
% 2.78/1.00  res_forward_subsumed:                   0
% 2.78/1.00  res_backward_subsumed:                  0
% 2.78/1.00  res_forward_subsumption_resolution:     1
% 2.78/1.00  res_backward_subsumption_resolution:    0
% 2.78/1.00  res_clause_to_clause_subsumption:       212
% 2.78/1.00  res_orphan_elimination:                 0
% 2.78/1.00  res_tautology_del:                      31
% 2.78/1.00  res_num_eq_res_simplified:              0
% 2.78/1.00  res_num_sel_changes:                    0
% 2.78/1.00  res_moves_from_active_to_pass:          0
% 2.78/1.00  
% 2.78/1.00  ------ Superposition
% 2.78/1.00  
% 2.78/1.00  sup_time_total:                         0.
% 2.78/1.00  sup_time_generating:                    0.
% 2.78/1.00  sup_time_sim_full:                      0.
% 2.78/1.00  sup_time_sim_immed:                     0.
% 2.78/1.00  
% 2.78/1.00  sup_num_of_clauses:                     49
% 2.78/1.00  sup_num_in_active:                      35
% 2.78/1.00  sup_num_in_passive:                     14
% 2.78/1.00  sup_num_of_loops:                       52
% 2.78/1.00  sup_fw_superposition:                   38
% 2.78/1.00  sup_bw_superposition:                   17
% 2.78/1.00  sup_immediate_simplified:               32
% 2.78/1.00  sup_given_eliminated:                   0
% 2.78/1.00  comparisons_done:                       0
% 2.78/1.00  comparisons_avoided:                    0
% 2.78/1.00  
% 2.78/1.00  ------ Simplifications
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  sim_fw_subset_subsumed:                 4
% 2.78/1.00  sim_bw_subset_subsumed:                 0
% 2.78/1.00  sim_fw_subsumed:                        3
% 2.78/1.00  sim_bw_subsumed:                        0
% 2.78/1.00  sim_fw_subsumption_res:                 3
% 2.78/1.00  sim_bw_subsumption_res:                 0
% 2.78/1.00  sim_tautology_del:                      0
% 2.78/1.00  sim_eq_tautology_del:                   21
% 2.78/1.00  sim_eq_res_simp:                        2
% 2.78/1.00  sim_fw_demodulated:                     0
% 2.78/1.00  sim_bw_demodulated:                     19
% 2.78/1.00  sim_light_normalised:                   32
% 2.78/1.00  sim_joinable_taut:                      0
% 2.78/1.00  sim_joinable_simp:                      0
% 2.78/1.00  sim_ac_normalised:                      0
% 2.78/1.00  sim_smt_subsumption:                    0
% 2.78/1.00  
%------------------------------------------------------------------------------
