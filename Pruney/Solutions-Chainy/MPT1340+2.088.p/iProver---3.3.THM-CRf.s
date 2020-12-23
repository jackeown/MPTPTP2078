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
% DateTime   : Thu Dec  3 12:17:40 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :  200 (4374 expanded)
%              Number of clauses        :  125 (1416 expanded)
%              Number of leaves         :   19 (1218 expanded)
%              Depth                    :   26
%              Number of atoms          :  722 (26936 expanded)
%              Number of equality atoms :  277 (4870 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

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
    inference(ennf_transformation,[],[f17])).

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
    inference(flattening,[],[f41])).

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,
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

fof(f48,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f47,f46,f45])).

fof(f77,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f72,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f74,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f78,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

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

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f79,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

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
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f30])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f63])).

fof(f80,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f48])).

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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f34])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

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
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f57,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_665,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1102,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_665])).

cnf(c_20,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_31,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_380,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_31])).

cnf(c_381,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_660,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_381])).

cnf(c_29,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_375,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_376,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_661,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_376])).

cnf(c_1126,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1102,c_660,c_661])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_672,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1096,plain,
    ( k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_672])).

cnf(c_1474,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1126,c_1096])).

cnf(c_25,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_666,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1123,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_666,c_660,c_661])).

cnf(c_1585,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1474,c_1123])).

cnf(c_1589,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1585,c_1126])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_12,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_449,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_16,c_12])).

cnf(c_9,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_453,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_449,c_9])).

cnf(c_658,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X1_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v1_relat_1(X0_52)
    | k1_relat_1(X0_52) = X0_53
    | k1_xboole_0 = X1_53 ),
    inference(subtyping,[status(esa)],[c_453])).

cnf(c_1106,plain,
    ( k1_relat_1(X0_52) = X0_53
    | k1_xboole_0 = X1_53
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_658])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_679,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_716,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_679])).

cnf(c_757,plain,
    ( k1_relat_1(X0_52) = X0_53
    | k1_xboole_0 = X1_53
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_658])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_680,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
    | ~ v1_relat_1(X1_52)
    | v1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1330,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | v1_relat_1(X0_52)
    | ~ v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
    inference(instantiation,[status(thm)],[c_680])).

cnf(c_1331,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_relat_1(X0_52) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1330])).

cnf(c_2945,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | k1_xboole_0 = X1_53
    | k1_relat_1(X0_52) = X0_53 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1106,c_716,c_757,c_1331])).

cnf(c_2946,plain,
    ( k1_relat_1(X0_52) = X0_53
    | k1_xboole_0 = X1_53
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_2945])).

cnf(c_2954,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1589,c_2946])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_35,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_664,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1103,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_1120,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1103,c_660,c_661])).

cnf(c_1590,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1585,c_1120])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_21,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_348,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_21])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_366,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_348,c_30])).

cnf(c_367,plain,
    ( ~ l1_struct_0(sK1)
    | k2_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_350,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | k2_struct_0(sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_348])).

cnf(c_369,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_367,c_30,c_29,c_350])).

cnf(c_662,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_369])).

cnf(c_1591,plain,
    ( k2_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1585,c_662])).

cnf(c_3296,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2954,c_35,c_1590,c_1591])).

cnf(c_1587,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1585,c_1474])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_668,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X1_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | k2_relset_1(X0_53,X1_53,X0_52) != X1_53
    | k2_tops_2(X0_53,X1_53,X0_52) = k2_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1100,plain,
    ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
    | k2_tops_2(X0_53,X1_53,X0_52) = k2_funct_1(X0_52)
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_668])).

cnf(c_2411,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1587,c_1100])).

cnf(c_24,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_38,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2577,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2411,c_35,c_38,c_1589,c_1590])).

cnf(c_13,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_23,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_428,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_429,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_659,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_429])).

cnf(c_1105,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_659])).

cnf(c_1257,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1105,c_660,c_661])).

cnf(c_1588,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1585,c_1257])).

cnf(c_2580,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2577,c_1588])).

cnf(c_3299,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3296,c_2580])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_671,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X1_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | m1_subset_1(k2_funct_1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | k2_relset_1(X0_53,X1_53,X0_52) != X1_53 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1097,plain,
    ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_671])).

cnf(c_2346,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1587,c_1097])).

cnf(c_2583,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2346,c_35,c_38,c_1589,c_1590])).

cnf(c_2589,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2583,c_1096])).

cnf(c_663,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1104,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_663])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_675,plain,
    ( ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | ~ v1_relat_1(X0_52)
    | k2_relat_1(k2_funct_1(X0_52)) = k1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1093,plain,
    ( k2_relat_1(k2_funct_1(X0_52)) = k1_relat_1(X0_52)
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_675])).

cnf(c_1820,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1104,c_1093])).

cnf(c_729,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_675])).

cnf(c_1451,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1330])).

cnf(c_1480,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_679])).

cnf(c_2069,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1820,c_28,c_26,c_24,c_729,c_1451,c_1480])).

cnf(c_2596,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2589,c_2069])).

cnf(c_2667,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2596,c_1100])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_673,plain,
    ( ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | ~ v1_relat_1(X0_52)
    | k2_funct_1(k2_funct_1(X0_52)) = X0_52 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1095,plain,
    ( k2_funct_1(k2_funct_1(X0_52)) = X0_52
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_673])).

cnf(c_1791,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1104,c_1095])).

cnf(c_735,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_673])).

cnf(c_2053,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1791,c_28,c_26,c_24,c_735,c_1451,c_1480])).

cnf(c_2690,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2667,c_2053])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_678,plain,
    ( ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | v2_funct_1(k2_funct_1(X0_52))
    | ~ v1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_719,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top
    | v2_funct_1(k2_funct_1(X0_52)) = iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_678])).

cnf(c_721,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_677,plain,
    ( ~ v1_funct_1(X0_52)
    | v1_funct_1(k2_funct_1(X0_52))
    | ~ v2_funct_1(X0_52)
    | ~ v1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_722,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k2_funct_1(X0_52)) = iProver_top
    | v2_funct_1(X0_52) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_677])).

cnf(c_724,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_722])).

cnf(c_1452,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1451])).

cnf(c_1481,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1480])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_670,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X1_53)
    | v1_funct_2(k2_funct_1(X0_52),X1_53,X0_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | k2_relset_1(X0_53,X1_53,X0_52) != X1_53 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1098,plain,
    ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | v1_funct_2(k2_funct_1(X0_52),X1_53,X0_53) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_670])).

cnf(c_2355,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1587,c_1098])).

cnf(c_2699,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2690,c_35,c_37,c_38,c_721,c_724,c_1452,c_1481,c_1589,c_1590,c_2346,c_2355])).

cnf(c_3300,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_3296,c_2699])).

cnf(c_3325,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_3300])).

cnf(c_3328,plain,
    ( sK2 != sK2
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3299,c_3325])).

cnf(c_3329,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3328])).

cnf(c_3305,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3296,c_1589])).

cnf(c_3307,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3296,c_1590])).

cnf(c_3333,plain,
    ( v1_funct_1(sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3329,c_3305,c_3307])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3333,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:47:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.63/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.00  
% 2.63/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.63/1.00  
% 2.63/1.00  ------  iProver source info
% 2.63/1.00  
% 2.63/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.63/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.63/1.00  git: non_committed_changes: false
% 2.63/1.00  git: last_make_outside_of_git: false
% 2.63/1.00  
% 2.63/1.00  ------ 
% 2.63/1.00  
% 2.63/1.00  ------ Input Options
% 2.63/1.00  
% 2.63/1.00  --out_options                           all
% 2.63/1.00  --tptp_safe_out                         true
% 2.63/1.00  --problem_path                          ""
% 2.63/1.00  --include_path                          ""
% 2.63/1.00  --clausifier                            res/vclausify_rel
% 2.63/1.00  --clausifier_options                    --mode clausify
% 2.63/1.00  --stdin                                 false
% 2.63/1.00  --stats_out                             all
% 2.63/1.00  
% 2.63/1.00  ------ General Options
% 2.63/1.00  
% 2.63/1.00  --fof                                   false
% 2.63/1.00  --time_out_real                         305.
% 2.63/1.00  --time_out_virtual                      -1.
% 2.63/1.00  --symbol_type_check                     false
% 2.63/1.00  --clausify_out                          false
% 2.63/1.00  --sig_cnt_out                           false
% 2.63/1.00  --trig_cnt_out                          false
% 2.63/1.00  --trig_cnt_out_tolerance                1.
% 2.63/1.00  --trig_cnt_out_sk_spl                   false
% 2.63/1.00  --abstr_cl_out                          false
% 2.63/1.00  
% 2.63/1.00  ------ Global Options
% 2.63/1.00  
% 2.63/1.00  --schedule                              default
% 2.63/1.00  --add_important_lit                     false
% 2.63/1.00  --prop_solver_per_cl                    1000
% 2.63/1.00  --min_unsat_core                        false
% 2.63/1.00  --soft_assumptions                      false
% 2.63/1.00  --soft_lemma_size                       3
% 2.63/1.00  --prop_impl_unit_size                   0
% 2.63/1.00  --prop_impl_unit                        []
% 2.63/1.00  --share_sel_clauses                     true
% 2.63/1.00  --reset_solvers                         false
% 2.63/1.00  --bc_imp_inh                            [conj_cone]
% 2.63/1.00  --conj_cone_tolerance                   3.
% 2.63/1.00  --extra_neg_conj                        none
% 2.63/1.00  --large_theory_mode                     true
% 2.63/1.00  --prolific_symb_bound                   200
% 2.63/1.00  --lt_threshold                          2000
% 2.63/1.00  --clause_weak_htbl                      true
% 2.63/1.00  --gc_record_bc_elim                     false
% 2.63/1.00  
% 2.63/1.00  ------ Preprocessing Options
% 2.63/1.00  
% 2.63/1.00  --preprocessing_flag                    true
% 2.63/1.00  --time_out_prep_mult                    0.1
% 2.63/1.00  --splitting_mode                        input
% 2.63/1.00  --splitting_grd                         true
% 2.63/1.00  --splitting_cvd                         false
% 2.63/1.00  --splitting_cvd_svl                     false
% 2.63/1.00  --splitting_nvd                         32
% 2.63/1.00  --sub_typing                            true
% 2.63/1.00  --prep_gs_sim                           true
% 2.63/1.00  --prep_unflatten                        true
% 2.63/1.00  --prep_res_sim                          true
% 2.63/1.00  --prep_upred                            true
% 2.63/1.00  --prep_sem_filter                       exhaustive
% 2.63/1.00  --prep_sem_filter_out                   false
% 2.63/1.00  --pred_elim                             true
% 2.63/1.00  --res_sim_input                         true
% 2.63/1.00  --eq_ax_congr_red                       true
% 2.63/1.00  --pure_diseq_elim                       true
% 2.63/1.00  --brand_transform                       false
% 2.63/1.00  --non_eq_to_eq                          false
% 2.63/1.00  --prep_def_merge                        true
% 2.63/1.00  --prep_def_merge_prop_impl              false
% 2.63/1.00  --prep_def_merge_mbd                    true
% 2.63/1.00  --prep_def_merge_tr_red                 false
% 2.63/1.00  --prep_def_merge_tr_cl                  false
% 2.63/1.00  --smt_preprocessing                     true
% 2.63/1.00  --smt_ac_axioms                         fast
% 2.63/1.00  --preprocessed_out                      false
% 2.63/1.00  --preprocessed_stats                    false
% 2.63/1.00  
% 2.63/1.00  ------ Abstraction refinement Options
% 2.63/1.00  
% 2.63/1.00  --abstr_ref                             []
% 2.63/1.00  --abstr_ref_prep                        false
% 2.63/1.00  --abstr_ref_until_sat                   false
% 2.63/1.00  --abstr_ref_sig_restrict                funpre
% 2.63/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.63/1.00  --abstr_ref_under                       []
% 2.63/1.00  
% 2.63/1.00  ------ SAT Options
% 2.63/1.00  
% 2.63/1.00  --sat_mode                              false
% 2.63/1.00  --sat_fm_restart_options                ""
% 2.63/1.00  --sat_gr_def                            false
% 2.63/1.00  --sat_epr_types                         true
% 2.63/1.00  --sat_non_cyclic_types                  false
% 2.63/1.00  --sat_finite_models                     false
% 2.63/1.00  --sat_fm_lemmas                         false
% 2.63/1.00  --sat_fm_prep                           false
% 2.63/1.00  --sat_fm_uc_incr                        true
% 2.63/1.00  --sat_out_model                         small
% 2.63/1.00  --sat_out_clauses                       false
% 2.63/1.00  
% 2.63/1.00  ------ QBF Options
% 2.63/1.00  
% 2.63/1.00  --qbf_mode                              false
% 2.63/1.00  --qbf_elim_univ                         false
% 2.63/1.00  --qbf_dom_inst                          none
% 2.63/1.00  --qbf_dom_pre_inst                      false
% 2.63/1.00  --qbf_sk_in                             false
% 2.63/1.00  --qbf_pred_elim                         true
% 2.63/1.00  --qbf_split                             512
% 2.63/1.00  
% 2.63/1.00  ------ BMC1 Options
% 2.63/1.00  
% 2.63/1.00  --bmc1_incremental                      false
% 2.63/1.00  --bmc1_axioms                           reachable_all
% 2.63/1.00  --bmc1_min_bound                        0
% 2.63/1.00  --bmc1_max_bound                        -1
% 2.63/1.00  --bmc1_max_bound_default                -1
% 2.63/1.00  --bmc1_symbol_reachability              true
% 2.63/1.00  --bmc1_property_lemmas                  false
% 2.63/1.00  --bmc1_k_induction                      false
% 2.63/1.00  --bmc1_non_equiv_states                 false
% 2.63/1.00  --bmc1_deadlock                         false
% 2.63/1.00  --bmc1_ucm                              false
% 2.63/1.00  --bmc1_add_unsat_core                   none
% 2.63/1.00  --bmc1_unsat_core_children              false
% 2.63/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.63/1.00  --bmc1_out_stat                         full
% 2.63/1.00  --bmc1_ground_init                      false
% 2.63/1.00  --bmc1_pre_inst_next_state              false
% 2.63/1.00  --bmc1_pre_inst_state                   false
% 2.63/1.00  --bmc1_pre_inst_reach_state             false
% 2.63/1.00  --bmc1_out_unsat_core                   false
% 2.63/1.00  --bmc1_aig_witness_out                  false
% 2.63/1.00  --bmc1_verbose                          false
% 2.63/1.00  --bmc1_dump_clauses_tptp                false
% 2.63/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.63/1.00  --bmc1_dump_file                        -
% 2.63/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.63/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.63/1.00  --bmc1_ucm_extend_mode                  1
% 2.63/1.00  --bmc1_ucm_init_mode                    2
% 2.63/1.00  --bmc1_ucm_cone_mode                    none
% 2.63/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.63/1.00  --bmc1_ucm_relax_model                  4
% 2.63/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.63/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.63/1.00  --bmc1_ucm_layered_model                none
% 2.63/1.00  --bmc1_ucm_max_lemma_size               10
% 2.63/1.00  
% 2.63/1.00  ------ AIG Options
% 2.63/1.00  
% 2.63/1.00  --aig_mode                              false
% 2.63/1.00  
% 2.63/1.00  ------ Instantiation Options
% 2.63/1.00  
% 2.63/1.00  --instantiation_flag                    true
% 2.63/1.00  --inst_sos_flag                         false
% 2.63/1.00  --inst_sos_phase                        true
% 2.63/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.63/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.63/1.00  --inst_lit_sel_side                     num_symb
% 2.63/1.00  --inst_solver_per_active                1400
% 2.63/1.00  --inst_solver_calls_frac                1.
% 2.63/1.00  --inst_passive_queue_type               priority_queues
% 2.63/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.63/1.00  --inst_passive_queues_freq              [25;2]
% 2.63/1.00  --inst_dismatching                      true
% 2.63/1.00  --inst_eager_unprocessed_to_passive     true
% 2.63/1.00  --inst_prop_sim_given                   true
% 2.63/1.00  --inst_prop_sim_new                     false
% 2.63/1.00  --inst_subs_new                         false
% 2.63/1.00  --inst_eq_res_simp                      false
% 2.63/1.00  --inst_subs_given                       false
% 2.63/1.00  --inst_orphan_elimination               true
% 2.63/1.00  --inst_learning_loop_flag               true
% 2.63/1.00  --inst_learning_start                   3000
% 2.63/1.00  --inst_learning_factor                  2
% 2.63/1.00  --inst_start_prop_sim_after_learn       3
% 2.63/1.00  --inst_sel_renew                        solver
% 2.63/1.00  --inst_lit_activity_flag                true
% 2.63/1.00  --inst_restr_to_given                   false
% 2.63/1.00  --inst_activity_threshold               500
% 2.63/1.00  --inst_out_proof                        true
% 2.63/1.00  
% 2.63/1.00  ------ Resolution Options
% 2.63/1.00  
% 2.63/1.00  --resolution_flag                       true
% 2.63/1.00  --res_lit_sel                           adaptive
% 2.63/1.00  --res_lit_sel_side                      none
% 2.63/1.00  --res_ordering                          kbo
% 2.63/1.00  --res_to_prop_solver                    active
% 2.63/1.00  --res_prop_simpl_new                    false
% 2.63/1.00  --res_prop_simpl_given                  true
% 2.63/1.00  --res_passive_queue_type                priority_queues
% 2.63/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.63/1.00  --res_passive_queues_freq               [15;5]
% 2.63/1.00  --res_forward_subs                      full
% 2.63/1.00  --res_backward_subs                     full
% 2.63/1.00  --res_forward_subs_resolution           true
% 2.63/1.00  --res_backward_subs_resolution          true
% 2.63/1.00  --res_orphan_elimination                true
% 2.63/1.00  --res_time_limit                        2.
% 2.63/1.00  --res_out_proof                         true
% 2.63/1.00  
% 2.63/1.00  ------ Superposition Options
% 2.63/1.00  
% 2.63/1.00  --superposition_flag                    true
% 2.63/1.00  --sup_passive_queue_type                priority_queues
% 2.63/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.63/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.63/1.00  --demod_completeness_check              fast
% 2.63/1.00  --demod_use_ground                      true
% 2.63/1.00  --sup_to_prop_solver                    passive
% 2.63/1.00  --sup_prop_simpl_new                    true
% 2.63/1.00  --sup_prop_simpl_given                  true
% 2.63/1.00  --sup_fun_splitting                     false
% 2.63/1.00  --sup_smt_interval                      50000
% 2.63/1.00  
% 2.63/1.00  ------ Superposition Simplification Setup
% 2.63/1.00  
% 2.63/1.00  --sup_indices_passive                   []
% 2.63/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.63/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/1.00  --sup_full_bw                           [BwDemod]
% 2.63/1.00  --sup_immed_triv                        [TrivRules]
% 2.63/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.63/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/1.00  --sup_immed_bw_main                     []
% 2.63/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.63/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/1.00  
% 2.63/1.00  ------ Combination Options
% 2.63/1.00  
% 2.63/1.00  --comb_res_mult                         3
% 2.63/1.00  --comb_sup_mult                         2
% 2.63/1.00  --comb_inst_mult                        10
% 2.63/1.00  
% 2.63/1.00  ------ Debug Options
% 2.63/1.00  
% 2.63/1.00  --dbg_backtrace                         false
% 2.63/1.00  --dbg_dump_prop_clauses                 false
% 2.63/1.00  --dbg_dump_prop_clauses_file            -
% 2.63/1.00  --dbg_out_stat                          false
% 2.63/1.00  ------ Parsing...
% 2.63/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.63/1.00  
% 2.63/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.63/1.00  
% 2.63/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.63/1.00  
% 2.63/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.63/1.00  ------ Proving...
% 2.63/1.00  ------ Problem Properties 
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  clauses                                 24
% 2.63/1.00  conjectures                             5
% 2.63/1.00  EPR                                     2
% 2.63/1.00  Horn                                    23
% 2.63/1.00  unary                                   9
% 2.63/1.00  binary                                  1
% 2.63/1.00  lits                                    77
% 2.63/1.00  lits eq                                 17
% 2.63/1.00  fd_pure                                 0
% 2.63/1.00  fd_pseudo                               0
% 2.63/1.00  fd_cond                                 0
% 2.63/1.00  fd_pseudo_cond                          1
% 2.63/1.00  AC symbols                              0
% 2.63/1.00  
% 2.63/1.00  ------ Schedule dynamic 5 is on 
% 2.63/1.00  
% 2.63/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  ------ 
% 2.63/1.00  Current options:
% 2.63/1.00  ------ 
% 2.63/1.00  
% 2.63/1.00  ------ Input Options
% 2.63/1.00  
% 2.63/1.00  --out_options                           all
% 2.63/1.00  --tptp_safe_out                         true
% 2.63/1.00  --problem_path                          ""
% 2.63/1.00  --include_path                          ""
% 2.63/1.00  --clausifier                            res/vclausify_rel
% 2.63/1.00  --clausifier_options                    --mode clausify
% 2.63/1.00  --stdin                                 false
% 2.63/1.00  --stats_out                             all
% 2.63/1.00  
% 2.63/1.00  ------ General Options
% 2.63/1.00  
% 2.63/1.00  --fof                                   false
% 2.63/1.00  --time_out_real                         305.
% 2.63/1.00  --time_out_virtual                      -1.
% 2.63/1.00  --symbol_type_check                     false
% 2.63/1.00  --clausify_out                          false
% 2.63/1.00  --sig_cnt_out                           false
% 2.63/1.00  --trig_cnt_out                          false
% 2.63/1.00  --trig_cnt_out_tolerance                1.
% 2.63/1.00  --trig_cnt_out_sk_spl                   false
% 2.63/1.00  --abstr_cl_out                          false
% 2.63/1.00  
% 2.63/1.00  ------ Global Options
% 2.63/1.00  
% 2.63/1.00  --schedule                              default
% 2.63/1.00  --add_important_lit                     false
% 2.63/1.00  --prop_solver_per_cl                    1000
% 2.63/1.00  --min_unsat_core                        false
% 2.63/1.00  --soft_assumptions                      false
% 2.63/1.00  --soft_lemma_size                       3
% 2.63/1.00  --prop_impl_unit_size                   0
% 2.63/1.00  --prop_impl_unit                        []
% 2.63/1.00  --share_sel_clauses                     true
% 2.63/1.00  --reset_solvers                         false
% 2.63/1.00  --bc_imp_inh                            [conj_cone]
% 2.63/1.00  --conj_cone_tolerance                   3.
% 2.63/1.00  --extra_neg_conj                        none
% 2.63/1.00  --large_theory_mode                     true
% 2.63/1.00  --prolific_symb_bound                   200
% 2.63/1.00  --lt_threshold                          2000
% 2.63/1.00  --clause_weak_htbl                      true
% 2.63/1.00  --gc_record_bc_elim                     false
% 2.63/1.00  
% 2.63/1.00  ------ Preprocessing Options
% 2.63/1.00  
% 2.63/1.00  --preprocessing_flag                    true
% 2.63/1.00  --time_out_prep_mult                    0.1
% 2.63/1.00  --splitting_mode                        input
% 2.63/1.00  --splitting_grd                         true
% 2.63/1.00  --splitting_cvd                         false
% 2.63/1.00  --splitting_cvd_svl                     false
% 2.63/1.00  --splitting_nvd                         32
% 2.63/1.00  --sub_typing                            true
% 2.63/1.00  --prep_gs_sim                           true
% 2.63/1.00  --prep_unflatten                        true
% 2.63/1.00  --prep_res_sim                          true
% 2.63/1.00  --prep_upred                            true
% 2.63/1.00  --prep_sem_filter                       exhaustive
% 2.63/1.00  --prep_sem_filter_out                   false
% 2.63/1.00  --pred_elim                             true
% 2.63/1.00  --res_sim_input                         true
% 2.63/1.00  --eq_ax_congr_red                       true
% 2.63/1.00  --pure_diseq_elim                       true
% 2.63/1.00  --brand_transform                       false
% 2.63/1.00  --non_eq_to_eq                          false
% 2.63/1.00  --prep_def_merge                        true
% 2.63/1.00  --prep_def_merge_prop_impl              false
% 2.63/1.00  --prep_def_merge_mbd                    true
% 2.63/1.00  --prep_def_merge_tr_red                 false
% 2.63/1.00  --prep_def_merge_tr_cl                  false
% 2.63/1.00  --smt_preprocessing                     true
% 2.63/1.00  --smt_ac_axioms                         fast
% 2.63/1.00  --preprocessed_out                      false
% 2.63/1.00  --preprocessed_stats                    false
% 2.63/1.00  
% 2.63/1.00  ------ Abstraction refinement Options
% 2.63/1.00  
% 2.63/1.00  --abstr_ref                             []
% 2.63/1.00  --abstr_ref_prep                        false
% 2.63/1.00  --abstr_ref_until_sat                   false
% 2.63/1.00  --abstr_ref_sig_restrict                funpre
% 2.63/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.63/1.00  --abstr_ref_under                       []
% 2.63/1.00  
% 2.63/1.00  ------ SAT Options
% 2.63/1.00  
% 2.63/1.00  --sat_mode                              false
% 2.63/1.00  --sat_fm_restart_options                ""
% 2.63/1.00  --sat_gr_def                            false
% 2.63/1.00  --sat_epr_types                         true
% 2.63/1.00  --sat_non_cyclic_types                  false
% 2.63/1.00  --sat_finite_models                     false
% 2.63/1.00  --sat_fm_lemmas                         false
% 2.63/1.00  --sat_fm_prep                           false
% 2.63/1.00  --sat_fm_uc_incr                        true
% 2.63/1.00  --sat_out_model                         small
% 2.63/1.00  --sat_out_clauses                       false
% 2.63/1.00  
% 2.63/1.00  ------ QBF Options
% 2.63/1.00  
% 2.63/1.00  --qbf_mode                              false
% 2.63/1.00  --qbf_elim_univ                         false
% 2.63/1.00  --qbf_dom_inst                          none
% 2.63/1.00  --qbf_dom_pre_inst                      false
% 2.63/1.00  --qbf_sk_in                             false
% 2.63/1.00  --qbf_pred_elim                         true
% 2.63/1.00  --qbf_split                             512
% 2.63/1.00  
% 2.63/1.00  ------ BMC1 Options
% 2.63/1.00  
% 2.63/1.00  --bmc1_incremental                      false
% 2.63/1.00  --bmc1_axioms                           reachable_all
% 2.63/1.00  --bmc1_min_bound                        0
% 2.63/1.00  --bmc1_max_bound                        -1
% 2.63/1.00  --bmc1_max_bound_default                -1
% 2.63/1.00  --bmc1_symbol_reachability              true
% 2.63/1.00  --bmc1_property_lemmas                  false
% 2.63/1.00  --bmc1_k_induction                      false
% 2.63/1.00  --bmc1_non_equiv_states                 false
% 2.63/1.00  --bmc1_deadlock                         false
% 2.63/1.00  --bmc1_ucm                              false
% 2.63/1.00  --bmc1_add_unsat_core                   none
% 2.63/1.00  --bmc1_unsat_core_children              false
% 2.63/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.63/1.00  --bmc1_out_stat                         full
% 2.63/1.00  --bmc1_ground_init                      false
% 2.63/1.00  --bmc1_pre_inst_next_state              false
% 2.63/1.00  --bmc1_pre_inst_state                   false
% 2.63/1.00  --bmc1_pre_inst_reach_state             false
% 2.63/1.00  --bmc1_out_unsat_core                   false
% 2.63/1.00  --bmc1_aig_witness_out                  false
% 2.63/1.00  --bmc1_verbose                          false
% 2.63/1.00  --bmc1_dump_clauses_tptp                false
% 2.63/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.63/1.00  --bmc1_dump_file                        -
% 2.63/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.63/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.63/1.00  --bmc1_ucm_extend_mode                  1
% 2.63/1.00  --bmc1_ucm_init_mode                    2
% 2.63/1.00  --bmc1_ucm_cone_mode                    none
% 2.63/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.63/1.00  --bmc1_ucm_relax_model                  4
% 2.63/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.63/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.63/1.00  --bmc1_ucm_layered_model                none
% 2.63/1.00  --bmc1_ucm_max_lemma_size               10
% 2.63/1.00  
% 2.63/1.00  ------ AIG Options
% 2.63/1.00  
% 2.63/1.00  --aig_mode                              false
% 2.63/1.00  
% 2.63/1.00  ------ Instantiation Options
% 2.63/1.00  
% 2.63/1.00  --instantiation_flag                    true
% 2.63/1.00  --inst_sos_flag                         false
% 2.63/1.00  --inst_sos_phase                        true
% 2.63/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.63/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.63/1.00  --inst_lit_sel_side                     none
% 2.63/1.00  --inst_solver_per_active                1400
% 2.63/1.00  --inst_solver_calls_frac                1.
% 2.63/1.00  --inst_passive_queue_type               priority_queues
% 2.63/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.63/1.00  --inst_passive_queues_freq              [25;2]
% 2.63/1.00  --inst_dismatching                      true
% 2.63/1.00  --inst_eager_unprocessed_to_passive     true
% 2.63/1.00  --inst_prop_sim_given                   true
% 2.63/1.00  --inst_prop_sim_new                     false
% 2.63/1.00  --inst_subs_new                         false
% 2.63/1.00  --inst_eq_res_simp                      false
% 2.63/1.00  --inst_subs_given                       false
% 2.63/1.00  --inst_orphan_elimination               true
% 2.63/1.00  --inst_learning_loop_flag               true
% 2.63/1.00  --inst_learning_start                   3000
% 2.63/1.00  --inst_learning_factor                  2
% 2.63/1.00  --inst_start_prop_sim_after_learn       3
% 2.63/1.00  --inst_sel_renew                        solver
% 2.63/1.00  --inst_lit_activity_flag                true
% 2.63/1.00  --inst_restr_to_given                   false
% 2.63/1.00  --inst_activity_threshold               500
% 2.63/1.00  --inst_out_proof                        true
% 2.63/1.00  
% 2.63/1.00  ------ Resolution Options
% 2.63/1.00  
% 2.63/1.00  --resolution_flag                       false
% 2.63/1.00  --res_lit_sel                           adaptive
% 2.63/1.00  --res_lit_sel_side                      none
% 2.63/1.00  --res_ordering                          kbo
% 2.63/1.00  --res_to_prop_solver                    active
% 2.63/1.00  --res_prop_simpl_new                    false
% 2.63/1.00  --res_prop_simpl_given                  true
% 2.63/1.00  --res_passive_queue_type                priority_queues
% 2.63/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.63/1.00  --res_passive_queues_freq               [15;5]
% 2.63/1.00  --res_forward_subs                      full
% 2.63/1.00  --res_backward_subs                     full
% 2.63/1.00  --res_forward_subs_resolution           true
% 2.63/1.00  --res_backward_subs_resolution          true
% 2.63/1.00  --res_orphan_elimination                true
% 2.63/1.00  --res_time_limit                        2.
% 2.63/1.00  --res_out_proof                         true
% 2.63/1.00  
% 2.63/1.00  ------ Superposition Options
% 2.63/1.00  
% 2.63/1.00  --superposition_flag                    true
% 2.63/1.00  --sup_passive_queue_type                priority_queues
% 2.63/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.63/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.63/1.00  --demod_completeness_check              fast
% 2.63/1.00  --demod_use_ground                      true
% 2.63/1.00  --sup_to_prop_solver                    passive
% 2.63/1.00  --sup_prop_simpl_new                    true
% 2.63/1.00  --sup_prop_simpl_given                  true
% 2.63/1.00  --sup_fun_splitting                     false
% 2.63/1.00  --sup_smt_interval                      50000
% 2.63/1.00  
% 2.63/1.00  ------ Superposition Simplification Setup
% 2.63/1.00  
% 2.63/1.00  --sup_indices_passive                   []
% 2.63/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.63/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.63/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/1.00  --sup_full_bw                           [BwDemod]
% 2.63/1.00  --sup_immed_triv                        [TrivRules]
% 2.63/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.63/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/1.00  --sup_immed_bw_main                     []
% 2.63/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.63/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.63/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.63/1.00  
% 2.63/1.00  ------ Combination Options
% 2.63/1.00  
% 2.63/1.00  --comb_res_mult                         3
% 2.63/1.00  --comb_sup_mult                         2
% 2.63/1.00  --comb_inst_mult                        10
% 2.63/1.00  
% 2.63/1.00  ------ Debug Options
% 2.63/1.00  
% 2.63/1.00  --dbg_backtrace                         false
% 2.63/1.00  --dbg_dump_prop_clauses                 false
% 2.63/1.00  --dbg_dump_prop_clauses_file            -
% 2.63/1.00  --dbg_out_stat                          false
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  ------ Proving...
% 2.63/1.00  
% 2.63/1.00  
% 2.63/1.00  % SZS status Theorem for theBenchmark.p
% 2.63/1.00  
% 2.63/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.63/1.00  
% 2.63/1.00  fof(f16,conjecture,(
% 2.63/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f17,negated_conjecture,(
% 2.63/1.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.63/1.00    inference(negated_conjecture,[],[f16])).
% 2.63/1.00  
% 2.63/1.00  fof(f41,plain,(
% 2.63/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.63/1.00    inference(ennf_transformation,[],[f17])).
% 2.63/1.00  
% 2.63/1.00  fof(f42,plain,(
% 2.63/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.63/1.00    inference(flattening,[],[f41])).
% 2.63/1.00  
% 2.63/1.00  fof(f47,plain,(
% 2.63/1.00    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.63/1.00    introduced(choice_axiom,[])).
% 2.63/1.00  
% 2.63/1.00  fof(f46,plain,(
% 2.63/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.63/1.00    introduced(choice_axiom,[])).
% 2.63/1.00  
% 2.63/1.00  fof(f45,plain,(
% 2.63/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.63/1.00    introduced(choice_axiom,[])).
% 2.63/1.00  
% 2.63/1.00  fof(f48,plain,(
% 2.63/1.00    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.63/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f47,f46,f45])).
% 2.63/1.00  
% 2.63/1.00  fof(f77,plain,(
% 2.63/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.63/1.00    inference(cnf_transformation,[],[f48])).
% 2.63/1.00  
% 2.63/1.00  fof(f13,axiom,(
% 2.63/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f36,plain,(
% 2.63/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.63/1.00    inference(ennf_transformation,[],[f13])).
% 2.63/1.00  
% 2.63/1.00  fof(f69,plain,(
% 2.63/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f36])).
% 2.63/1.00  
% 2.63/1.00  fof(f72,plain,(
% 2.63/1.00    l1_struct_0(sK0)),
% 2.63/1.00    inference(cnf_transformation,[],[f48])).
% 2.63/1.00  
% 2.63/1.00  fof(f74,plain,(
% 2.63/1.00    l1_struct_0(sK1)),
% 2.63/1.00    inference(cnf_transformation,[],[f48])).
% 2.63/1.00  
% 2.63/1.00  fof(f8,axiom,(
% 2.63/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f27,plain,(
% 2.63/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.63/1.00    inference(ennf_transformation,[],[f8])).
% 2.63/1.00  
% 2.63/1.00  fof(f59,plain,(
% 2.63/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.63/1.00    inference(cnf_transformation,[],[f27])).
% 2.63/1.00  
% 2.63/1.00  fof(f78,plain,(
% 2.63/1.00    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.63/1.00    inference(cnf_transformation,[],[f48])).
% 2.63/1.00  
% 2.63/1.00  fof(f11,axiom,(
% 2.63/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f32,plain,(
% 2.63/1.00    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.63/1.00    inference(ennf_transformation,[],[f11])).
% 2.63/1.00  
% 2.63/1.00  fof(f33,plain,(
% 2.63/1.00    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.63/1.00    inference(flattening,[],[f32])).
% 2.63/1.00  
% 2.63/1.00  fof(f64,plain,(
% 2.63/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f33])).
% 2.63/1.00  
% 2.63/1.00  fof(f9,axiom,(
% 2.63/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f28,plain,(
% 2.63/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.63/1.00    inference(ennf_transformation,[],[f9])).
% 2.63/1.00  
% 2.63/1.00  fof(f29,plain,(
% 2.63/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.63/1.00    inference(flattening,[],[f28])).
% 2.63/1.00  
% 2.63/1.00  fof(f43,plain,(
% 2.63/1.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.63/1.00    inference(nnf_transformation,[],[f29])).
% 2.63/1.00  
% 2.63/1.00  fof(f60,plain,(
% 2.63/1.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f43])).
% 2.63/1.00  
% 2.63/1.00  fof(f7,axiom,(
% 2.63/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f18,plain,(
% 2.63/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.63/1.00    inference(pure_predicate_removal,[],[f7])).
% 2.63/1.00  
% 2.63/1.00  fof(f26,plain,(
% 2.63/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.63/1.00    inference(ennf_transformation,[],[f18])).
% 2.63/1.00  
% 2.63/1.00  fof(f58,plain,(
% 2.63/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.63/1.00    inference(cnf_transformation,[],[f26])).
% 2.63/1.00  
% 2.63/1.00  fof(f3,axiom,(
% 2.63/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f51,plain,(
% 2.63/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.63/1.00    inference(cnf_transformation,[],[f3])).
% 2.63/1.00  
% 2.63/1.00  fof(f2,axiom,(
% 2.63/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f19,plain,(
% 2.63/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.63/1.00    inference(ennf_transformation,[],[f2])).
% 2.63/1.00  
% 2.63/1.00  fof(f50,plain,(
% 2.63/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f19])).
% 2.63/1.00  
% 2.63/1.00  fof(f75,plain,(
% 2.63/1.00    v1_funct_1(sK2)),
% 2.63/1.00    inference(cnf_transformation,[],[f48])).
% 2.63/1.00  
% 2.63/1.00  fof(f76,plain,(
% 2.63/1.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.63/1.00    inference(cnf_transformation,[],[f48])).
% 2.63/1.00  
% 2.63/1.00  fof(f1,axiom,(
% 2.63/1.00    v1_xboole_0(k1_xboole_0)),
% 2.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f49,plain,(
% 2.63/1.00    v1_xboole_0(k1_xboole_0)),
% 2.63/1.00    inference(cnf_transformation,[],[f1])).
% 2.63/1.00  
% 2.63/1.00  fof(f14,axiom,(
% 2.63/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 2.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f37,plain,(
% 2.63/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.63/1.00    inference(ennf_transformation,[],[f14])).
% 2.63/1.00  
% 2.63/1.00  fof(f38,plain,(
% 2.63/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.63/1.00    inference(flattening,[],[f37])).
% 2.63/1.00  
% 2.63/1.00  fof(f70,plain,(
% 2.63/1.00    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f38])).
% 2.63/1.00  
% 2.63/1.00  fof(f73,plain,(
% 2.63/1.00    ~v2_struct_0(sK1)),
% 2.63/1.00    inference(cnf_transformation,[],[f48])).
% 2.63/1.00  
% 2.63/1.00  fof(f15,axiom,(
% 2.63/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f39,plain,(
% 2.63/1.00    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.63/1.00    inference(ennf_transformation,[],[f15])).
% 2.63/1.00  
% 2.63/1.00  fof(f40,plain,(
% 2.63/1.00    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.63/1.00    inference(flattening,[],[f39])).
% 2.63/1.00  
% 2.63/1.00  fof(f71,plain,(
% 2.63/1.00    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f40])).
% 2.63/1.00  
% 2.63/1.00  fof(f79,plain,(
% 2.63/1.00    v2_funct_1(sK2)),
% 2.63/1.00    inference(cnf_transformation,[],[f48])).
% 2.63/1.00  
% 2.63/1.00  fof(f10,axiom,(
% 2.63/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f30,plain,(
% 2.63/1.00    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.63/1.00    inference(ennf_transformation,[],[f10])).
% 2.63/1.00  
% 2.63/1.00  fof(f31,plain,(
% 2.63/1.00    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.63/1.00    inference(flattening,[],[f30])).
% 2.63/1.00  
% 2.63/1.00  fof(f44,plain,(
% 2.63/1.00    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.63/1.00    inference(nnf_transformation,[],[f31])).
% 2.63/1.00  
% 2.63/1.00  fof(f63,plain,(
% 2.63/1.00    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f44])).
% 2.63/1.00  
% 2.63/1.00  fof(f82,plain,(
% 2.63/1.00    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.63/1.00    inference(equality_resolution,[],[f63])).
% 2.63/1.00  
% 2.63/1.00  fof(f80,plain,(
% 2.63/1.00    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 2.63/1.00    inference(cnf_transformation,[],[f48])).
% 2.63/1.00  
% 2.63/1.00  fof(f12,axiom,(
% 2.63/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f34,plain,(
% 2.63/1.00    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.63/1.00    inference(ennf_transformation,[],[f12])).
% 2.63/1.00  
% 2.63/1.00  fof(f35,plain,(
% 2.63/1.00    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.63/1.00    inference(flattening,[],[f34])).
% 2.63/1.00  
% 2.63/1.00  fof(f68,plain,(
% 2.63/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f35])).
% 2.63/1.00  
% 2.63/1.00  fof(f5,axiom,(
% 2.63/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f22,plain,(
% 2.63/1.00    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.63/1.00    inference(ennf_transformation,[],[f5])).
% 2.63/1.00  
% 2.63/1.00  fof(f23,plain,(
% 2.63/1.00    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.63/1.00    inference(flattening,[],[f22])).
% 2.63/1.00  
% 2.63/1.00  fof(f56,plain,(
% 2.63/1.00    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f23])).
% 2.63/1.00  
% 2.63/1.00  fof(f6,axiom,(
% 2.63/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f24,plain,(
% 2.63/1.00    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.63/1.00    inference(ennf_transformation,[],[f6])).
% 2.63/1.00  
% 2.63/1.00  fof(f25,plain,(
% 2.63/1.00    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.63/1.00    inference(flattening,[],[f24])).
% 2.63/1.00  
% 2.63/1.00  fof(f57,plain,(
% 2.63/1.00    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f25])).
% 2.63/1.00  
% 2.63/1.00  fof(f4,axiom,(
% 2.63/1.00    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.63/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.63/1.00  
% 2.63/1.00  fof(f20,plain,(
% 2.63/1.00    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.63/1.00    inference(ennf_transformation,[],[f4])).
% 2.63/1.00  
% 2.63/1.00  fof(f21,plain,(
% 2.63/1.00    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.63/1.00    inference(flattening,[],[f20])).
% 2.63/1.00  
% 2.63/1.00  fof(f54,plain,(
% 2.63/1.00    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f21])).
% 2.63/1.00  
% 2.63/1.00  fof(f53,plain,(
% 2.63/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f21])).
% 2.63/1.00  
% 2.63/1.00  fof(f67,plain,(
% 2.63/1.00    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.63/1.00    inference(cnf_transformation,[],[f35])).
% 2.63/1.00  
% 2.63/1.00  cnf(c_26,negated_conjecture,
% 2.63/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.63/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_665,negated_conjecture,
% 2.63/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_26]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1102,plain,
% 2.63/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_665]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_20,plain,
% 2.63/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.63/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_31,negated_conjecture,
% 2.63/1.00      ( l1_struct_0(sK0) ),
% 2.63/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_380,plain,
% 2.63/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.63/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_31]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_381,plain,
% 2.63/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.63/1.00      inference(unflattening,[status(thm)],[c_380]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_660,plain,
% 2.63/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_381]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_29,negated_conjecture,
% 2.63/1.00      ( l1_struct_0(sK1) ),
% 2.63/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_375,plain,
% 2.63/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.63/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_376,plain,
% 2.63/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.63/1.00      inference(unflattening,[status(thm)],[c_375]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_661,plain,
% 2.63/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_376]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1126,plain,
% 2.63/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.63/1.00      inference(light_normalisation,[status(thm)],[c_1102,c_660,c_661]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_10,plain,
% 2.63/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.63/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.63/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_672,plain,
% 2.63/1.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.63/1.00      | k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52) ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1096,plain,
% 2.63/1.00      ( k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52)
% 2.63/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_672]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1474,plain,
% 2.63/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.63/1.00      inference(superposition,[status(thm)],[c_1126,c_1096]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_25,negated_conjecture,
% 2.63/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.63/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_666,negated_conjecture,
% 2.63/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_25]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1123,plain,
% 2.63/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.63/1.00      inference(light_normalisation,[status(thm)],[c_666,c_660,c_661]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1585,plain,
% 2.63/1.00      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.63/1.00      inference(demodulation,[status(thm)],[c_1474,c_1123]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1589,plain,
% 2.63/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.63/1.00      inference(demodulation,[status(thm)],[c_1585,c_1126]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_16,plain,
% 2.63/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.63/1.00      | v1_partfun1(X0,X1)
% 2.63/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.63/1.00      | ~ v1_funct_1(X0)
% 2.63/1.00      | k1_xboole_0 = X2 ),
% 2.63/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_12,plain,
% 2.63/1.00      ( ~ v1_partfun1(X0,X1)
% 2.63/1.00      | ~ v4_relat_1(X0,X1)
% 2.63/1.00      | ~ v1_relat_1(X0)
% 2.63/1.00      | k1_relat_1(X0) = X1 ),
% 2.63/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_449,plain,
% 2.63/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.63/1.00      | ~ v4_relat_1(X0,X1)
% 2.63/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.63/1.00      | ~ v1_funct_1(X0)
% 2.63/1.00      | ~ v1_relat_1(X0)
% 2.63/1.00      | k1_relat_1(X0) = X1
% 2.63/1.00      | k1_xboole_0 = X2 ),
% 2.63/1.00      inference(resolution,[status(thm)],[c_16,c_12]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_9,plain,
% 2.63/1.00      ( v4_relat_1(X0,X1)
% 2.63/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.63/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_453,plain,
% 2.63/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.63/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.63/1.00      | ~ v1_funct_1(X0)
% 2.63/1.00      | ~ v1_relat_1(X0)
% 2.63/1.00      | k1_relat_1(X0) = X1
% 2.63/1.00      | k1_xboole_0 = X2 ),
% 2.63/1.00      inference(global_propositional_subsumption,
% 2.63/1.00                [status(thm)],
% 2.63/1.00                [c_449,c_9]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_658,plain,
% 2.63/1.00      ( ~ v1_funct_2(X0_52,X0_53,X1_53)
% 2.63/1.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.63/1.00      | ~ v1_funct_1(X0_52)
% 2.63/1.00      | ~ v1_relat_1(X0_52)
% 2.63/1.00      | k1_relat_1(X0_52) = X0_53
% 2.63/1.00      | k1_xboole_0 = X1_53 ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_453]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1106,plain,
% 2.63/1.00      ( k1_relat_1(X0_52) = X0_53
% 2.63/1.00      | k1_xboole_0 = X1_53
% 2.63/1.00      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.63/1.00      | v1_funct_1(X0_52) != iProver_top
% 2.63/1.00      | v1_relat_1(X0_52) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_658]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_2,plain,
% 2.63/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.63/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_679,plain,
% 2.63/1.00      ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
% 2.63/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_716,plain,
% 2.63/1.00      ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) = iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_679]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_757,plain,
% 2.63/1.00      ( k1_relat_1(X0_52) = X0_53
% 2.63/1.00      | k1_xboole_0 = X1_53
% 2.63/1.00      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.63/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.63/1.00      | v1_funct_1(X0_52) != iProver_top
% 2.63/1.00      | v1_relat_1(X0_52) != iProver_top ),
% 2.63/1.00      inference(predicate_to_equality,[status(thm)],[c_658]) ).
% 2.63/1.00  
% 2.63/1.00  cnf(c_1,plain,
% 2.63/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.63/1.00      | ~ v1_relat_1(X1)
% 2.63/1.00      | v1_relat_1(X0) ),
% 2.63/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_680,plain,
% 2.63/1.01      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
% 2.63/1.01      | ~ v1_relat_1(X1_52)
% 2.63/1.01      | v1_relat_1(X0_52) ),
% 2.63/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1330,plain,
% 2.63/1.01      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.63/1.01      | v1_relat_1(X0_52)
% 2.63/1.01      | ~ v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
% 2.63/1.01      inference(instantiation,[status(thm)],[c_680]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1331,plain,
% 2.63/1.01      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.63/1.01      | v1_relat_1(X0_52) = iProver_top
% 2.63/1.01      | v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) != iProver_top ),
% 2.63/1.01      inference(predicate_to_equality,[status(thm)],[c_1330]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_2945,plain,
% 2.63/1.01      ( v1_funct_1(X0_52) != iProver_top
% 2.63/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.63/1.01      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.63/1.01      | k1_xboole_0 = X1_53
% 2.63/1.01      | k1_relat_1(X0_52) = X0_53 ),
% 2.63/1.01      inference(global_propositional_subsumption,
% 2.63/1.01                [status(thm)],
% 2.63/1.01                [c_1106,c_716,c_757,c_1331]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_2946,plain,
% 2.63/1.01      ( k1_relat_1(X0_52) = X0_53
% 2.63/1.01      | k1_xboole_0 = X1_53
% 2.63/1.01      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.63/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.63/1.01      | v1_funct_1(X0_52) != iProver_top ),
% 2.63/1.01      inference(renaming,[status(thm)],[c_2945]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_2954,plain,
% 2.63/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.63/1.01      | k2_relat_1(sK2) = k1_xboole_0
% 2.63/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.63/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.63/1.01      inference(superposition,[status(thm)],[c_1589,c_2946]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_28,negated_conjecture,
% 2.63/1.01      ( v1_funct_1(sK2) ),
% 2.63/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_35,plain,
% 2.63/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 2.63/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_27,negated_conjecture,
% 2.63/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.63/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_664,negated_conjecture,
% 2.63/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.63/1.01      inference(subtyping,[status(esa)],[c_27]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1103,plain,
% 2.63/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.63/1.01      inference(predicate_to_equality,[status(thm)],[c_664]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1120,plain,
% 2.63/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.63/1.01      inference(light_normalisation,[status(thm)],[c_1103,c_660,c_661]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1590,plain,
% 2.63/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.63/1.01      inference(demodulation,[status(thm)],[c_1585,c_1120]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_0,plain,
% 2.63/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 2.63/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_21,plain,
% 2.63/1.01      ( v2_struct_0(X0)
% 2.63/1.01      | ~ l1_struct_0(X0)
% 2.63/1.01      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 2.63/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_348,plain,
% 2.63/1.01      ( v2_struct_0(X0)
% 2.63/1.01      | ~ l1_struct_0(X0)
% 2.63/1.01      | k2_struct_0(X0) != k1_xboole_0 ),
% 2.63/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_21]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_30,negated_conjecture,
% 2.63/1.01      ( ~ v2_struct_0(sK1) ),
% 2.63/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_366,plain,
% 2.63/1.01      ( ~ l1_struct_0(X0) | k2_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 2.63/1.01      inference(resolution_lifted,[status(thm)],[c_348,c_30]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_367,plain,
% 2.63/1.01      ( ~ l1_struct_0(sK1) | k2_struct_0(sK1) != k1_xboole_0 ),
% 2.63/1.01      inference(unflattening,[status(thm)],[c_366]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_350,plain,
% 2.63/1.01      ( v2_struct_0(sK1)
% 2.63/1.01      | ~ l1_struct_0(sK1)
% 2.63/1.01      | k2_struct_0(sK1) != k1_xboole_0 ),
% 2.63/1.01      inference(instantiation,[status(thm)],[c_348]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_369,plain,
% 2.63/1.01      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 2.63/1.01      inference(global_propositional_subsumption,
% 2.63/1.01                [status(thm)],
% 2.63/1.01                [c_367,c_30,c_29,c_350]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_662,plain,
% 2.63/1.01      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 2.63/1.01      inference(subtyping,[status(esa)],[c_369]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1591,plain,
% 2.63/1.01      ( k2_relat_1(sK2) != k1_xboole_0 ),
% 2.63/1.01      inference(demodulation,[status(thm)],[c_1585,c_662]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_3296,plain,
% 2.63/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.63/1.01      inference(global_propositional_subsumption,
% 2.63/1.01                [status(thm)],
% 2.63/1.01                [c_2954,c_35,c_1590,c_1591]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1587,plain,
% 2.63/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.63/1.01      inference(demodulation,[status(thm)],[c_1585,c_1474]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_22,plain,
% 2.63/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.63/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.63/1.01      | ~ v1_funct_1(X0)
% 2.63/1.01      | ~ v2_funct_1(X0)
% 2.63/1.01      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.63/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.63/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_668,plain,
% 2.63/1.01      ( ~ v1_funct_2(X0_52,X0_53,X1_53)
% 2.63/1.01      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.63/1.01      | ~ v1_funct_1(X0_52)
% 2.63/1.01      | ~ v2_funct_1(X0_52)
% 2.63/1.01      | k2_relset_1(X0_53,X1_53,X0_52) != X1_53
% 2.63/1.01      | k2_tops_2(X0_53,X1_53,X0_52) = k2_funct_1(X0_52) ),
% 2.63/1.01      inference(subtyping,[status(esa)],[c_22]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1100,plain,
% 2.63/1.01      ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
% 2.63/1.01      | k2_tops_2(X0_53,X1_53,X0_52) = k2_funct_1(X0_52)
% 2.63/1.01      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.63/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.63/1.01      | v1_funct_1(X0_52) != iProver_top
% 2.63/1.01      | v2_funct_1(X0_52) != iProver_top ),
% 2.63/1.01      inference(predicate_to_equality,[status(thm)],[c_668]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_2411,plain,
% 2.63/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 2.63/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.63/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.63/1.01      | v1_funct_1(sK2) != iProver_top
% 2.63/1.01      | v2_funct_1(sK2) != iProver_top ),
% 2.63/1.01      inference(superposition,[status(thm)],[c_1587,c_1100]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_24,negated_conjecture,
% 2.63/1.01      ( v2_funct_1(sK2) ),
% 2.63/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_38,plain,
% 2.63/1.01      ( v2_funct_1(sK2) = iProver_top ),
% 2.63/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_2577,plain,
% 2.63/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.63/1.01      inference(global_propositional_subsumption,
% 2.63/1.01                [status(thm)],
% 2.63/1.01                [c_2411,c_35,c_38,c_1589,c_1590]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_13,plain,
% 2.63/1.01      ( r2_funct_2(X0,X1,X2,X2)
% 2.63/1.01      | ~ v1_funct_2(X2,X0,X1)
% 2.63/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.63/1.01      | ~ v1_funct_1(X2) ),
% 2.63/1.01      inference(cnf_transformation,[],[f82]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_23,negated_conjecture,
% 2.63/1.01      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 2.63/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_428,plain,
% 2.63/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.63/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.63/1.01      | ~ v1_funct_1(X0)
% 2.63/1.01      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 2.63/1.01      | u1_struct_0(sK1) != X2
% 2.63/1.01      | u1_struct_0(sK0) != X1
% 2.63/1.01      | sK2 != X0 ),
% 2.63/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_429,plain,
% 2.63/1.01      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.63/1.01      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.63/1.01      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.63/1.01      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.63/1.01      inference(unflattening,[status(thm)],[c_428]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_659,plain,
% 2.63/1.01      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.63/1.01      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.63/1.01      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.63/1.01      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.63/1.01      inference(subtyping,[status(esa)],[c_429]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1105,plain,
% 2.63/1.01      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.63/1.01      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.63/1.01      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.63/1.01      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 2.63/1.01      inference(predicate_to_equality,[status(thm)],[c_659]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1257,plain,
% 2.63/1.01      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.63/1.01      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.63/1.01      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.63/1.01      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.63/1.01      inference(light_normalisation,[status(thm)],[c_1105,c_660,c_661]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1588,plain,
% 2.63/1.01      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
% 2.63/1.01      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.63/1.01      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.63/1.01      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
% 2.63/1.01      inference(demodulation,[status(thm)],[c_1585,c_1257]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_2580,plain,
% 2.63/1.01      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 2.63/1.01      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.63/1.01      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.63/1.01      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 2.63/1.01      inference(demodulation,[status(thm)],[c_2577,c_1588]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_3299,plain,
% 2.63/1.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 2.63/1.01      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.63/1.01      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.63/1.01      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 2.63/1.01      inference(demodulation,[status(thm)],[c_3296,c_2580]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_17,plain,
% 2.63/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.63/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.63/1.01      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.63/1.01      | ~ v1_funct_1(X0)
% 2.63/1.01      | ~ v2_funct_1(X0)
% 2.63/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.63/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_671,plain,
% 2.63/1.01      ( ~ v1_funct_2(X0_52,X0_53,X1_53)
% 2.63/1.01      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.63/1.01      | m1_subset_1(k2_funct_1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53)))
% 2.63/1.01      | ~ v1_funct_1(X0_52)
% 2.63/1.01      | ~ v2_funct_1(X0_52)
% 2.63/1.01      | k2_relset_1(X0_53,X1_53,X0_52) != X1_53 ),
% 2.63/1.01      inference(subtyping,[status(esa)],[c_17]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1097,plain,
% 2.63/1.01      ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
% 2.63/1.01      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.63/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.63/1.01      | m1_subset_1(k2_funct_1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) = iProver_top
% 2.63/1.01      | v1_funct_1(X0_52) != iProver_top
% 2.63/1.01      | v2_funct_1(X0_52) != iProver_top ),
% 2.63/1.01      inference(predicate_to_equality,[status(thm)],[c_671]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_2346,plain,
% 2.63/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.63/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 2.63/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.63/1.01      | v1_funct_1(sK2) != iProver_top
% 2.63/1.01      | v2_funct_1(sK2) != iProver_top ),
% 2.63/1.01      inference(superposition,[status(thm)],[c_1587,c_1097]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_2583,plain,
% 2.63/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 2.63/1.01      inference(global_propositional_subsumption,
% 2.63/1.01                [status(thm)],
% 2.63/1.01                [c_2346,c_35,c_38,c_1589,c_1590]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_2589,plain,
% 2.63/1.01      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.63/1.01      inference(superposition,[status(thm)],[c_2583,c_1096]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_663,negated_conjecture,
% 2.63/1.01      ( v1_funct_1(sK2) ),
% 2.63/1.01      inference(subtyping,[status(esa)],[c_28]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1104,plain,
% 2.63/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 2.63/1.01      inference(predicate_to_equality,[status(thm)],[c_663]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_6,plain,
% 2.63/1.01      ( ~ v1_funct_1(X0)
% 2.63/1.01      | ~ v2_funct_1(X0)
% 2.63/1.01      | ~ v1_relat_1(X0)
% 2.63/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.63/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_675,plain,
% 2.63/1.01      ( ~ v1_funct_1(X0_52)
% 2.63/1.01      | ~ v2_funct_1(X0_52)
% 2.63/1.01      | ~ v1_relat_1(X0_52)
% 2.63/1.01      | k2_relat_1(k2_funct_1(X0_52)) = k1_relat_1(X0_52) ),
% 2.63/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1093,plain,
% 2.63/1.01      ( k2_relat_1(k2_funct_1(X0_52)) = k1_relat_1(X0_52)
% 2.63/1.01      | v1_funct_1(X0_52) != iProver_top
% 2.63/1.01      | v2_funct_1(X0_52) != iProver_top
% 2.63/1.01      | v1_relat_1(X0_52) != iProver_top ),
% 2.63/1.01      inference(predicate_to_equality,[status(thm)],[c_675]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1820,plain,
% 2.63/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.63/1.01      | v2_funct_1(sK2) != iProver_top
% 2.63/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.63/1.01      inference(superposition,[status(thm)],[c_1104,c_1093]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_729,plain,
% 2.63/1.01      ( ~ v1_funct_1(sK2)
% 2.63/1.01      | ~ v2_funct_1(sK2)
% 2.63/1.01      | ~ v1_relat_1(sK2)
% 2.63/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.63/1.01      inference(instantiation,[status(thm)],[c_675]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1451,plain,
% 2.63/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.63/1.01      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.63/1.01      | v1_relat_1(sK2) ),
% 2.63/1.01      inference(instantiation,[status(thm)],[c_1330]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1480,plain,
% 2.63/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.63/1.01      inference(instantiation,[status(thm)],[c_679]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_2069,plain,
% 2.63/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.63/1.01      inference(global_propositional_subsumption,
% 2.63/1.01                [status(thm)],
% 2.63/1.01                [c_1820,c_28,c_26,c_24,c_729,c_1451,c_1480]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_2596,plain,
% 2.63/1.01      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.63/1.01      inference(light_normalisation,[status(thm)],[c_2589,c_2069]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_2667,plain,
% 2.63/1.01      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 2.63/1.01      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.63/1.01      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 2.63/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 2.63/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.63/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.63/1.01      inference(superposition,[status(thm)],[c_2596,c_1100]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_8,plain,
% 2.63/1.01      ( ~ v1_funct_1(X0)
% 2.63/1.01      | ~ v2_funct_1(X0)
% 2.63/1.01      | ~ v1_relat_1(X0)
% 2.63/1.01      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.63/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_673,plain,
% 2.63/1.01      ( ~ v1_funct_1(X0_52)
% 2.63/1.01      | ~ v2_funct_1(X0_52)
% 2.63/1.01      | ~ v1_relat_1(X0_52)
% 2.63/1.01      | k2_funct_1(k2_funct_1(X0_52)) = X0_52 ),
% 2.63/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1095,plain,
% 2.63/1.01      ( k2_funct_1(k2_funct_1(X0_52)) = X0_52
% 2.63/1.01      | v1_funct_1(X0_52) != iProver_top
% 2.63/1.01      | v2_funct_1(X0_52) != iProver_top
% 2.63/1.01      | v1_relat_1(X0_52) != iProver_top ),
% 2.63/1.01      inference(predicate_to_equality,[status(thm)],[c_673]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1791,plain,
% 2.63/1.01      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.63/1.01      | v2_funct_1(sK2) != iProver_top
% 2.63/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.63/1.01      inference(superposition,[status(thm)],[c_1104,c_1095]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_735,plain,
% 2.63/1.01      ( ~ v1_funct_1(sK2)
% 2.63/1.01      | ~ v2_funct_1(sK2)
% 2.63/1.01      | ~ v1_relat_1(sK2)
% 2.63/1.01      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.63/1.01      inference(instantiation,[status(thm)],[c_673]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_2053,plain,
% 2.63/1.01      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.63/1.01      inference(global_propositional_subsumption,
% 2.63/1.01                [status(thm)],
% 2.63/1.01                [c_1791,c_28,c_26,c_24,c_735,c_1451,c_1480]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_2690,plain,
% 2.63/1.01      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 2.63/1.01      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 2.63/1.01      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 2.63/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 2.63/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.63/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.63/1.01      inference(light_normalisation,[status(thm)],[c_2667,c_2053]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_37,plain,
% 2.63/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.63/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_3,plain,
% 2.63/1.01      ( ~ v1_funct_1(X0)
% 2.63/1.01      | ~ v2_funct_1(X0)
% 2.63/1.01      | v2_funct_1(k2_funct_1(X0))
% 2.63/1.01      | ~ v1_relat_1(X0) ),
% 2.63/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_678,plain,
% 2.63/1.01      ( ~ v1_funct_1(X0_52)
% 2.63/1.01      | ~ v2_funct_1(X0_52)
% 2.63/1.01      | v2_funct_1(k2_funct_1(X0_52))
% 2.63/1.01      | ~ v1_relat_1(X0_52) ),
% 2.63/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_719,plain,
% 2.63/1.01      ( v1_funct_1(X0_52) != iProver_top
% 2.63/1.01      | v2_funct_1(X0_52) != iProver_top
% 2.63/1.01      | v2_funct_1(k2_funct_1(X0_52)) = iProver_top
% 2.63/1.01      | v1_relat_1(X0_52) != iProver_top ),
% 2.63/1.01      inference(predicate_to_equality,[status(thm)],[c_678]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_721,plain,
% 2.63/1.01      ( v1_funct_1(sK2) != iProver_top
% 2.63/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.63/1.01      | v2_funct_1(sK2) != iProver_top
% 2.63/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.63/1.01      inference(instantiation,[status(thm)],[c_719]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_4,plain,
% 2.63/1.01      ( ~ v1_funct_1(X0)
% 2.63/1.01      | v1_funct_1(k2_funct_1(X0))
% 2.63/1.01      | ~ v2_funct_1(X0)
% 2.63/1.01      | ~ v1_relat_1(X0) ),
% 2.63/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_677,plain,
% 2.63/1.01      ( ~ v1_funct_1(X0_52)
% 2.63/1.01      | v1_funct_1(k2_funct_1(X0_52))
% 2.63/1.01      | ~ v2_funct_1(X0_52)
% 2.63/1.01      | ~ v1_relat_1(X0_52) ),
% 2.63/1.01      inference(subtyping,[status(esa)],[c_4]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_722,plain,
% 2.63/1.01      ( v1_funct_1(X0_52) != iProver_top
% 2.63/1.01      | v1_funct_1(k2_funct_1(X0_52)) = iProver_top
% 2.63/1.01      | v2_funct_1(X0_52) != iProver_top
% 2.63/1.01      | v1_relat_1(X0_52) != iProver_top ),
% 2.63/1.01      inference(predicate_to_equality,[status(thm)],[c_677]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_724,plain,
% 2.63/1.01      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.63/1.01      | v1_funct_1(sK2) != iProver_top
% 2.63/1.01      | v2_funct_1(sK2) != iProver_top
% 2.63/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.63/1.01      inference(instantiation,[status(thm)],[c_722]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1452,plain,
% 2.63/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.63/1.01      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.63/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.63/1.01      inference(predicate_to_equality,[status(thm)],[c_1451]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1481,plain,
% 2.63/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.63/1.01      inference(predicate_to_equality,[status(thm)],[c_1480]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_18,plain,
% 2.63/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.63/1.01      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.63/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.63/1.01      | ~ v1_funct_1(X0)
% 2.63/1.01      | ~ v2_funct_1(X0)
% 2.63/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.63/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_670,plain,
% 2.63/1.01      ( ~ v1_funct_2(X0_52,X0_53,X1_53)
% 2.63/1.01      | v1_funct_2(k2_funct_1(X0_52),X1_53,X0_53)
% 2.63/1.01      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.63/1.01      | ~ v1_funct_1(X0_52)
% 2.63/1.01      | ~ v2_funct_1(X0_52)
% 2.63/1.01      | k2_relset_1(X0_53,X1_53,X0_52) != X1_53 ),
% 2.63/1.01      inference(subtyping,[status(esa)],[c_18]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_1098,plain,
% 2.63/1.01      ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
% 2.63/1.01      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.63/1.01      | v1_funct_2(k2_funct_1(X0_52),X1_53,X0_53) = iProver_top
% 2.63/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.63/1.01      | v1_funct_1(X0_52) != iProver_top
% 2.63/1.01      | v2_funct_1(X0_52) != iProver_top ),
% 2.63/1.01      inference(predicate_to_equality,[status(thm)],[c_670]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_2355,plain,
% 2.63/1.01      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
% 2.63/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.63/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.63/1.01      | v1_funct_1(sK2) != iProver_top
% 2.63/1.01      | v2_funct_1(sK2) != iProver_top ),
% 2.63/1.01      inference(superposition,[status(thm)],[c_1587,c_1098]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_2699,plain,
% 2.63/1.01      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 2.63/1.01      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
% 2.63/1.01      inference(global_propositional_subsumption,
% 2.63/1.01                [status(thm)],
% 2.63/1.01                [c_2690,c_35,c_37,c_38,c_721,c_724,c_1452,c_1481,c_1589,
% 2.63/1.01                 c_1590,c_2346,c_2355]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_3300,plain,
% 2.63/1.01      ( k1_relat_1(sK2) != k1_relat_1(sK2)
% 2.63/1.01      | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 2.63/1.01      inference(demodulation,[status(thm)],[c_3296,c_2699]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_3325,plain,
% 2.63/1.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 2.63/1.01      inference(equality_resolution_simp,[status(thm)],[c_3300]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_3328,plain,
% 2.63/1.01      ( sK2 != sK2
% 2.63/1.01      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.63/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.63/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.63/1.01      inference(light_normalisation,[status(thm)],[c_3299,c_3325]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_3329,plain,
% 2.63/1.01      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.63/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.63/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.63/1.01      inference(equality_resolution_simp,[status(thm)],[c_3328]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_3305,plain,
% 2.63/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 2.63/1.01      inference(demodulation,[status(thm)],[c_3296,c_1589]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_3307,plain,
% 2.63/1.01      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 2.63/1.01      inference(demodulation,[status(thm)],[c_3296,c_1590]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(c_3333,plain,
% 2.63/1.01      ( v1_funct_1(sK2) != iProver_top ),
% 2.63/1.01      inference(forward_subsumption_resolution,
% 2.63/1.01                [status(thm)],
% 2.63/1.01                [c_3329,c_3305,c_3307]) ).
% 2.63/1.01  
% 2.63/1.01  cnf(contradiction,plain,
% 2.63/1.01      ( $false ),
% 2.63/1.01      inference(minisat,[status(thm)],[c_3333,c_35]) ).
% 2.63/1.01  
% 2.63/1.01  
% 2.63/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.63/1.01  
% 2.63/1.01  ------                               Statistics
% 2.63/1.01  
% 2.63/1.01  ------ General
% 2.63/1.01  
% 2.63/1.01  abstr_ref_over_cycles:                  0
% 2.63/1.01  abstr_ref_under_cycles:                 0
% 2.63/1.01  gc_basic_clause_elim:                   0
% 2.63/1.01  forced_gc_time:                         0
% 2.63/1.01  parsing_time:                           0.017
% 2.63/1.01  unif_index_cands_time:                  0.
% 2.63/1.01  unif_index_add_time:                    0.
% 2.63/1.01  orderings_time:                         0.
% 2.63/1.01  out_proof_time:                         0.013
% 2.63/1.01  total_time:                             0.16
% 2.63/1.01  num_of_symbols:                         56
% 2.63/1.01  num_of_terms:                           2824
% 2.63/1.01  
% 2.63/1.01  ------ Preprocessing
% 2.63/1.01  
% 2.63/1.01  num_of_splits:                          0
% 2.63/1.01  num_of_split_atoms:                     0
% 2.63/1.01  num_of_reused_defs:                     0
% 2.63/1.01  num_eq_ax_congr_red:                    4
% 2.63/1.01  num_of_sem_filtered_clauses:            1
% 2.63/1.01  num_of_subtypes:                        4
% 2.63/1.01  monotx_restored_types:                  1
% 2.63/1.01  sat_num_of_epr_types:                   0
% 2.63/1.01  sat_num_of_non_cyclic_types:            0
% 2.63/1.01  sat_guarded_non_collapsed_types:        1
% 2.63/1.01  num_pure_diseq_elim:                    0
% 2.63/1.01  simp_replaced_by:                       0
% 2.63/1.01  res_preprocessed:                       139
% 2.63/1.01  prep_upred:                             0
% 2.63/1.01  prep_unflattend:                        16
% 2.63/1.01  smt_new_axioms:                         0
% 2.63/1.01  pred_elim_cands:                        5
% 2.63/1.01  pred_elim:                              6
% 2.63/1.01  pred_elim_cl:                           8
% 2.63/1.01  pred_elim_cycles:                       9
% 2.63/1.01  merged_defs:                            0
% 2.63/1.01  merged_defs_ncl:                        0
% 2.63/1.01  bin_hyper_res:                          0
% 2.63/1.01  prep_cycles:                            4
% 2.63/1.01  pred_elim_time:                         0.005
% 2.63/1.01  splitting_time:                         0.
% 2.63/1.01  sem_filter_time:                        0.
% 2.63/1.01  monotx_time:                            0.001
% 2.63/1.01  subtype_inf_time:                       0.001
% 2.63/1.01  
% 2.63/1.01  ------ Problem properties
% 2.63/1.01  
% 2.63/1.01  clauses:                                24
% 2.63/1.01  conjectures:                            5
% 2.63/1.01  epr:                                    2
% 2.63/1.01  horn:                                   23
% 2.63/1.01  ground:                                 9
% 2.63/1.01  unary:                                  9
% 2.63/1.01  binary:                                 1
% 2.63/1.01  lits:                                   77
% 2.63/1.01  lits_eq:                                17
% 2.63/1.01  fd_pure:                                0
% 2.63/1.01  fd_pseudo:                              0
% 2.63/1.01  fd_cond:                                0
% 2.63/1.01  fd_pseudo_cond:                         1
% 2.63/1.01  ac_symbols:                             0
% 2.63/1.01  
% 2.63/1.01  ------ Propositional Solver
% 2.63/1.01  
% 2.63/1.01  prop_solver_calls:                      28
% 2.63/1.01  prop_fast_solver_calls:                 1107
% 2.63/1.01  smt_solver_calls:                       0
% 2.63/1.01  smt_fast_solver_calls:                  0
% 2.63/1.01  prop_num_of_clauses:                    1064
% 2.63/1.01  prop_preprocess_simplified:             4309
% 2.63/1.01  prop_fo_subsumed:                       50
% 2.63/1.01  prop_solver_time:                       0.
% 2.63/1.01  smt_solver_time:                        0.
% 2.63/1.01  smt_fast_solver_time:                   0.
% 2.63/1.01  prop_fast_solver_time:                  0.
% 2.63/1.01  prop_unsat_core_time:                   0.
% 2.63/1.01  
% 2.63/1.01  ------ QBF
% 2.63/1.01  
% 2.63/1.01  qbf_q_res:                              0
% 2.63/1.01  qbf_num_tautologies:                    0
% 2.63/1.01  qbf_prep_cycles:                        0
% 2.63/1.01  
% 2.63/1.01  ------ BMC1
% 2.63/1.01  
% 2.63/1.01  bmc1_current_bound:                     -1
% 2.63/1.01  bmc1_last_solved_bound:                 -1
% 2.63/1.01  bmc1_unsat_core_size:                   -1
% 2.63/1.01  bmc1_unsat_core_parents_size:           -1
% 2.63/1.01  bmc1_merge_next_fun:                    0
% 2.63/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.63/1.01  
% 2.63/1.01  ------ Instantiation
% 2.63/1.01  
% 2.63/1.01  inst_num_of_clauses:                    341
% 2.63/1.01  inst_num_in_passive:                    55
% 2.63/1.01  inst_num_in_active:                     207
% 2.63/1.01  inst_num_in_unprocessed:                79
% 2.63/1.01  inst_num_of_loops:                      260
% 2.63/1.01  inst_num_of_learning_restarts:          0
% 2.63/1.01  inst_num_moves_active_passive:          49
% 2.63/1.01  inst_lit_activity:                      0
% 2.63/1.01  inst_lit_activity_moves:                0
% 2.63/1.01  inst_num_tautologies:                   0
% 2.63/1.01  inst_num_prop_implied:                  0
% 2.63/1.01  inst_num_existing_simplified:           0
% 2.63/1.01  inst_num_eq_res_simplified:             0
% 2.63/1.01  inst_num_child_elim:                    0
% 2.63/1.01  inst_num_of_dismatching_blockings:      62
% 2.63/1.01  inst_num_of_non_proper_insts:           339
% 2.63/1.01  inst_num_of_duplicates:                 0
% 2.63/1.01  inst_inst_num_from_inst_to_res:         0
% 2.63/1.01  inst_dismatching_checking_time:         0.
% 2.63/1.01  
% 2.63/1.01  ------ Resolution
% 2.63/1.01  
% 2.63/1.01  res_num_of_clauses:                     0
% 2.63/1.01  res_num_in_passive:                     0
% 2.63/1.01  res_num_in_active:                      0
% 2.63/1.01  res_num_of_loops:                       143
% 2.63/1.01  res_forward_subset_subsumed:            30
% 2.63/1.01  res_backward_subset_subsumed:           0
% 2.63/1.01  res_forward_subsumed:                   0
% 2.63/1.01  res_backward_subsumed:                  0
% 2.63/1.01  res_forward_subsumption_resolution:     1
% 2.63/1.01  res_backward_subsumption_resolution:    0
% 2.63/1.01  res_clause_to_clause_subsumption:       157
% 2.63/1.01  res_orphan_elimination:                 0
% 2.63/1.01  res_tautology_del:                      35
% 2.63/1.01  res_num_eq_res_simplified:              0
% 2.63/1.01  res_num_sel_changes:                    0
% 2.63/1.01  res_moves_from_active_to_pass:          0
% 2.63/1.01  
% 2.63/1.01  ------ Superposition
% 2.63/1.01  
% 2.63/1.01  sup_time_total:                         0.
% 2.63/1.01  sup_time_generating:                    0.
% 2.63/1.01  sup_time_sim_full:                      0.
% 2.63/1.01  sup_time_sim_immed:                     0.
% 2.63/1.01  
% 2.63/1.01  sup_num_of_clauses:                     46
% 2.63/1.01  sup_num_in_active:                      32
% 2.63/1.01  sup_num_in_passive:                     14
% 2.63/1.01  sup_num_of_loops:                       50
% 2.63/1.01  sup_fw_superposition:                   32
% 2.63/1.01  sup_bw_superposition:                   14
% 2.63/1.01  sup_immediate_simplified:               24
% 2.63/1.01  sup_given_eliminated:                   0
% 2.63/1.01  comparisons_done:                       0
% 2.63/1.01  comparisons_avoided:                    0
% 2.63/1.01  
% 2.63/1.01  ------ Simplifications
% 2.63/1.01  
% 2.63/1.01  
% 2.63/1.01  sim_fw_subset_subsumed:                 3
% 2.63/1.01  sim_bw_subset_subsumed:                 0
% 2.63/1.01  sim_fw_subsumed:                        3
% 2.63/1.01  sim_bw_subsumed:                        0
% 2.63/1.01  sim_fw_subsumption_res:                 2
% 2.63/1.01  sim_bw_subsumption_res:                 0
% 2.63/1.01  sim_tautology_del:                      0
% 2.63/1.01  sim_eq_tautology_del:                   15
% 2.63/1.01  sim_eq_res_simp:                        2
% 2.63/1.01  sim_fw_demodulated:                     0
% 2.63/1.01  sim_bw_demodulated:                     18
% 2.63/1.01  sim_light_normalised:                   25
% 2.63/1.01  sim_joinable_taut:                      0
% 2.63/1.01  sim_joinable_simp:                      0
% 2.63/1.01  sim_ac_normalised:                      0
% 2.63/1.01  sim_smt_subsumption:                    0
% 2.63/1.01  
%------------------------------------------------------------------------------
