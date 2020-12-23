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
% DateTime   : Thu Dec  3 12:17:02 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :  203 (12586 expanded)
%              Number of clauses        :  134 (3370 expanded)
%              Number of leaves         :   18 (3814 expanded)
%              Depth                    :   25
%              Number of atoms          :  692 (93895 expanded)
%              Number of equality atoms :  320 (32040 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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
               => ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                  & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
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
                 => ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                    & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
            | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0)
          | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1) )
        & v2_funct_1(sK2)
        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1)
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0)
              | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1) )
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_struct_0(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
                  | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
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
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) )
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f42,f41,f40])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f73,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f22])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
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

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f47,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k1_xboole_0
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k1_xboole_0
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( k1_relat_1(X0) = k1_xboole_0
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_xboole_0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f46,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f54])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1425,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_20,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_29,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_349,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_350,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_31,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_354,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_31])).

cnf(c_355,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_1448,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1425,c_350,c_355])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1432,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1842,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1448,c_1432])).

cnf(c_25,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1445,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_25,c_350,c_355])).

cnf(c_2791,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1842,c_1445])).

cnf(c_3014,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2791,c_1448])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_21,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_336,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_337,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_339,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_337,c_29])).

cnf(c_361,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_339])).

cnf(c_362,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_5,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_16,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_384,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_5,c_16])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_388,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_384,c_16,c_5,c_4])).

cnf(c_389,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_388])).

cnf(c_428,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_362,c_389])).

cnf(c_1422,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_1558,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1422,c_350])).

cnf(c_2580,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1448,c_1558])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_35,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1424,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1442,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1424,c_350,c_355])).

cnf(c_3626,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) != iProver_top
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2580,c_35,c_1442])).

cnf(c_3627,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3626])).

cnf(c_3634,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3014,c_3627])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_24,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_604,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_605,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_604])).

cnf(c_609,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_605,c_28])).

cnf(c_610,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_609])).

cnf(c_1418,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_610])).

cnf(c_2088,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_1418])).

cnf(c_2171,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2088,c_1448,c_1442])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1426,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2190,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK1)
    | k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2171,c_1426])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_580,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_581,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(unflattening,[status(thm)],[c_580])).

cnf(c_585,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X1,X0)
    | v1_funct_2(k2_funct_1(sK2),X0,X1)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_581,c_28])).

cnf(c_586,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(renaming,[status(thm)],[c_585])).

cnf(c_1419,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(k2_funct_1(sK2),X1,X0) = iProver_top
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_1926,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_1419])).

cnf(c_3379,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2190,c_1448,c_1442,c_1926])).

cnf(c_3380,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK1)
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3379])).

cnf(c_3381,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3380,c_2791])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_532,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_24])).

cnf(c_533,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_532])).

cnf(c_537,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_533,c_28])).

cnf(c_538,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_537])).

cnf(c_1421,plain,
    ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_538])).

cnf(c_1996,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_1421])).

cnf(c_1999,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1996,c_1448,c_1442])).

cnf(c_23,negated_conjecture,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1529,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_23,c_350,c_355])).

cnf(c_2002,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_1999,c_1529])).

cnf(c_3011,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2791,c_2002])).

cnf(c_2177,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2171,c_1432])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_642,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_24])).

cnf(c_643,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_642])).

cnf(c_645,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_643,c_28])).

cnf(c_1416,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_645])).

cnf(c_1633,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1665,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1416,c_28,c_26,c_643,c_1633])).

cnf(c_2179,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2177,c_1665])).

cnf(c_3438,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2179,c_2791])).

cnf(c_3621,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3011,c_3438])).

cnf(c_3624,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3381,c_3621])).

cnf(c_3746,plain,
    ( k2_struct_0(sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3624,c_3634])).

cnf(c_3874,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3634,c_3746])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1435,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1771,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1665,c_1435])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_628,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_24])).

cnf(c_629,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_628])).

cnf(c_631,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_629,c_28])).

cnf(c_1417,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_631])).

cnf(c_1696,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1417,c_28,c_26,c_629,c_1633])).

cnf(c_1772,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1771,c_1696])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1674,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3582,plain,
    ( k1_relat_1(sK2) != k1_xboole_0
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1772,c_26,c_1633,c_1674])).

cnf(c_3583,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3582])).

cnf(c_3876,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3874,c_3583])).

cnf(c_3881,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3876])).

cnf(c_3010,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2791,c_2171])).

cnf(c_3750,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3746,c_3010])).

cnf(c_4410,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3881,c_3750])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1427,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5288,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4410,c_1427])).

cnf(c_3749,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_xboole_0,k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k1_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3746,c_3621])).

cnf(c_1044,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1075,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1044])).

cnf(c_1630,plain,
    ( ~ v1_funct_2(sK2,X0,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | k1_relat_1(sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_428])).

cnf(c_1726,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1630])).

cnf(c_1918,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1726])).

cnf(c_1045,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1759,plain,
    ( k1_relat_1(sK2) != X0
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1045])).

cnf(c_2022,plain,
    ( k1_relat_1(sK2) != u1_struct_0(sK0)
    | k1_relat_1(sK2) = k1_xboole_0
    | k1_xboole_0 != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1759])).

cnf(c_1909,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK0)
    | u1_struct_0(sK0) != X1 ),
    inference(instantiation,[status(thm)],[c_1045])).

cnf(c_2836,plain,
    ( X0 = u1_struct_0(sK0)
    | X0 != k2_struct_0(sK0)
    | u1_struct_0(sK0) != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1909])).

cnf(c_2837,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2836])).

cnf(c_3236,plain,
    ( X0 != X1
    | X0 = k2_struct_0(sK0)
    | k2_struct_0(sK0) != X1 ),
    inference(instantiation,[status(thm)],[c_1045])).

cnf(c_3237,plain,
    ( k2_struct_0(sK0) != k1_xboole_0
    | k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3236])).

cnf(c_4459,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_xboole_0,k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3749,c_28,c_27,c_26,c_355,c_1075,c_1918,c_2022,c_2837,c_3237,c_3624,c_3634])).

cnf(c_4461,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4459,c_3881])).

cnf(c_1929,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1926,c_1448,c_1442])).

cnf(c_3013,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2791,c_1929])).

cnf(c_3753,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3746,c_3013])).

cnf(c_4415,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3881,c_3753])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5288,c_4461,c_4415])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n025.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 10:50:50 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 2.74/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/0.97  
% 2.74/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.74/0.97  
% 2.74/0.97  ------  iProver source info
% 2.74/0.97  
% 2.74/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.74/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.74/0.97  git: non_committed_changes: false
% 2.74/0.97  git: last_make_outside_of_git: false
% 2.74/0.97  
% 2.74/0.97  ------ 
% 2.74/0.97  
% 2.74/0.97  ------ Input Options
% 2.74/0.97  
% 2.74/0.97  --out_options                           all
% 2.74/0.97  --tptp_safe_out                         true
% 2.74/0.97  --problem_path                          ""
% 2.74/0.97  --include_path                          ""
% 2.74/0.97  --clausifier                            res/vclausify_rel
% 2.74/0.97  --clausifier_options                    --mode clausify
% 2.74/0.97  --stdin                                 false
% 2.74/0.97  --stats_out                             all
% 2.74/0.97  
% 2.74/0.97  ------ General Options
% 2.74/0.97  
% 2.74/0.97  --fof                                   false
% 2.74/0.97  --time_out_real                         305.
% 2.74/0.97  --time_out_virtual                      -1.
% 2.74/0.97  --symbol_type_check                     false
% 2.74/0.97  --clausify_out                          false
% 2.74/0.97  --sig_cnt_out                           false
% 2.74/0.97  --trig_cnt_out                          false
% 2.74/0.97  --trig_cnt_out_tolerance                1.
% 2.74/0.97  --trig_cnt_out_sk_spl                   false
% 2.74/0.97  --abstr_cl_out                          false
% 2.74/0.97  
% 2.74/0.97  ------ Global Options
% 2.74/0.97  
% 2.74/0.97  --schedule                              default
% 2.74/0.97  --add_important_lit                     false
% 2.74/0.97  --prop_solver_per_cl                    1000
% 2.74/0.97  --min_unsat_core                        false
% 2.74/0.97  --soft_assumptions                      false
% 2.74/0.97  --soft_lemma_size                       3
% 2.74/0.97  --prop_impl_unit_size                   0
% 2.74/0.97  --prop_impl_unit                        []
% 2.74/0.97  --share_sel_clauses                     true
% 2.74/0.97  --reset_solvers                         false
% 2.74/0.97  --bc_imp_inh                            [conj_cone]
% 2.74/0.97  --conj_cone_tolerance                   3.
% 2.74/0.97  --extra_neg_conj                        none
% 2.74/0.97  --large_theory_mode                     true
% 2.74/0.97  --prolific_symb_bound                   200
% 2.74/0.97  --lt_threshold                          2000
% 2.74/0.97  --clause_weak_htbl                      true
% 2.74/0.97  --gc_record_bc_elim                     false
% 2.74/0.97  
% 2.74/0.97  ------ Preprocessing Options
% 2.74/0.97  
% 2.74/0.97  --preprocessing_flag                    true
% 2.74/0.97  --time_out_prep_mult                    0.1
% 2.74/0.97  --splitting_mode                        input
% 2.74/0.97  --splitting_grd                         true
% 2.74/0.97  --splitting_cvd                         false
% 2.74/0.97  --splitting_cvd_svl                     false
% 2.74/0.97  --splitting_nvd                         32
% 2.74/0.97  --sub_typing                            true
% 2.74/0.97  --prep_gs_sim                           true
% 2.74/0.97  --prep_unflatten                        true
% 2.74/0.97  --prep_res_sim                          true
% 2.74/0.97  --prep_upred                            true
% 2.74/0.97  --prep_sem_filter                       exhaustive
% 2.74/0.97  --prep_sem_filter_out                   false
% 2.74/0.97  --pred_elim                             true
% 2.74/0.97  --res_sim_input                         true
% 2.74/0.97  --eq_ax_congr_red                       true
% 2.74/0.97  --pure_diseq_elim                       true
% 2.74/0.97  --brand_transform                       false
% 2.74/0.97  --non_eq_to_eq                          false
% 2.74/0.97  --prep_def_merge                        true
% 2.74/0.97  --prep_def_merge_prop_impl              false
% 2.74/0.97  --prep_def_merge_mbd                    true
% 2.74/0.97  --prep_def_merge_tr_red                 false
% 2.74/0.97  --prep_def_merge_tr_cl                  false
% 2.74/0.97  --smt_preprocessing                     true
% 2.74/0.97  --smt_ac_axioms                         fast
% 2.74/0.97  --preprocessed_out                      false
% 2.74/0.97  --preprocessed_stats                    false
% 2.74/0.97  
% 2.74/0.97  ------ Abstraction refinement Options
% 2.74/0.97  
% 2.74/0.97  --abstr_ref                             []
% 2.74/0.97  --abstr_ref_prep                        false
% 2.74/0.97  --abstr_ref_until_sat                   false
% 2.74/0.97  --abstr_ref_sig_restrict                funpre
% 2.74/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.74/0.97  --abstr_ref_under                       []
% 2.74/0.97  
% 2.74/0.97  ------ SAT Options
% 2.74/0.97  
% 2.74/0.97  --sat_mode                              false
% 2.74/0.97  --sat_fm_restart_options                ""
% 2.74/0.97  --sat_gr_def                            false
% 2.74/0.97  --sat_epr_types                         true
% 2.74/0.97  --sat_non_cyclic_types                  false
% 2.74/0.97  --sat_finite_models                     false
% 2.74/0.97  --sat_fm_lemmas                         false
% 2.74/0.97  --sat_fm_prep                           false
% 2.74/0.97  --sat_fm_uc_incr                        true
% 2.74/0.97  --sat_out_model                         small
% 2.74/0.97  --sat_out_clauses                       false
% 2.74/0.97  
% 2.74/0.97  ------ QBF Options
% 2.74/0.97  
% 2.74/0.97  --qbf_mode                              false
% 2.74/0.97  --qbf_elim_univ                         false
% 2.74/0.97  --qbf_dom_inst                          none
% 2.74/0.97  --qbf_dom_pre_inst                      false
% 2.74/0.97  --qbf_sk_in                             false
% 2.74/0.97  --qbf_pred_elim                         true
% 2.74/0.97  --qbf_split                             512
% 2.74/0.97  
% 2.74/0.97  ------ BMC1 Options
% 2.74/0.97  
% 2.74/0.97  --bmc1_incremental                      false
% 2.74/0.97  --bmc1_axioms                           reachable_all
% 2.74/0.97  --bmc1_min_bound                        0
% 2.74/0.97  --bmc1_max_bound                        -1
% 2.74/0.97  --bmc1_max_bound_default                -1
% 2.74/0.97  --bmc1_symbol_reachability              true
% 2.74/0.97  --bmc1_property_lemmas                  false
% 2.74/0.97  --bmc1_k_induction                      false
% 2.74/0.97  --bmc1_non_equiv_states                 false
% 2.74/0.97  --bmc1_deadlock                         false
% 2.74/0.97  --bmc1_ucm                              false
% 2.74/0.97  --bmc1_add_unsat_core                   none
% 2.74/0.97  --bmc1_unsat_core_children              false
% 2.74/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.74/0.97  --bmc1_out_stat                         full
% 2.74/0.97  --bmc1_ground_init                      false
% 2.74/0.97  --bmc1_pre_inst_next_state              false
% 2.74/0.97  --bmc1_pre_inst_state                   false
% 2.74/0.97  --bmc1_pre_inst_reach_state             false
% 2.74/0.97  --bmc1_out_unsat_core                   false
% 2.74/0.97  --bmc1_aig_witness_out                  false
% 2.74/0.97  --bmc1_verbose                          false
% 2.74/0.97  --bmc1_dump_clauses_tptp                false
% 2.74/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.74/0.97  --bmc1_dump_file                        -
% 2.74/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.74/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.74/0.97  --bmc1_ucm_extend_mode                  1
% 2.74/0.97  --bmc1_ucm_init_mode                    2
% 2.74/0.97  --bmc1_ucm_cone_mode                    none
% 2.74/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.74/0.97  --bmc1_ucm_relax_model                  4
% 2.74/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.74/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.74/0.97  --bmc1_ucm_layered_model                none
% 2.74/0.97  --bmc1_ucm_max_lemma_size               10
% 2.74/0.97  
% 2.74/0.97  ------ AIG Options
% 2.74/0.97  
% 2.74/0.97  --aig_mode                              false
% 2.74/0.97  
% 2.74/0.97  ------ Instantiation Options
% 2.74/0.97  
% 2.74/0.97  --instantiation_flag                    true
% 2.74/0.97  --inst_sos_flag                         false
% 2.74/0.97  --inst_sos_phase                        true
% 2.74/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.74/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.74/0.97  --inst_lit_sel_side                     num_symb
% 2.74/0.97  --inst_solver_per_active                1400
% 2.74/0.97  --inst_solver_calls_frac                1.
% 2.74/0.97  --inst_passive_queue_type               priority_queues
% 2.74/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.74/0.97  --inst_passive_queues_freq              [25;2]
% 2.74/0.97  --inst_dismatching                      true
% 2.74/0.97  --inst_eager_unprocessed_to_passive     true
% 2.74/0.97  --inst_prop_sim_given                   true
% 2.74/0.97  --inst_prop_sim_new                     false
% 2.74/0.97  --inst_subs_new                         false
% 2.74/0.97  --inst_eq_res_simp                      false
% 2.74/0.97  --inst_subs_given                       false
% 2.74/0.97  --inst_orphan_elimination               true
% 2.74/0.97  --inst_learning_loop_flag               true
% 2.74/0.97  --inst_learning_start                   3000
% 2.74/0.97  --inst_learning_factor                  2
% 2.74/0.97  --inst_start_prop_sim_after_learn       3
% 2.74/0.97  --inst_sel_renew                        solver
% 2.74/0.97  --inst_lit_activity_flag                true
% 2.74/0.97  --inst_restr_to_given                   false
% 2.74/0.97  --inst_activity_threshold               500
% 2.74/0.97  --inst_out_proof                        true
% 2.74/0.97  
% 2.74/0.97  ------ Resolution Options
% 2.74/0.97  
% 2.74/0.97  --resolution_flag                       true
% 2.74/0.97  --res_lit_sel                           adaptive
% 2.74/0.97  --res_lit_sel_side                      none
% 2.74/0.97  --res_ordering                          kbo
% 2.74/0.97  --res_to_prop_solver                    active
% 2.74/0.97  --res_prop_simpl_new                    false
% 2.74/0.97  --res_prop_simpl_given                  true
% 2.74/0.97  --res_passive_queue_type                priority_queues
% 2.74/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.74/0.97  --res_passive_queues_freq               [15;5]
% 2.74/0.97  --res_forward_subs                      full
% 2.74/0.97  --res_backward_subs                     full
% 2.74/0.97  --res_forward_subs_resolution           true
% 2.74/0.97  --res_backward_subs_resolution          true
% 2.74/0.97  --res_orphan_elimination                true
% 2.74/0.97  --res_time_limit                        2.
% 2.74/0.97  --res_out_proof                         true
% 2.74/0.97  
% 2.74/0.97  ------ Superposition Options
% 2.74/0.97  
% 2.74/0.97  --superposition_flag                    true
% 2.74/0.97  --sup_passive_queue_type                priority_queues
% 2.74/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.74/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.74/0.97  --demod_completeness_check              fast
% 2.74/0.97  --demod_use_ground                      true
% 2.74/0.97  --sup_to_prop_solver                    passive
% 2.74/0.97  --sup_prop_simpl_new                    true
% 2.74/0.97  --sup_prop_simpl_given                  true
% 2.74/0.97  --sup_fun_splitting                     false
% 2.74/0.97  --sup_smt_interval                      50000
% 2.74/0.97  
% 2.74/0.97  ------ Superposition Simplification Setup
% 2.74/0.97  
% 2.74/0.97  --sup_indices_passive                   []
% 2.74/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.74/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.97  --sup_full_bw                           [BwDemod]
% 2.74/0.97  --sup_immed_triv                        [TrivRules]
% 2.74/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.74/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.97  --sup_immed_bw_main                     []
% 2.74/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.74/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.97  
% 2.74/0.97  ------ Combination Options
% 2.74/0.97  
% 2.74/0.97  --comb_res_mult                         3
% 2.74/0.97  --comb_sup_mult                         2
% 2.74/0.97  --comb_inst_mult                        10
% 2.74/0.97  
% 2.74/0.97  ------ Debug Options
% 2.74/0.97  
% 2.74/0.97  --dbg_backtrace                         false
% 2.74/0.97  --dbg_dump_prop_clauses                 false
% 2.74/0.97  --dbg_dump_prop_clauses_file            -
% 2.74/0.97  --dbg_out_stat                          false
% 2.74/0.97  ------ Parsing...
% 2.74/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.74/0.97  
% 2.74/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.74/0.97  
% 2.74/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.74/0.97  
% 2.74/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.74/0.97  ------ Proving...
% 2.74/0.97  ------ Problem Properties 
% 2.74/0.97  
% 2.74/0.97  
% 2.74/0.97  clauses                                 24
% 2.74/0.97  conjectures                             5
% 2.74/0.97  EPR                                     1
% 2.74/0.97  Horn                                    20
% 2.74/0.97  unary                                   6
% 2.74/0.97  binary                                  5
% 2.74/0.97  lits                                    64
% 2.74/0.97  lits eq                                 27
% 2.74/0.97  fd_pure                                 0
% 2.74/0.97  fd_pseudo                               0
% 2.74/0.97  fd_cond                                 3
% 2.74/0.97  fd_pseudo_cond                          1
% 2.74/0.97  AC symbols                              0
% 2.74/0.97  
% 2.74/0.97  ------ Schedule dynamic 5 is on 
% 2.74/0.97  
% 2.74/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.74/0.97  
% 2.74/0.97  
% 2.74/0.97  ------ 
% 2.74/0.97  Current options:
% 2.74/0.97  ------ 
% 2.74/0.97  
% 2.74/0.97  ------ Input Options
% 2.74/0.97  
% 2.74/0.97  --out_options                           all
% 2.74/0.97  --tptp_safe_out                         true
% 2.74/0.97  --problem_path                          ""
% 2.74/0.97  --include_path                          ""
% 2.74/0.97  --clausifier                            res/vclausify_rel
% 2.74/0.97  --clausifier_options                    --mode clausify
% 2.74/0.97  --stdin                                 false
% 2.74/0.97  --stats_out                             all
% 2.74/0.97  
% 2.74/0.97  ------ General Options
% 2.74/0.97  
% 2.74/0.97  --fof                                   false
% 2.74/0.97  --time_out_real                         305.
% 2.74/0.97  --time_out_virtual                      -1.
% 2.74/0.97  --symbol_type_check                     false
% 2.74/0.97  --clausify_out                          false
% 2.74/0.97  --sig_cnt_out                           false
% 2.74/0.97  --trig_cnt_out                          false
% 2.74/0.97  --trig_cnt_out_tolerance                1.
% 2.74/0.97  --trig_cnt_out_sk_spl                   false
% 2.74/0.97  --abstr_cl_out                          false
% 2.74/0.97  
% 2.74/0.97  ------ Global Options
% 2.74/0.97  
% 2.74/0.97  --schedule                              default
% 2.74/0.97  --add_important_lit                     false
% 2.74/0.97  --prop_solver_per_cl                    1000
% 2.74/0.97  --min_unsat_core                        false
% 2.74/0.97  --soft_assumptions                      false
% 2.74/0.97  --soft_lemma_size                       3
% 2.74/0.97  --prop_impl_unit_size                   0
% 2.74/0.97  --prop_impl_unit                        []
% 2.74/0.97  --share_sel_clauses                     true
% 2.74/0.97  --reset_solvers                         false
% 2.74/0.97  --bc_imp_inh                            [conj_cone]
% 2.74/0.97  --conj_cone_tolerance                   3.
% 2.74/0.97  --extra_neg_conj                        none
% 2.74/0.97  --large_theory_mode                     true
% 2.74/0.97  --prolific_symb_bound                   200
% 2.74/0.97  --lt_threshold                          2000
% 2.74/0.97  --clause_weak_htbl                      true
% 2.74/0.97  --gc_record_bc_elim                     false
% 2.74/0.97  
% 2.74/0.97  ------ Preprocessing Options
% 2.74/0.97  
% 2.74/0.97  --preprocessing_flag                    true
% 2.74/0.97  --time_out_prep_mult                    0.1
% 2.74/0.97  --splitting_mode                        input
% 2.74/0.97  --splitting_grd                         true
% 2.74/0.97  --splitting_cvd                         false
% 2.74/0.97  --splitting_cvd_svl                     false
% 2.74/0.97  --splitting_nvd                         32
% 2.74/0.97  --sub_typing                            true
% 2.74/0.97  --prep_gs_sim                           true
% 2.74/0.97  --prep_unflatten                        true
% 2.74/0.97  --prep_res_sim                          true
% 2.74/0.97  --prep_upred                            true
% 2.74/0.97  --prep_sem_filter                       exhaustive
% 2.74/0.97  --prep_sem_filter_out                   false
% 2.74/0.97  --pred_elim                             true
% 2.74/0.97  --res_sim_input                         true
% 2.74/0.97  --eq_ax_congr_red                       true
% 2.74/0.97  --pure_diseq_elim                       true
% 2.74/0.97  --brand_transform                       false
% 2.74/0.97  --non_eq_to_eq                          false
% 2.74/0.97  --prep_def_merge                        true
% 2.74/0.97  --prep_def_merge_prop_impl              false
% 2.74/0.97  --prep_def_merge_mbd                    true
% 2.74/0.97  --prep_def_merge_tr_red                 false
% 2.74/0.97  --prep_def_merge_tr_cl                  false
% 2.74/0.97  --smt_preprocessing                     true
% 2.74/0.97  --smt_ac_axioms                         fast
% 2.74/0.97  --preprocessed_out                      false
% 2.74/0.97  --preprocessed_stats                    false
% 2.74/0.97  
% 2.74/0.97  ------ Abstraction refinement Options
% 2.74/0.97  
% 2.74/0.97  --abstr_ref                             []
% 2.74/0.97  --abstr_ref_prep                        false
% 2.74/0.97  --abstr_ref_until_sat                   false
% 2.74/0.97  --abstr_ref_sig_restrict                funpre
% 2.74/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.74/0.97  --abstr_ref_under                       []
% 2.74/0.97  
% 2.74/0.97  ------ SAT Options
% 2.74/0.97  
% 2.74/0.97  --sat_mode                              false
% 2.74/0.97  --sat_fm_restart_options                ""
% 2.74/0.97  --sat_gr_def                            false
% 2.74/0.97  --sat_epr_types                         true
% 2.74/0.97  --sat_non_cyclic_types                  false
% 2.74/0.97  --sat_finite_models                     false
% 2.74/0.97  --sat_fm_lemmas                         false
% 2.74/0.97  --sat_fm_prep                           false
% 2.74/0.97  --sat_fm_uc_incr                        true
% 2.74/0.97  --sat_out_model                         small
% 2.74/0.97  --sat_out_clauses                       false
% 2.74/0.97  
% 2.74/0.97  ------ QBF Options
% 2.74/0.97  
% 2.74/0.97  --qbf_mode                              false
% 2.74/0.97  --qbf_elim_univ                         false
% 2.74/0.97  --qbf_dom_inst                          none
% 2.74/0.97  --qbf_dom_pre_inst                      false
% 2.74/0.97  --qbf_sk_in                             false
% 2.74/0.97  --qbf_pred_elim                         true
% 2.74/0.97  --qbf_split                             512
% 2.74/0.97  
% 2.74/0.97  ------ BMC1 Options
% 2.74/0.97  
% 2.74/0.97  --bmc1_incremental                      false
% 2.74/0.97  --bmc1_axioms                           reachable_all
% 2.74/0.97  --bmc1_min_bound                        0
% 2.74/0.97  --bmc1_max_bound                        -1
% 2.74/0.97  --bmc1_max_bound_default                -1
% 2.74/0.97  --bmc1_symbol_reachability              true
% 2.74/0.97  --bmc1_property_lemmas                  false
% 2.74/0.97  --bmc1_k_induction                      false
% 2.74/0.97  --bmc1_non_equiv_states                 false
% 2.74/0.97  --bmc1_deadlock                         false
% 2.74/0.97  --bmc1_ucm                              false
% 2.74/0.97  --bmc1_add_unsat_core                   none
% 2.74/0.97  --bmc1_unsat_core_children              false
% 2.74/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.74/0.97  --bmc1_out_stat                         full
% 2.74/0.97  --bmc1_ground_init                      false
% 2.74/0.97  --bmc1_pre_inst_next_state              false
% 2.74/0.97  --bmc1_pre_inst_state                   false
% 2.74/0.97  --bmc1_pre_inst_reach_state             false
% 2.74/0.97  --bmc1_out_unsat_core                   false
% 2.74/0.97  --bmc1_aig_witness_out                  false
% 2.74/0.97  --bmc1_verbose                          false
% 2.74/0.97  --bmc1_dump_clauses_tptp                false
% 2.74/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.74/0.97  --bmc1_dump_file                        -
% 2.74/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.74/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.74/0.97  --bmc1_ucm_extend_mode                  1
% 2.74/0.97  --bmc1_ucm_init_mode                    2
% 2.74/0.97  --bmc1_ucm_cone_mode                    none
% 2.74/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.74/0.97  --bmc1_ucm_relax_model                  4
% 2.74/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.74/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.74/0.97  --bmc1_ucm_layered_model                none
% 2.74/0.97  --bmc1_ucm_max_lemma_size               10
% 2.74/0.97  
% 2.74/0.97  ------ AIG Options
% 2.74/0.97  
% 2.74/0.97  --aig_mode                              false
% 2.74/0.97  
% 2.74/0.97  ------ Instantiation Options
% 2.74/0.97  
% 2.74/0.97  --instantiation_flag                    true
% 2.74/0.97  --inst_sos_flag                         false
% 2.74/0.97  --inst_sos_phase                        true
% 2.74/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.74/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.74/0.97  --inst_lit_sel_side                     none
% 2.74/0.97  --inst_solver_per_active                1400
% 2.74/0.97  --inst_solver_calls_frac                1.
% 2.74/0.97  --inst_passive_queue_type               priority_queues
% 2.74/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.74/0.97  --inst_passive_queues_freq              [25;2]
% 2.74/0.97  --inst_dismatching                      true
% 2.74/0.97  --inst_eager_unprocessed_to_passive     true
% 2.74/0.97  --inst_prop_sim_given                   true
% 2.74/0.97  --inst_prop_sim_new                     false
% 2.74/0.97  --inst_subs_new                         false
% 2.74/0.97  --inst_eq_res_simp                      false
% 2.74/0.97  --inst_subs_given                       false
% 2.74/0.97  --inst_orphan_elimination               true
% 2.74/0.97  --inst_learning_loop_flag               true
% 2.74/0.97  --inst_learning_start                   3000
% 2.74/0.97  --inst_learning_factor                  2
% 2.74/0.97  --inst_start_prop_sim_after_learn       3
% 2.74/0.97  --inst_sel_renew                        solver
% 2.74/0.97  --inst_lit_activity_flag                true
% 2.74/0.97  --inst_restr_to_given                   false
% 2.74/0.97  --inst_activity_threshold               500
% 2.74/0.97  --inst_out_proof                        true
% 2.74/0.97  
% 2.74/0.97  ------ Resolution Options
% 2.74/0.97  
% 2.74/0.97  --resolution_flag                       false
% 2.74/0.97  --res_lit_sel                           adaptive
% 2.74/0.97  --res_lit_sel_side                      none
% 2.74/0.97  --res_ordering                          kbo
% 2.74/0.97  --res_to_prop_solver                    active
% 2.74/0.97  --res_prop_simpl_new                    false
% 2.74/0.97  --res_prop_simpl_given                  true
% 2.74/0.97  --res_passive_queue_type                priority_queues
% 2.74/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.74/0.97  --res_passive_queues_freq               [15;5]
% 2.74/0.97  --res_forward_subs                      full
% 2.74/0.97  --res_backward_subs                     full
% 2.74/0.97  --res_forward_subs_resolution           true
% 2.74/0.97  --res_backward_subs_resolution          true
% 2.74/0.97  --res_orphan_elimination                true
% 2.74/0.97  --res_time_limit                        2.
% 2.74/0.97  --res_out_proof                         true
% 2.74/0.97  
% 2.74/0.97  ------ Superposition Options
% 2.74/0.97  
% 2.74/0.97  --superposition_flag                    true
% 2.74/0.97  --sup_passive_queue_type                priority_queues
% 2.74/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.74/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.74/0.97  --demod_completeness_check              fast
% 2.74/0.97  --demod_use_ground                      true
% 2.74/0.97  --sup_to_prop_solver                    passive
% 2.74/0.97  --sup_prop_simpl_new                    true
% 2.74/0.97  --sup_prop_simpl_given                  true
% 2.74/0.97  --sup_fun_splitting                     false
% 2.74/0.97  --sup_smt_interval                      50000
% 2.74/0.97  
% 2.74/0.97  ------ Superposition Simplification Setup
% 2.74/0.97  
% 2.74/0.97  --sup_indices_passive                   []
% 2.74/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.74/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.97  --sup_full_bw                           [BwDemod]
% 2.74/0.97  --sup_immed_triv                        [TrivRules]
% 2.74/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.74/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.97  --sup_immed_bw_main                     []
% 2.74/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.74/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.97  
% 2.74/0.97  ------ Combination Options
% 2.74/0.97  
% 2.74/0.97  --comb_res_mult                         3
% 2.74/0.97  --comb_sup_mult                         2
% 2.74/0.97  --comb_inst_mult                        10
% 2.74/0.97  
% 2.74/0.97  ------ Debug Options
% 2.74/0.97  
% 2.74/0.97  --dbg_backtrace                         false
% 2.74/0.97  --dbg_dump_prop_clauses                 false
% 2.74/0.97  --dbg_dump_prop_clauses_file            -
% 2.74/0.97  --dbg_out_stat                          false
% 2.74/0.97  
% 2.74/0.97  
% 2.74/0.97  
% 2.74/0.97  
% 2.74/0.97  ------ Proving...
% 2.74/0.97  
% 2.74/0.97  
% 2.74/0.97  % SZS status Theorem for theBenchmark.p
% 2.74/0.97  
% 2.74/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.74/0.97  
% 2.74/0.97  fof(f13,conjecture,(
% 2.74/0.97    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.74/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.97  
% 2.74/0.97  fof(f14,negated_conjecture,(
% 2.74/0.97    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.74/0.97    inference(negated_conjecture,[],[f13])).
% 2.74/0.97  
% 2.74/0.97  fof(f35,plain,(
% 2.74/0.97    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.74/0.97    inference(ennf_transformation,[],[f14])).
% 2.74/0.97  
% 2.74/0.97  fof(f36,plain,(
% 2.74/0.97    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.74/0.97    inference(flattening,[],[f35])).
% 2.74/0.97  
% 2.74/0.97  fof(f42,plain,(
% 2.74/0.97    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.74/0.97    introduced(choice_axiom,[])).
% 2.74/0.97  
% 2.74/0.97  fof(f41,plain,(
% 2.74/0.97    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.74/0.97    introduced(choice_axiom,[])).
% 2.74/0.97  
% 2.74/0.97  fof(f40,plain,(
% 2.74/0.97    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.74/0.97    introduced(choice_axiom,[])).
% 2.74/0.97  
% 2.74/0.97  fof(f43,plain,(
% 2.74/0.97    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.74/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f42,f41,f40])).
% 2.74/0.97  
% 2.74/0.97  fof(f72,plain,(
% 2.74/0.97    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.74/0.97    inference(cnf_transformation,[],[f43])).
% 2.74/0.97  
% 2.74/0.97  fof(f10,axiom,(
% 2.74/0.97    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.74/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.97  
% 2.74/0.97  fof(f30,plain,(
% 2.74/0.97    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.74/0.97    inference(ennf_transformation,[],[f10])).
% 2.74/0.97  
% 2.74/0.97  fof(f64,plain,(
% 2.74/0.97    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.74/0.97    inference(cnf_transformation,[],[f30])).
% 2.74/0.97  
% 2.74/0.97  fof(f69,plain,(
% 2.74/0.97    l1_struct_0(sK1)),
% 2.74/0.97    inference(cnf_transformation,[],[f43])).
% 2.74/0.97  
% 2.74/0.97  fof(f67,plain,(
% 2.74/0.97    l1_struct_0(sK0)),
% 2.74/0.97    inference(cnf_transformation,[],[f43])).
% 2.74/0.97  
% 2.74/0.97  fof(f5,axiom,(
% 2.74/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.74/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.97  
% 2.74/0.97  fof(f21,plain,(
% 2.74/0.97    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/0.97    inference(ennf_transformation,[],[f5])).
% 2.74/0.97  
% 2.74/0.97  fof(f50,plain,(
% 2.74/0.97    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/0.97    inference(cnf_transformation,[],[f21])).
% 2.74/0.97  
% 2.74/0.97  fof(f73,plain,(
% 2.74/0.97    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.74/0.97    inference(cnf_transformation,[],[f43])).
% 2.74/0.97  
% 2.74/0.97  fof(f6,axiom,(
% 2.74/0.97    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.74/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.97  
% 2.74/0.97  fof(f22,plain,(
% 2.74/0.97    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.74/0.97    inference(ennf_transformation,[],[f6])).
% 2.74/0.97  
% 2.74/0.97  fof(f23,plain,(
% 2.74/0.97    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.74/0.97    inference(flattening,[],[f22])).
% 2.74/0.97  
% 2.74/0.97  fof(f52,plain,(
% 2.74/0.97    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.74/0.97    inference(cnf_transformation,[],[f23])).
% 2.74/0.97  
% 2.74/0.97  fof(f11,axiom,(
% 2.74/0.97    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.74/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.97  
% 2.74/0.97  fof(f31,plain,(
% 2.74/0.97    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.74/0.97    inference(ennf_transformation,[],[f11])).
% 2.74/0.97  
% 2.74/0.97  fof(f32,plain,(
% 2.74/0.97    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.74/0.97    inference(flattening,[],[f31])).
% 2.74/0.97  
% 2.74/0.97  fof(f65,plain,(
% 2.74/0.97    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.74/0.97    inference(cnf_transformation,[],[f32])).
% 2.74/0.97  
% 2.74/0.97  fof(f68,plain,(
% 2.74/0.97    ~v2_struct_0(sK1)),
% 2.74/0.97    inference(cnf_transformation,[],[f43])).
% 2.74/0.97  
% 2.74/0.97  fof(f4,axiom,(
% 2.74/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.74/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.97  
% 2.74/0.97  fof(f15,plain,(
% 2.74/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.74/0.97    inference(pure_predicate_removal,[],[f4])).
% 2.74/0.97  
% 2.74/0.97  fof(f20,plain,(
% 2.74/0.97    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/0.97    inference(ennf_transformation,[],[f15])).
% 2.74/0.97  
% 2.74/0.97  fof(f49,plain,(
% 2.74/0.97    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/0.97    inference(cnf_transformation,[],[f20])).
% 2.74/0.97  
% 2.74/0.97  fof(f8,axiom,(
% 2.74/0.97    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.74/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.97  
% 2.74/0.97  fof(f26,plain,(
% 2.74/0.97    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.74/0.97    inference(ennf_transformation,[],[f8])).
% 2.74/0.97  
% 2.74/0.97  fof(f27,plain,(
% 2.74/0.97    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.74/0.97    inference(flattening,[],[f26])).
% 2.74/0.97  
% 2.74/0.97  fof(f39,plain,(
% 2.74/0.97    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.74/0.97    inference(nnf_transformation,[],[f27])).
% 2.74/0.97  
% 2.74/0.97  fof(f59,plain,(
% 2.74/0.97    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.74/0.97    inference(cnf_transformation,[],[f39])).
% 2.74/0.97  
% 2.74/0.97  fof(f3,axiom,(
% 2.74/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.74/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.97  
% 2.74/0.97  fof(f19,plain,(
% 2.74/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/0.97    inference(ennf_transformation,[],[f3])).
% 2.74/0.97  
% 2.74/0.97  fof(f48,plain,(
% 2.74/0.97    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/0.97    inference(cnf_transformation,[],[f19])).
% 2.74/0.97  
% 2.74/0.97  fof(f70,plain,(
% 2.74/0.97    v1_funct_1(sK2)),
% 2.74/0.97    inference(cnf_transformation,[],[f43])).
% 2.74/0.97  
% 2.74/0.97  fof(f71,plain,(
% 2.74/0.97    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.74/0.97    inference(cnf_transformation,[],[f43])).
% 2.74/0.97  
% 2.74/0.97  fof(f9,axiom,(
% 2.74/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.74/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.97  
% 2.74/0.97  fof(f28,plain,(
% 2.74/0.97    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.74/0.97    inference(ennf_transformation,[],[f9])).
% 2.74/0.97  
% 2.74/0.97  fof(f29,plain,(
% 2.74/0.97    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.74/0.97    inference(flattening,[],[f28])).
% 2.74/0.97  
% 2.74/0.97  fof(f63,plain,(
% 2.74/0.97    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.74/0.97    inference(cnf_transformation,[],[f29])).
% 2.74/0.97  
% 2.74/0.97  fof(f74,plain,(
% 2.74/0.97    v2_funct_1(sK2)),
% 2.74/0.97    inference(cnf_transformation,[],[f43])).
% 2.74/0.97  
% 2.74/0.97  fof(f7,axiom,(
% 2.74/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.74/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.97  
% 2.74/0.97  fof(f24,plain,(
% 2.74/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/0.97    inference(ennf_transformation,[],[f7])).
% 2.74/0.97  
% 2.74/0.97  fof(f25,plain,(
% 2.74/0.97    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/0.97    inference(flattening,[],[f24])).
% 2.74/0.97  
% 2.74/0.97  fof(f38,plain,(
% 2.74/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.74/0.97    inference(nnf_transformation,[],[f25])).
% 2.74/0.97  
% 2.74/0.97  fof(f53,plain,(
% 2.74/0.97    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/0.97    inference(cnf_transformation,[],[f38])).
% 2.74/0.97  
% 2.74/0.97  fof(f62,plain,(
% 2.74/0.97    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.74/0.97    inference(cnf_transformation,[],[f29])).
% 2.74/0.97  
% 2.74/0.97  fof(f12,axiom,(
% 2.74/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.74/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.97  
% 2.74/0.97  fof(f33,plain,(
% 2.74/0.97    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.74/0.97    inference(ennf_transformation,[],[f12])).
% 2.74/0.97  
% 2.74/0.97  fof(f34,plain,(
% 2.74/0.97    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.74/0.97    inference(flattening,[],[f33])).
% 2.74/0.97  
% 2.74/0.97  fof(f66,plain,(
% 2.74/0.97    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.74/0.97    inference(cnf_transformation,[],[f34])).
% 2.74/0.97  
% 2.74/0.97  fof(f75,plain,(
% 2.74/0.97    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 2.74/0.97    inference(cnf_transformation,[],[f43])).
% 2.74/0.97  
% 2.74/0.97  fof(f2,axiom,(
% 2.74/0.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 2.74/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.97  
% 2.74/0.97  fof(f17,plain,(
% 2.74/0.97    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.74/0.97    inference(ennf_transformation,[],[f2])).
% 2.74/0.97  
% 2.74/0.97  fof(f18,plain,(
% 2.74/0.97    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.74/0.97    inference(flattening,[],[f17])).
% 2.74/0.97  
% 2.74/0.97  fof(f47,plain,(
% 2.74/0.97    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.74/0.97    inference(cnf_transformation,[],[f18])).
% 2.74/0.97  
% 2.74/0.97  fof(f1,axiom,(
% 2.74/0.97    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k1_xboole_0 <=> k1_xboole_0 = k2_relat_1(X0)))),
% 2.74/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/0.97  
% 2.74/0.97  fof(f16,plain,(
% 2.74/0.97    ! [X0] : ((k1_relat_1(X0) = k1_xboole_0 <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.74/0.97    inference(ennf_transformation,[],[f1])).
% 2.74/0.97  
% 2.74/0.97  fof(f37,plain,(
% 2.74/0.97    ! [X0] : (((k1_relat_1(X0) = k1_xboole_0 | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 2.74/0.97    inference(nnf_transformation,[],[f16])).
% 2.74/0.97  
% 2.74/0.97  fof(f45,plain,(
% 2.74/0.97    ( ! [X0] : (k1_relat_1(X0) = k1_xboole_0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.74/0.97    inference(cnf_transformation,[],[f37])).
% 2.74/0.97  
% 2.74/0.97  fof(f46,plain,(
% 2.74/0.97    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.74/0.97    inference(cnf_transformation,[],[f18])).
% 2.74/0.97  
% 2.74/0.97  fof(f44,plain,(
% 2.74/0.97    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0)) )),
% 2.74/0.97    inference(cnf_transformation,[],[f37])).
% 2.74/0.97  
% 2.74/0.97  fof(f54,plain,(
% 2.74/0.97    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.74/0.97    inference(cnf_transformation,[],[f38])).
% 2.74/0.97  
% 2.74/0.97  fof(f80,plain,(
% 2.74/0.97    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.74/0.97    inference(equality_resolution,[],[f54])).
% 2.74/0.97  
% 2.74/0.97  cnf(c_26,negated_conjecture,
% 2.74/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.74/0.97      inference(cnf_transformation,[],[f72]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1425,plain,
% 2.74/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.74/0.97      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_20,plain,
% 2.74/0.97      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.74/0.97      inference(cnf_transformation,[],[f64]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_29,negated_conjecture,
% 2.74/0.97      ( l1_struct_0(sK1) ),
% 2.74/0.97      inference(cnf_transformation,[],[f69]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_349,plain,
% 2.74/0.97      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.74/0.97      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_350,plain,
% 2.74/0.97      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.74/0.97      inference(unflattening,[status(thm)],[c_349]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_31,negated_conjecture,
% 2.74/0.97      ( l1_struct_0(sK0) ),
% 2.74/0.97      inference(cnf_transformation,[],[f67]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_354,plain,
% 2.74/0.97      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.74/0.97      inference(resolution_lifted,[status(thm)],[c_20,c_31]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_355,plain,
% 2.74/0.97      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.74/0.97      inference(unflattening,[status(thm)],[c_354]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1448,plain,
% 2.74/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.74/0.97      inference(light_normalisation,[status(thm)],[c_1425,c_350,c_355]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_6,plain,
% 2.74/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.97      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.74/0.97      inference(cnf_transformation,[],[f50]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1432,plain,
% 2.74/0.97      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.74/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.74/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1842,plain,
% 2.74/0.97      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.74/0.97      inference(superposition,[status(thm)],[c_1448,c_1432]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_25,negated_conjecture,
% 2.74/0.97      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.74/0.97      inference(cnf_transformation,[],[f73]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1445,plain,
% 2.74/0.97      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.74/0.97      inference(light_normalisation,[status(thm)],[c_25,c_350,c_355]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_2791,plain,
% 2.74/0.97      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.74/0.97      inference(demodulation,[status(thm)],[c_1842,c_1445]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_3014,plain,
% 2.74/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.74/0.97      inference(demodulation,[status(thm)],[c_2791,c_1448]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_7,plain,
% 2.74/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 2.74/0.97      | v1_partfun1(X0,X1)
% 2.74/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.97      | v1_xboole_0(X2)
% 2.74/0.97      | ~ v1_funct_1(X0) ),
% 2.74/0.97      inference(cnf_transformation,[],[f52]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_21,plain,
% 2.74/0.97      ( v2_struct_0(X0)
% 2.74/0.97      | ~ l1_struct_0(X0)
% 2.74/0.97      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.74/0.97      inference(cnf_transformation,[],[f65]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_30,negated_conjecture,
% 2.74/0.97      ( ~ v2_struct_0(sK1) ),
% 2.74/0.97      inference(cnf_transformation,[],[f68]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_336,plain,
% 2.74/0.97      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 2.74/0.97      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_337,plain,
% 2.74/0.97      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.74/0.97      inference(unflattening,[status(thm)],[c_336]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_339,plain,
% 2.74/0.97      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.74/0.97      inference(global_propositional_subsumption,
% 2.74/0.97                [status(thm)],
% 2.74/0.97                [c_337,c_29]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_361,plain,
% 2.74/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 2.74/0.97      | v1_partfun1(X0,X1)
% 2.74/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.97      | ~ v1_funct_1(X0)
% 2.74/0.97      | u1_struct_0(sK1) != X2 ),
% 2.74/0.97      inference(resolution_lifted,[status(thm)],[c_7,c_339]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_362,plain,
% 2.74/0.97      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.74/0.97      | v1_partfun1(X0,X1)
% 2.74/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.74/0.97      | ~ v1_funct_1(X0) ),
% 2.74/0.97      inference(unflattening,[status(thm)],[c_361]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_5,plain,
% 2.74/0.97      ( v4_relat_1(X0,X1)
% 2.74/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.74/0.97      inference(cnf_transformation,[],[f49]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_16,plain,
% 2.74/0.97      ( ~ v1_partfun1(X0,X1)
% 2.74/0.97      | ~ v4_relat_1(X0,X1)
% 2.74/0.97      | ~ v1_relat_1(X0)
% 2.74/0.97      | k1_relat_1(X0) = X1 ),
% 2.74/0.97      inference(cnf_transformation,[],[f59]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_384,plain,
% 2.74/0.97      ( ~ v1_partfun1(X0,X1)
% 2.74/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.97      | ~ v1_relat_1(X0)
% 2.74/0.97      | k1_relat_1(X0) = X1 ),
% 2.74/0.97      inference(resolution,[status(thm)],[c_5,c_16]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_4,plain,
% 2.74/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.97      | v1_relat_1(X0) ),
% 2.74/0.97      inference(cnf_transformation,[],[f48]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_388,plain,
% 2.74/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.97      | ~ v1_partfun1(X0,X1)
% 2.74/0.97      | k1_relat_1(X0) = X1 ),
% 2.74/0.97      inference(global_propositional_subsumption,
% 2.74/0.97                [status(thm)],
% 2.74/0.97                [c_384,c_16,c_5,c_4]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_389,plain,
% 2.74/0.97      ( ~ v1_partfun1(X0,X1)
% 2.74/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.97      | k1_relat_1(X0) = X1 ),
% 2.74/0.97      inference(renaming,[status(thm)],[c_388]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_428,plain,
% 2.74/0.97      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.74/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.74/0.97      | ~ v1_funct_1(X0)
% 2.74/0.97      | k1_relat_1(X0) = X1 ),
% 2.74/0.97      inference(resolution,[status(thm)],[c_362,c_389]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1422,plain,
% 2.74/0.97      ( k1_relat_1(X0) = X1
% 2.74/0.97      | v1_funct_2(X0,X1,u1_struct_0(sK1)) != iProver_top
% 2.74/0.97      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.74/0.97      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1)))) != iProver_top
% 2.74/0.97      | v1_funct_1(X0) != iProver_top ),
% 2.74/0.97      inference(predicate_to_equality,[status(thm)],[c_428]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1558,plain,
% 2.74/0.97      ( k1_relat_1(X0) = X1
% 2.74/0.97      | v1_funct_2(X0,X1,k2_struct_0(sK1)) != iProver_top
% 2.74/0.97      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.74/0.97      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1)))) != iProver_top
% 2.74/0.97      | v1_funct_1(X0) != iProver_top ),
% 2.74/0.97      inference(light_normalisation,[status(thm)],[c_1422,c_350]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_2580,plain,
% 2.74/0.97      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.74/0.97      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.74/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) != iProver_top
% 2.74/0.97      | v1_funct_1(sK2) != iProver_top ),
% 2.74/0.97      inference(superposition,[status(thm)],[c_1448,c_1558]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_28,negated_conjecture,
% 2.74/0.97      ( v1_funct_1(sK2) ),
% 2.74/0.97      inference(cnf_transformation,[],[f70]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_35,plain,
% 2.74/0.97      ( v1_funct_1(sK2) = iProver_top ),
% 2.74/0.97      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_27,negated_conjecture,
% 2.74/0.97      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.74/0.97      inference(cnf_transformation,[],[f71]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1424,plain,
% 2.74/0.97      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.74/0.97      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1442,plain,
% 2.74/0.97      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.74/0.97      inference(light_normalisation,[status(thm)],[c_1424,c_350,c_355]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_3626,plain,
% 2.74/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) != iProver_top
% 2.74/0.97      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.74/0.97      inference(global_propositional_subsumption,
% 2.74/0.97                [status(thm)],
% 2.74/0.97                [c_2580,c_35,c_1442]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_3627,plain,
% 2.74/0.97      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.74/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) != iProver_top ),
% 2.74/0.97      inference(renaming,[status(thm)],[c_3626]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_3634,plain,
% 2.74/0.97      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.74/0.97      inference(superposition,[status(thm)],[c_3014,c_3627]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_17,plain,
% 2.74/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 2.74/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.97      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.74/0.97      | ~ v1_funct_1(X0)
% 2.74/0.97      | ~ v2_funct_1(X0)
% 2.74/0.97      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.74/0.97      inference(cnf_transformation,[],[f63]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_24,negated_conjecture,
% 2.74/0.97      ( v2_funct_1(sK2) ),
% 2.74/0.97      inference(cnf_transformation,[],[f74]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_604,plain,
% 2.74/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 2.74/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.97      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.74/0.97      | ~ v1_funct_1(X0)
% 2.74/0.97      | k2_relset_1(X1,X2,X0) != X2
% 2.74/0.97      | sK2 != X0 ),
% 2.74/0.97      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_605,plain,
% 2.74/0.97      ( ~ v1_funct_2(sK2,X0,X1)
% 2.74/0.97      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.74/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.74/0.97      | ~ v1_funct_1(sK2)
% 2.74/0.97      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.74/0.97      inference(unflattening,[status(thm)],[c_604]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_609,plain,
% 2.74/0.97      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.74/0.97      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.74/0.97      | ~ v1_funct_2(sK2,X0,X1)
% 2.74/0.97      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.74/0.97      inference(global_propositional_subsumption,
% 2.74/0.97                [status(thm)],
% 2.74/0.97                [c_605,c_28]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_610,plain,
% 2.74/0.97      ( ~ v1_funct_2(sK2,X0,X1)
% 2.74/0.97      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.74/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.74/0.97      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.74/0.97      inference(renaming,[status(thm)],[c_609]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1418,plain,
% 2.74/0.97      ( k2_relset_1(X0,X1,sK2) != X1
% 2.74/0.97      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.74/0.97      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 2.74/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.74/0.97      inference(predicate_to_equality,[status(thm)],[c_610]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_2088,plain,
% 2.74/0.97      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.74/0.97      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 2.74/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.74/0.97      inference(superposition,[status(thm)],[c_1445,c_1418]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_2171,plain,
% 2.74/0.97      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
% 2.74/0.97      inference(global_propositional_subsumption,
% 2.74/0.97                [status(thm)],
% 2.74/0.97                [c_2088,c_1448,c_1442]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_14,plain,
% 2.74/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 2.74/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.97      | k1_relset_1(X1,X2,X0) = X1
% 2.74/0.97      | k1_xboole_0 = X2 ),
% 2.74/0.97      inference(cnf_transformation,[],[f53]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1426,plain,
% 2.74/0.97      ( k1_relset_1(X0,X1,X2) = X0
% 2.74/0.97      | k1_xboole_0 = X1
% 2.74/0.97      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.74/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.74/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_2190,plain,
% 2.74/0.97      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK1)
% 2.74/0.97      | k2_struct_0(sK0) = k1_xboole_0
% 2.74/0.97      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top ),
% 2.74/0.97      inference(superposition,[status(thm)],[c_2171,c_1426]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_18,plain,
% 2.74/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 2.74/0.97      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.74/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.97      | ~ v1_funct_1(X0)
% 2.74/0.97      | ~ v2_funct_1(X0)
% 2.74/0.97      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.74/0.97      inference(cnf_transformation,[],[f62]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_580,plain,
% 2.74/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 2.74/0.97      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.74/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.97      | ~ v1_funct_1(X0)
% 2.74/0.97      | k2_relset_1(X1,X2,X0) != X2
% 2.74/0.97      | sK2 != X0 ),
% 2.74/0.97      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_581,plain,
% 2.74/0.97      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 2.74/0.97      | ~ v1_funct_2(sK2,X1,X0)
% 2.74/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.74/0.97      | ~ v1_funct_1(sK2)
% 2.74/0.97      | k2_relset_1(X1,X0,sK2) != X0 ),
% 2.74/0.97      inference(unflattening,[status(thm)],[c_580]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_585,plain,
% 2.74/0.97      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.74/0.97      | ~ v1_funct_2(sK2,X1,X0)
% 2.74/0.97      | v1_funct_2(k2_funct_1(sK2),X0,X1)
% 2.74/0.97      | k2_relset_1(X1,X0,sK2) != X0 ),
% 2.74/0.97      inference(global_propositional_subsumption,
% 2.74/0.97                [status(thm)],
% 2.74/0.97                [c_581,c_28]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_586,plain,
% 2.74/0.97      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 2.74/0.97      | ~ v1_funct_2(sK2,X1,X0)
% 2.74/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.74/0.97      | k2_relset_1(X1,X0,sK2) != X0 ),
% 2.74/0.97      inference(renaming,[status(thm)],[c_585]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1419,plain,
% 2.74/0.97      ( k2_relset_1(X0,X1,sK2) != X1
% 2.74/0.97      | v1_funct_2(k2_funct_1(sK2),X1,X0) = iProver_top
% 2.74/0.97      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.74/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.74/0.97      inference(predicate_to_equality,[status(thm)],[c_586]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1926,plain,
% 2.74/0.97      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
% 2.74/0.97      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.74/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.74/0.97      inference(superposition,[status(thm)],[c_1445,c_1419]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_3379,plain,
% 2.74/0.97      ( k2_struct_0(sK0) = k1_xboole_0
% 2.74/0.97      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK1) ),
% 2.74/0.97      inference(global_propositional_subsumption,
% 2.74/0.97                [status(thm)],
% 2.74/0.97                [c_2190,c_1448,c_1442,c_1926]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_3380,plain,
% 2.74/0.97      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK1)
% 2.74/0.97      | k2_struct_0(sK0) = k1_xboole_0 ),
% 2.74/0.97      inference(renaming,[status(thm)],[c_3379]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_3381,plain,
% 2.74/0.97      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.74/0.97      | k2_struct_0(sK0) = k1_xboole_0 ),
% 2.74/0.97      inference(light_normalisation,[status(thm)],[c_3380,c_2791]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_22,plain,
% 2.74/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 2.74/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.97      | ~ v1_funct_1(X0)
% 2.74/0.97      | ~ v2_funct_1(X0)
% 2.74/0.97      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.74/0.97      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.74/0.97      inference(cnf_transformation,[],[f66]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_532,plain,
% 2.74/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 2.74/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.74/0.97      | ~ v1_funct_1(X0)
% 2.74/0.97      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.74/0.97      | k2_relset_1(X1,X2,X0) != X2
% 2.74/0.97      | sK2 != X0 ),
% 2.74/0.97      inference(resolution_lifted,[status(thm)],[c_22,c_24]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_533,plain,
% 2.74/0.97      ( ~ v1_funct_2(sK2,X0,X1)
% 2.74/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.74/0.97      | ~ v1_funct_1(sK2)
% 2.74/0.97      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.74/0.97      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.74/0.97      inference(unflattening,[status(thm)],[c_532]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_537,plain,
% 2.74/0.97      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.74/0.97      | ~ v1_funct_2(sK2,X0,X1)
% 2.74/0.97      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.74/0.97      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.74/0.97      inference(global_propositional_subsumption,
% 2.74/0.97                [status(thm)],
% 2.74/0.97                [c_533,c_28]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_538,plain,
% 2.74/0.97      ( ~ v1_funct_2(sK2,X0,X1)
% 2.74/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.74/0.97      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.74/0.97      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.74/0.97      inference(renaming,[status(thm)],[c_537]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1421,plain,
% 2.74/0.97      ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.74/0.97      | k2_relset_1(X0,X1,sK2) != X1
% 2.74/0.97      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.74/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.74/0.97      inference(predicate_to_equality,[status(thm)],[c_538]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1996,plain,
% 2.74/0.97      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.74/0.97      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.74/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.74/0.97      inference(superposition,[status(thm)],[c_1445,c_1421]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1999,plain,
% 2.74/0.97      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.74/0.97      inference(global_propositional_subsumption,
% 2.74/0.97                [status(thm)],
% 2.74/0.97                [c_1996,c_1448,c_1442]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_23,negated_conjecture,
% 2.74/0.97      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.74/0.97      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.74/0.97      inference(cnf_transformation,[],[f75]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1529,plain,
% 2.74/0.97      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.74/0.97      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.74/0.97      inference(light_normalisation,[status(thm)],[c_23,c_350,c_355]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_2002,plain,
% 2.74/0.97      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1)
% 2.74/0.97      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 2.74/0.97      inference(demodulation,[status(thm)],[c_1999,c_1529]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_3011,plain,
% 2.74/0.97      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
% 2.74/0.97      | k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 2.74/0.97      inference(demodulation,[status(thm)],[c_2791,c_2002]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_2177,plain,
% 2.74/0.97      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.74/0.97      inference(superposition,[status(thm)],[c_2171,c_1432]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_2,plain,
% 2.74/0.97      ( ~ v1_funct_1(X0)
% 2.74/0.97      | ~ v2_funct_1(X0)
% 2.74/0.97      | ~ v1_relat_1(X0)
% 2.74/0.97      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.74/0.97      inference(cnf_transformation,[],[f47]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_642,plain,
% 2.74/0.97      ( ~ v1_funct_1(X0)
% 2.74/0.97      | ~ v1_relat_1(X0)
% 2.74/0.97      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.74/0.97      | sK2 != X0 ),
% 2.74/0.97      inference(resolution_lifted,[status(thm)],[c_2,c_24]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_643,plain,
% 2.74/0.97      ( ~ v1_funct_1(sK2)
% 2.74/0.97      | ~ v1_relat_1(sK2)
% 2.74/0.97      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.74/0.97      inference(unflattening,[status(thm)],[c_642]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_645,plain,
% 2.74/0.97      ( ~ v1_relat_1(sK2)
% 2.74/0.97      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.74/0.97      inference(global_propositional_subsumption,
% 2.74/0.97                [status(thm)],
% 2.74/0.97                [c_643,c_28]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1416,plain,
% 2.74/0.97      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.74/0.97      | v1_relat_1(sK2) != iProver_top ),
% 2.74/0.97      inference(predicate_to_equality,[status(thm)],[c_645]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1633,plain,
% 2.74/0.97      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.74/0.97      | v1_relat_1(sK2) ),
% 2.74/0.97      inference(instantiation,[status(thm)],[c_4]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1665,plain,
% 2.74/0.97      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.74/0.97      inference(global_propositional_subsumption,
% 2.74/0.97                [status(thm)],
% 2.74/0.97                [c_1416,c_28,c_26,c_643,c_1633]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_2179,plain,
% 2.74/0.97      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.74/0.97      inference(light_normalisation,[status(thm)],[c_2177,c_1665]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_3438,plain,
% 2.74/0.97      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.74/0.97      inference(light_normalisation,[status(thm)],[c_2179,c_2791]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_3621,plain,
% 2.74/0.97      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
% 2.74/0.97      | k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 2.74/0.97      inference(light_normalisation,[status(thm)],[c_3011,c_3438]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_3624,plain,
% 2.74/0.97      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 2.74/0.97      | k2_struct_0(sK0) = k1_xboole_0 ),
% 2.74/0.97      inference(superposition,[status(thm)],[c_3381,c_3621]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_3746,plain,
% 2.74/0.97      ( k2_struct_0(sK0) = k1_xboole_0 ),
% 2.74/0.97      inference(global_propositional_subsumption,
% 2.74/0.97                [status(thm)],
% 2.74/0.97                [c_3624,c_3634]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_3874,plain,
% 2.74/0.97      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 2.74/0.97      inference(light_normalisation,[status(thm)],[c_3634,c_3746]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_0,plain,
% 2.74/0.97      ( ~ v1_relat_1(X0)
% 2.74/0.97      | k2_relat_1(X0) != k1_xboole_0
% 2.74/0.97      | k1_relat_1(X0) = k1_xboole_0 ),
% 2.74/0.97      inference(cnf_transformation,[],[f45]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1435,plain,
% 2.74/0.97      ( k2_relat_1(X0) != k1_xboole_0
% 2.74/0.97      | k1_relat_1(X0) = k1_xboole_0
% 2.74/0.97      | v1_relat_1(X0) != iProver_top ),
% 2.74/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1771,plain,
% 2.74/0.97      ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0
% 2.74/0.97      | k1_relat_1(sK2) != k1_xboole_0
% 2.74/0.97      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.74/0.97      inference(superposition,[status(thm)],[c_1665,c_1435]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_3,plain,
% 2.74/0.97      ( ~ v1_funct_1(X0)
% 2.74/0.97      | ~ v2_funct_1(X0)
% 2.74/0.97      | ~ v1_relat_1(X0)
% 2.74/0.97      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.74/0.97      inference(cnf_transformation,[],[f46]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_628,plain,
% 2.74/0.97      ( ~ v1_funct_1(X0)
% 2.74/0.97      | ~ v1_relat_1(X0)
% 2.74/0.97      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.74/0.97      | sK2 != X0 ),
% 2.74/0.97      inference(resolution_lifted,[status(thm)],[c_3,c_24]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_629,plain,
% 2.74/0.97      ( ~ v1_funct_1(sK2)
% 2.74/0.97      | ~ v1_relat_1(sK2)
% 2.74/0.97      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.74/0.97      inference(unflattening,[status(thm)],[c_628]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_631,plain,
% 2.74/0.97      ( ~ v1_relat_1(sK2)
% 2.74/0.97      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.74/0.97      inference(global_propositional_subsumption,
% 2.74/0.97                [status(thm)],
% 2.74/0.97                [c_629,c_28]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1417,plain,
% 2.74/0.97      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.74/0.97      | v1_relat_1(sK2) != iProver_top ),
% 2.74/0.97      inference(predicate_to_equality,[status(thm)],[c_631]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1696,plain,
% 2.74/0.97      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.74/0.97      inference(global_propositional_subsumption,
% 2.74/0.97                [status(thm)],
% 2.74/0.97                [c_1417,c_28,c_26,c_629,c_1633]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1772,plain,
% 2.74/0.97      ( k2_relat_1(sK2) = k1_xboole_0
% 2.74/0.97      | k1_relat_1(sK2) != k1_xboole_0
% 2.74/0.97      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.74/0.97      inference(demodulation,[status(thm)],[c_1771,c_1696]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1,plain,
% 2.74/0.97      ( ~ v1_relat_1(X0)
% 2.74/0.97      | k2_relat_1(X0) = k1_xboole_0
% 2.74/0.97      | k1_relat_1(X0) != k1_xboole_0 ),
% 2.74/0.97      inference(cnf_transformation,[],[f44]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1674,plain,
% 2.74/0.97      ( ~ v1_relat_1(sK2)
% 2.74/0.97      | k2_relat_1(sK2) = k1_xboole_0
% 2.74/0.97      | k1_relat_1(sK2) != k1_xboole_0 ),
% 2.74/0.97      inference(instantiation,[status(thm)],[c_1]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_3582,plain,
% 2.74/0.97      ( k1_relat_1(sK2) != k1_xboole_0 | k2_relat_1(sK2) = k1_xboole_0 ),
% 2.74/0.97      inference(global_propositional_subsumption,
% 2.74/0.97                [status(thm)],
% 2.74/0.97                [c_1772,c_26,c_1633,c_1674]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_3583,plain,
% 2.74/0.97      ( k2_relat_1(sK2) = k1_xboole_0 | k1_relat_1(sK2) != k1_xboole_0 ),
% 2.74/0.97      inference(renaming,[status(thm)],[c_3582]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_3876,plain,
% 2.74/0.97      ( k2_relat_1(sK2) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.74/0.97      inference(demodulation,[status(thm)],[c_3874,c_3583]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_3881,plain,
% 2.74/0.97      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 2.74/0.97      inference(equality_resolution_simp,[status(thm)],[c_3876]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_3010,plain,
% 2.74/0.97      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 2.74/0.97      inference(demodulation,[status(thm)],[c_2791,c_2171]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_3750,plain,
% 2.74/0.97      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_xboole_0))) = iProver_top ),
% 2.74/0.97      inference(demodulation,[status(thm)],[c_3746,c_3010]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_4410,plain,
% 2.74/0.97      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 2.74/0.97      inference(demodulation,[status(thm)],[c_3881,c_3750]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_13,plain,
% 2.74/0.97      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.74/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.74/0.97      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.74/0.97      inference(cnf_transformation,[],[f80]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1427,plain,
% 2.74/0.97      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 2.74/0.97      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 2.74/0.97      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 2.74/0.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_5288,plain,
% 2.74/0.97      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) = k1_xboole_0
% 2.74/0.97      | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.74/0.97      inference(superposition,[status(thm)],[c_4410,c_1427]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_3749,plain,
% 2.74/0.97      ( k1_relset_1(k2_relat_1(sK2),k1_xboole_0,k2_funct_1(sK2)) != k2_relat_1(sK2)
% 2.74/0.97      | k1_relat_1(sK2) != k1_xboole_0 ),
% 2.74/0.97      inference(demodulation,[status(thm)],[c_3746,c_3621]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1044,plain,( X0 = X0 ),theory(equality) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1075,plain,
% 2.74/0.97      ( k1_xboole_0 = k1_xboole_0 ),
% 2.74/0.97      inference(instantiation,[status(thm)],[c_1044]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1630,plain,
% 2.74/0.97      ( ~ v1_funct_2(sK2,X0,u1_struct_0(sK1))
% 2.74/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.74/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
% 2.74/0.97      | ~ v1_funct_1(sK2)
% 2.74/0.97      | k1_relat_1(sK2) = X0 ),
% 2.74/0.97      inference(instantiation,[status(thm)],[c_428]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1726,plain,
% 2.74/0.97      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.74/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
% 2.74/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.74/0.97      | ~ v1_funct_1(sK2)
% 2.74/0.97      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 2.74/0.97      inference(instantiation,[status(thm)],[c_1630]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1918,plain,
% 2.74/0.97      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.74/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.74/0.97      | ~ v1_funct_1(sK2)
% 2.74/0.97      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 2.74/0.97      inference(instantiation,[status(thm)],[c_1726]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1045,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1759,plain,
% 2.74/0.97      ( k1_relat_1(sK2) != X0
% 2.74/0.97      | k1_relat_1(sK2) = k1_xboole_0
% 2.74/0.97      | k1_xboole_0 != X0 ),
% 2.74/0.97      inference(instantiation,[status(thm)],[c_1045]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_2022,plain,
% 2.74/0.97      ( k1_relat_1(sK2) != u1_struct_0(sK0)
% 2.74/0.97      | k1_relat_1(sK2) = k1_xboole_0
% 2.74/0.97      | k1_xboole_0 != u1_struct_0(sK0) ),
% 2.74/0.97      inference(instantiation,[status(thm)],[c_1759]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1909,plain,
% 2.74/0.97      ( X0 != X1 | X0 = u1_struct_0(sK0) | u1_struct_0(sK0) != X1 ),
% 2.74/0.97      inference(instantiation,[status(thm)],[c_1045]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_2836,plain,
% 2.74/0.97      ( X0 = u1_struct_0(sK0)
% 2.74/0.97      | X0 != k2_struct_0(sK0)
% 2.74/0.97      | u1_struct_0(sK0) != k2_struct_0(sK0) ),
% 2.74/0.97      inference(instantiation,[status(thm)],[c_1909]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_2837,plain,
% 2.74/0.97      ( u1_struct_0(sK0) != k2_struct_0(sK0)
% 2.74/0.97      | k1_xboole_0 = u1_struct_0(sK0)
% 2.74/0.97      | k1_xboole_0 != k2_struct_0(sK0) ),
% 2.74/0.97      inference(instantiation,[status(thm)],[c_2836]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_3236,plain,
% 2.74/0.97      ( X0 != X1 | X0 = k2_struct_0(sK0) | k2_struct_0(sK0) != X1 ),
% 2.74/0.97      inference(instantiation,[status(thm)],[c_1045]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_3237,plain,
% 2.74/0.97      ( k2_struct_0(sK0) != k1_xboole_0
% 2.74/0.97      | k1_xboole_0 = k2_struct_0(sK0)
% 2.74/0.97      | k1_xboole_0 != k1_xboole_0 ),
% 2.74/0.97      inference(instantiation,[status(thm)],[c_3236]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_4459,plain,
% 2.74/0.97      ( k1_relset_1(k2_relat_1(sK2),k1_xboole_0,k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 2.74/0.97      inference(global_propositional_subsumption,
% 2.74/0.97                [status(thm)],
% 2.74/0.97                [c_3749,c_28,c_27,c_26,c_355,c_1075,c_1918,c_2022,c_2837,
% 2.74/0.97                 c_3237,c_3624,c_3634]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_4461,plain,
% 2.74/0.97      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) != k1_xboole_0 ),
% 2.74/0.97      inference(light_normalisation,[status(thm)],[c_4459,c_3881]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_1929,plain,
% 2.74/0.97      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top ),
% 2.74/0.97      inference(global_propositional_subsumption,
% 2.74/0.97                [status(thm)],
% 2.74/0.97                [c_1926,c_1448,c_1442]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_3013,plain,
% 2.74/0.97      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top ),
% 2.74/0.97      inference(demodulation,[status(thm)],[c_2791,c_1929]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_3753,plain,
% 2.74/0.97      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_xboole_0) = iProver_top ),
% 2.74/0.97      inference(demodulation,[status(thm)],[c_3746,c_3013]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(c_4415,plain,
% 2.74/0.97      ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.74/0.97      inference(demodulation,[status(thm)],[c_3881,c_3753]) ).
% 2.74/0.97  
% 2.74/0.97  cnf(contradiction,plain,
% 2.74/0.97      ( $false ),
% 2.74/0.97      inference(minisat,[status(thm)],[c_5288,c_4461,c_4415]) ).
% 2.74/0.97  
% 2.74/0.97  
% 2.74/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.74/0.97  
% 2.74/0.97  ------                               Statistics
% 2.74/0.97  
% 2.74/0.97  ------ General
% 2.74/0.97  
% 2.74/0.97  abstr_ref_over_cycles:                  0
% 2.74/0.97  abstr_ref_under_cycles:                 0
% 2.74/0.97  gc_basic_clause_elim:                   0
% 2.74/0.97  forced_gc_time:                         0
% 2.74/0.97  parsing_time:                           0.012
% 2.74/0.97  unif_index_cands_time:                  0.
% 2.74/0.97  unif_index_add_time:                    0.
% 2.74/0.97  orderings_time:                         0.
% 2.74/0.97  out_proof_time:                         0.016
% 2.74/0.97  total_time:                             0.19
% 2.74/0.97  num_of_symbols:                         55
% 2.74/0.97  num_of_terms:                           4277
% 2.74/0.97  
% 2.74/0.97  ------ Preprocessing
% 2.74/0.97  
% 2.74/0.97  num_of_splits:                          0
% 2.74/0.97  num_of_split_atoms:                     0
% 2.74/0.97  num_of_reused_defs:                     0
% 2.74/0.97  num_eq_ax_congr_red:                    4
% 2.74/0.97  num_of_sem_filtered_clauses:            1
% 2.74/0.97  num_of_subtypes:                        0
% 2.74/0.97  monotx_restored_types:                  0
% 2.74/0.97  sat_num_of_epr_types:                   0
% 2.74/0.97  sat_num_of_non_cyclic_types:            0
% 2.74/0.97  sat_guarded_non_collapsed_types:        0
% 2.74/0.97  num_pure_diseq_elim:                    0
% 2.74/0.97  simp_replaced_by:                       0
% 2.74/0.97  res_preprocessed:                       136
% 2.74/0.97  prep_upred:                             0
% 2.74/0.97  prep_unflattend:                        22
% 2.74/0.97  smt_new_axioms:                         0
% 2.74/0.97  pred_elim_cands:                        4
% 2.74/0.97  pred_elim:                              6
% 2.74/0.97  pred_elim_cl:                           7
% 2.74/0.97  pred_elim_cycles:                       11
% 2.74/0.97  merged_defs:                            0
% 2.74/0.97  merged_defs_ncl:                        0
% 2.74/0.97  bin_hyper_res:                          0
% 2.74/0.97  prep_cycles:                            4
% 2.74/0.97  pred_elim_time:                         0.011
% 2.74/0.97  splitting_time:                         0.
% 2.74/0.97  sem_filter_time:                        0.
% 2.74/0.97  monotx_time:                            0.
% 2.74/0.97  subtype_inf_time:                       0.
% 2.74/0.97  
% 2.74/0.97  ------ Problem properties
% 2.74/0.97  
% 2.74/0.97  clauses:                                24
% 2.74/0.97  conjectures:                            5
% 2.74/0.97  epr:                                    1
% 2.74/0.97  horn:                                   20
% 2.74/0.97  ground:                                 9
% 2.74/0.97  unary:                                  6
% 2.74/0.97  binary:                                 5
% 2.74/0.97  lits:                                   64
% 2.74/0.97  lits_eq:                                27
% 2.74/0.97  fd_pure:                                0
% 2.74/0.97  fd_pseudo:                              0
% 2.74/0.97  fd_cond:                                3
% 2.74/0.97  fd_pseudo_cond:                         1
% 2.74/0.97  ac_symbols:                             0
% 2.74/0.97  
% 2.74/0.97  ------ Propositional Solver
% 2.74/0.97  
% 2.74/0.97  prop_solver_calls:                      28
% 2.74/0.97  prop_fast_solver_calls:                 1054
% 2.74/0.97  smt_solver_calls:                       0
% 2.74/0.97  smt_fast_solver_calls:                  0
% 2.74/0.97  prop_num_of_clauses:                    1591
% 2.74/0.97  prop_preprocess_simplified:             5466
% 2.74/0.97  prop_fo_subsumed:                       29
% 2.74/0.97  prop_solver_time:                       0.
% 2.74/0.97  smt_solver_time:                        0.
% 2.74/0.97  smt_fast_solver_time:                   0.
% 2.74/0.97  prop_fast_solver_time:                  0.
% 2.74/0.97  prop_unsat_core_time:                   0.
% 2.74/0.97  
% 2.74/0.97  ------ QBF
% 2.74/0.97  
% 2.74/0.97  qbf_q_res:                              0
% 2.74/0.97  qbf_num_tautologies:                    0
% 2.74/0.97  qbf_prep_cycles:                        0
% 2.74/0.97  
% 2.74/0.97  ------ BMC1
% 2.74/0.97  
% 2.74/0.97  bmc1_current_bound:                     -1
% 2.74/0.97  bmc1_last_solved_bound:                 -1
% 2.74/0.97  bmc1_unsat_core_size:                   -1
% 2.74/0.97  bmc1_unsat_core_parents_size:           -1
% 2.74/0.97  bmc1_merge_next_fun:                    0
% 2.74/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.74/0.97  
% 2.74/0.97  ------ Instantiation
% 2.74/0.97  
% 2.74/0.97  inst_num_of_clauses:                    666
% 2.74/0.97  inst_num_in_passive:                    2
% 2.74/0.97  inst_num_in_active:                     338
% 2.74/0.97  inst_num_in_unprocessed:                326
% 2.74/0.97  inst_num_of_loops:                      360
% 2.74/0.97  inst_num_of_learning_restarts:          0
% 2.74/0.97  inst_num_moves_active_passive:          19
% 2.74/0.97  inst_lit_activity:                      0
% 2.74/0.97  inst_lit_activity_moves:                0
% 2.74/0.97  inst_num_tautologies:                   0
% 2.74/0.97  inst_num_prop_implied:                  0
% 2.74/0.97  inst_num_existing_simplified:           0
% 2.74/0.97  inst_num_eq_res_simplified:             0
% 2.74/0.97  inst_num_child_elim:                    0
% 2.74/0.97  inst_num_of_dismatching_blockings:      70
% 2.74/0.97  inst_num_of_non_proper_insts:           544
% 2.74/0.97  inst_num_of_duplicates:                 0
% 2.74/0.97  inst_inst_num_from_inst_to_res:         0
% 2.74/0.97  inst_dismatching_checking_time:         0.
% 2.74/0.97  
% 2.74/0.97  ------ Resolution
% 2.74/0.97  
% 2.74/0.97  res_num_of_clauses:                     0
% 2.74/0.97  res_num_in_passive:                     0
% 2.74/0.97  res_num_in_active:                      0
% 2.74/0.97  res_num_of_loops:                       140
% 2.74/0.97  res_forward_subset_subsumed:            62
% 2.74/0.97  res_backward_subset_subsumed:           4
% 2.74/0.97  res_forward_subsumed:                   0
% 2.74/0.97  res_backward_subsumed:                  0
% 2.74/0.97  res_forward_subsumption_resolution:     1
% 2.74/0.97  res_backward_subsumption_resolution:    0
% 2.74/0.97  res_clause_to_clause_subsumption:       87
% 2.74/0.97  res_orphan_elimination:                 0
% 2.74/0.97  res_tautology_del:                      75
% 2.74/0.97  res_num_eq_res_simplified:              0
% 2.74/0.97  res_num_sel_changes:                    0
% 2.74/0.97  res_moves_from_active_to_pass:          0
% 2.74/0.97  
% 2.74/0.97  ------ Superposition
% 2.74/0.97  
% 2.74/0.97  sup_time_total:                         0.
% 2.74/0.97  sup_time_generating:                    0.
% 2.74/0.97  sup_time_sim_full:                      0.
% 2.74/0.97  sup_time_sim_immed:                     0.
% 2.74/0.97  
% 2.74/0.97  sup_num_of_clauses:                     36
% 2.74/0.97  sup_num_in_active:                      34
% 2.74/0.97  sup_num_in_passive:                     2
% 2.74/0.97  sup_num_of_loops:                       70
% 2.74/0.97  sup_fw_superposition:                   13
% 2.74/0.97  sup_bw_superposition:                   49
% 2.74/0.97  sup_immediate_simplified:               37
% 2.74/0.97  sup_given_eliminated:                   0
% 2.74/0.97  comparisons_done:                       0
% 2.74/0.97  comparisons_avoided:                    6
% 2.74/0.97  
% 2.74/0.97  ------ Simplifications
% 2.74/0.97  
% 2.74/0.97  
% 2.74/0.97  sim_fw_subset_subsumed:                 28
% 2.74/0.97  sim_bw_subset_subsumed:                 2
% 2.74/0.97  sim_fw_subsumed:                        0
% 2.74/0.97  sim_bw_subsumed:                        0
% 2.74/0.97  sim_fw_subsumption_res:                 0
% 2.74/0.97  sim_bw_subsumption_res:                 0
% 2.74/0.97  sim_tautology_del:                      0
% 2.74/0.97  sim_eq_tautology_del:                   11
% 2.74/0.97  sim_eq_res_simp:                        1
% 2.74/0.97  sim_fw_demodulated:                     4
% 2.74/0.97  sim_bw_demodulated:                     36
% 2.74/0.97  sim_light_normalised:                   18
% 2.74/0.97  sim_joinable_taut:                      0
% 2.74/0.97  sim_joinable_simp:                      0
% 2.74/0.97  sim_ac_normalised:                      0
% 2.74/0.97  sim_smt_subsumption:                    0
% 2.74/0.97  
%------------------------------------------------------------------------------
