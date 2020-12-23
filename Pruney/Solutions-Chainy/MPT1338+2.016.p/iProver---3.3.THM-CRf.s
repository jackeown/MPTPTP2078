%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:02 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :  183 (3987 expanded)
%              Number of clauses        :  118 (1161 expanded)
%              Number of leaves         :   17 (1113 expanded)
%              Depth                    :   29
%              Number of atoms          :  542 (27528 expanded)
%              Number of equality atoms :  213 (8769 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

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
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f41,plain,(
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

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f42,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f41,f40,f39])).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f56,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k4_relat_1(X2) = k3_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_relat_1(X2) = k3_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_relat_1(X2) = k3_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(X0) = k4_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f43,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f66,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f45,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f67,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_599,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_829,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_599])).

cnf(c_13,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_24,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_280,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_281,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_597,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_281])).

cnf(c_22,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_275,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_276,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_598,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_276])).

cnf(c_842,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_829,c_597,c_598])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_602,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | k3_relset_1(X0_56,X1_56,X0_53) = k4_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_828,plain,
    ( k3_relset_1(X0_56,X1_56,X0_53) = k4_relat_1(X0_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_602])).

cnf(c_1124,plain,
    ( k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_842,c_828])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k4_relat_1(X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_17,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_448,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k4_relat_1(X0) = k2_funct_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_17])).

cnf(c_449,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k4_relat_1(sK2) = k2_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_451,plain,
    ( ~ v1_relat_1(sK2)
    | k4_relat_1(sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_449,c_21])).

cnf(c_471,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k4_relat_1(sK2) = k2_funct_1(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_451])).

cnf(c_472,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k4_relat_1(sK2) = k2_funct_1(sK2) ),
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_594,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | k4_relat_1(sK2) = k2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_472])).

cnf(c_832,plain,
    ( k4_relat_1(sK2) = k2_funct_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_594])).

cnf(c_929,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k4_relat_1(sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_594])).

cnf(c_966,plain,
    ( k4_relat_1(sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_832,c_19,c_929])).

cnf(c_1126,plain,
    ( k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1124,c_966])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_603,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | k2_relset_1(X0_56,X1_56,X0_53) = k2_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_827,plain,
    ( k2_relset_1(X0_56,X1_56,X0_53) = k2_relat_1(X0_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_603])).

cnf(c_1110,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_842,c_827])).

cnf(c_18,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_600,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_839,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_600,c_597,c_598])).

cnf(c_1177,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1110,c_839])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_14,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_262,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_263,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_262])).

cnf(c_36,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_265,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_263,c_23,c_22,c_36])).

cnf(c_287,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_265])).

cnf(c_288,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_4,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_12,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_310,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_4,c_12])).

cnf(c_314,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_310,c_12,c_4,c_3])).

cnf(c_315,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_314])).

cnf(c_354,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_288,c_315])).

cnf(c_393,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK0) != X1
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k1_relat_1(X0) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_354])).

cnf(c_394,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_39,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_398,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_394,c_22,c_21,c_39])).

cnf(c_595,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0_56)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_398])).

cnf(c_607,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | sP0_iProver_split
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_595])).

cnf(c_830,plain,
    ( k1_relat_1(sK2) = u1_struct_0(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_607])).

cnf(c_882,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_830,c_597])).

cnf(c_883,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_882,c_597])).

cnf(c_887,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | sP0_iProver_split = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_883,c_842])).

cnf(c_895,plain,
    ( sP0_iProver_split
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_887])).

cnf(c_606,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0_56)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_595])).

cnf(c_918,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_606])).

cnf(c_1566,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_887,c_19,c_895,c_918])).

cnf(c_1730,plain,
    ( k3_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1126,c_1177,c_1566])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_605,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | m1_subset_1(k3_relset_1(X0_56,X1_56,X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_56,X0_56))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_825,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
    | m1_subset_1(k3_relset_1(X0_56,X1_56,X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_56,X0_56))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_605])).

cnf(c_1732,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1730,c_825])).

cnf(c_1226,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1177,c_842])).

cnf(c_1569,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1566,c_1226])).

cnf(c_1870,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1732,c_1569])).

cnf(c_1877,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_1870,c_827])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_434,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_17])).

cnf(c_435,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_437,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_435,c_21])).

cnf(c_483,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_437])).

cnf(c_484,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_593,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_484])).

cnf(c_833,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_593])).

cnf(c_924,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_593])).

cnf(c_1353,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_833,c_19,c_924])).

cnf(c_1891,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1877,c_1353])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_604,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | k1_relset_1(X0_56,X1_56,X0_53) = k1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_826,plain,
    ( k1_relset_1(X0_56,X1_56,X0_53) = k1_relat_1(X0_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_604])).

cnf(c_1026,plain,
    ( k1_relset_1(X0_56,X1_56,k3_relset_1(X1_56,X0_56,X0_53)) = k1_relat_1(k3_relset_1(X1_56,X0_56,X0_53))
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_56,X0_56))) != iProver_top ),
    inference(superposition,[status(thm)],[c_825,c_826])).

cnf(c_1408,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k1_relat_1(k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    inference(superposition,[status(thm)],[c_1226,c_1026])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_420,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_17])).

cnf(c_421,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_423,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_421,c_21])).

cnf(c_495,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_423])).

cnf(c_496,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_495])).

cnf(c_592,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_496])).

cnf(c_834,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_592])).

cnf(c_921,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_592])).

cnf(c_1562,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_834,c_19,c_921])).

cnf(c_1824,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1408,c_1562,c_1566,c_1730])).

cnf(c_16,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_601,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_382,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | u1_struct_0(sK0) != X1
    | u1_struct_0(sK1) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_383,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_385,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_383,c_21,c_19,c_17])).

cnf(c_596,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_385])).

cnf(c_874,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_596,c_597,c_598,c_839])).

cnf(c_875,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_874])).

cnf(c_890,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_601,c_597,c_598,c_875])).

cnf(c_1227,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1177,c_890])).

cnf(c_1573,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2)
    | k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1566,c_1227])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1891,c_1824,c_1573])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:51:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.67/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.00  
% 2.67/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.67/1.00  
% 2.67/1.00  ------  iProver source info
% 2.67/1.00  
% 2.67/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.67/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.67/1.00  git: non_committed_changes: false
% 2.67/1.00  git: last_make_outside_of_git: false
% 2.67/1.00  
% 2.67/1.00  ------ 
% 2.67/1.00  
% 2.67/1.00  ------ Input Options
% 2.67/1.00  
% 2.67/1.00  --out_options                           all
% 2.67/1.00  --tptp_safe_out                         true
% 2.67/1.00  --problem_path                          ""
% 2.67/1.00  --include_path                          ""
% 2.67/1.00  --clausifier                            res/vclausify_rel
% 2.67/1.00  --clausifier_options                    --mode clausify
% 2.67/1.00  --stdin                                 false
% 2.67/1.00  --stats_out                             all
% 2.67/1.00  
% 2.67/1.00  ------ General Options
% 2.67/1.00  
% 2.67/1.00  --fof                                   false
% 2.67/1.00  --time_out_real                         305.
% 2.67/1.00  --time_out_virtual                      -1.
% 2.67/1.00  --symbol_type_check                     false
% 2.67/1.00  --clausify_out                          false
% 2.67/1.00  --sig_cnt_out                           false
% 2.67/1.00  --trig_cnt_out                          false
% 2.67/1.00  --trig_cnt_out_tolerance                1.
% 2.67/1.00  --trig_cnt_out_sk_spl                   false
% 2.67/1.00  --abstr_cl_out                          false
% 2.67/1.00  
% 2.67/1.00  ------ Global Options
% 2.67/1.00  
% 2.67/1.00  --schedule                              default
% 2.67/1.00  --add_important_lit                     false
% 2.67/1.00  --prop_solver_per_cl                    1000
% 2.67/1.00  --min_unsat_core                        false
% 2.67/1.00  --soft_assumptions                      false
% 2.67/1.00  --soft_lemma_size                       3
% 2.67/1.00  --prop_impl_unit_size                   0
% 2.67/1.00  --prop_impl_unit                        []
% 2.67/1.00  --share_sel_clauses                     true
% 2.67/1.00  --reset_solvers                         false
% 2.67/1.00  --bc_imp_inh                            [conj_cone]
% 2.67/1.00  --conj_cone_tolerance                   3.
% 2.67/1.00  --extra_neg_conj                        none
% 2.67/1.00  --large_theory_mode                     true
% 2.67/1.00  --prolific_symb_bound                   200
% 2.67/1.00  --lt_threshold                          2000
% 2.67/1.00  --clause_weak_htbl                      true
% 2.67/1.00  --gc_record_bc_elim                     false
% 2.67/1.00  
% 2.67/1.00  ------ Preprocessing Options
% 2.67/1.00  
% 2.67/1.00  --preprocessing_flag                    true
% 2.67/1.00  --time_out_prep_mult                    0.1
% 2.67/1.00  --splitting_mode                        input
% 2.67/1.00  --splitting_grd                         true
% 2.67/1.00  --splitting_cvd                         false
% 2.67/1.00  --splitting_cvd_svl                     false
% 2.67/1.00  --splitting_nvd                         32
% 2.67/1.00  --sub_typing                            true
% 2.67/1.00  --prep_gs_sim                           true
% 2.67/1.00  --prep_unflatten                        true
% 2.67/1.00  --prep_res_sim                          true
% 2.67/1.00  --prep_upred                            true
% 2.67/1.00  --prep_sem_filter                       exhaustive
% 2.67/1.00  --prep_sem_filter_out                   false
% 2.67/1.00  --pred_elim                             true
% 2.67/1.00  --res_sim_input                         true
% 2.67/1.00  --eq_ax_congr_red                       true
% 2.67/1.00  --pure_diseq_elim                       true
% 2.67/1.00  --brand_transform                       false
% 2.67/1.00  --non_eq_to_eq                          false
% 2.67/1.00  --prep_def_merge                        true
% 2.67/1.00  --prep_def_merge_prop_impl              false
% 2.67/1.00  --prep_def_merge_mbd                    true
% 2.67/1.00  --prep_def_merge_tr_red                 false
% 2.67/1.00  --prep_def_merge_tr_cl                  false
% 2.67/1.00  --smt_preprocessing                     true
% 2.67/1.00  --smt_ac_axioms                         fast
% 2.67/1.00  --preprocessed_out                      false
% 2.67/1.00  --preprocessed_stats                    false
% 2.67/1.00  
% 2.67/1.00  ------ Abstraction refinement Options
% 2.67/1.00  
% 2.67/1.00  --abstr_ref                             []
% 2.67/1.00  --abstr_ref_prep                        false
% 2.67/1.00  --abstr_ref_until_sat                   false
% 2.67/1.00  --abstr_ref_sig_restrict                funpre
% 2.67/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/1.00  --abstr_ref_under                       []
% 2.67/1.00  
% 2.67/1.00  ------ SAT Options
% 2.67/1.00  
% 2.67/1.00  --sat_mode                              false
% 2.67/1.00  --sat_fm_restart_options                ""
% 2.67/1.00  --sat_gr_def                            false
% 2.67/1.00  --sat_epr_types                         true
% 2.67/1.00  --sat_non_cyclic_types                  false
% 2.67/1.00  --sat_finite_models                     false
% 2.67/1.00  --sat_fm_lemmas                         false
% 2.67/1.00  --sat_fm_prep                           false
% 2.67/1.00  --sat_fm_uc_incr                        true
% 2.67/1.00  --sat_out_model                         small
% 2.67/1.00  --sat_out_clauses                       false
% 2.67/1.00  
% 2.67/1.00  ------ QBF Options
% 2.67/1.00  
% 2.67/1.00  --qbf_mode                              false
% 2.67/1.00  --qbf_elim_univ                         false
% 2.67/1.00  --qbf_dom_inst                          none
% 2.67/1.00  --qbf_dom_pre_inst                      false
% 2.67/1.00  --qbf_sk_in                             false
% 2.67/1.00  --qbf_pred_elim                         true
% 2.67/1.00  --qbf_split                             512
% 2.67/1.00  
% 2.67/1.00  ------ BMC1 Options
% 2.67/1.00  
% 2.67/1.00  --bmc1_incremental                      false
% 2.67/1.00  --bmc1_axioms                           reachable_all
% 2.67/1.00  --bmc1_min_bound                        0
% 2.67/1.00  --bmc1_max_bound                        -1
% 2.67/1.00  --bmc1_max_bound_default                -1
% 2.67/1.00  --bmc1_symbol_reachability              true
% 2.67/1.00  --bmc1_property_lemmas                  false
% 2.67/1.00  --bmc1_k_induction                      false
% 2.67/1.00  --bmc1_non_equiv_states                 false
% 2.67/1.00  --bmc1_deadlock                         false
% 2.67/1.00  --bmc1_ucm                              false
% 2.67/1.00  --bmc1_add_unsat_core                   none
% 2.67/1.00  --bmc1_unsat_core_children              false
% 2.67/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/1.00  --bmc1_out_stat                         full
% 2.67/1.00  --bmc1_ground_init                      false
% 2.67/1.00  --bmc1_pre_inst_next_state              false
% 2.67/1.00  --bmc1_pre_inst_state                   false
% 2.67/1.00  --bmc1_pre_inst_reach_state             false
% 2.67/1.00  --bmc1_out_unsat_core                   false
% 2.67/1.00  --bmc1_aig_witness_out                  false
% 2.67/1.00  --bmc1_verbose                          false
% 2.67/1.00  --bmc1_dump_clauses_tptp                false
% 2.67/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.67/1.00  --bmc1_dump_file                        -
% 2.67/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.67/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.67/1.00  --bmc1_ucm_extend_mode                  1
% 2.67/1.00  --bmc1_ucm_init_mode                    2
% 2.67/1.00  --bmc1_ucm_cone_mode                    none
% 2.67/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.67/1.00  --bmc1_ucm_relax_model                  4
% 2.67/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.67/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/1.00  --bmc1_ucm_layered_model                none
% 2.67/1.00  --bmc1_ucm_max_lemma_size               10
% 2.67/1.00  
% 2.67/1.00  ------ AIG Options
% 2.67/1.00  
% 2.67/1.00  --aig_mode                              false
% 2.67/1.00  
% 2.67/1.00  ------ Instantiation Options
% 2.67/1.00  
% 2.67/1.00  --instantiation_flag                    true
% 2.67/1.00  --inst_sos_flag                         false
% 2.67/1.00  --inst_sos_phase                        true
% 2.67/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/1.00  --inst_lit_sel_side                     num_symb
% 2.67/1.00  --inst_solver_per_active                1400
% 2.67/1.00  --inst_solver_calls_frac                1.
% 2.67/1.00  --inst_passive_queue_type               priority_queues
% 2.67/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/1.00  --inst_passive_queues_freq              [25;2]
% 2.67/1.00  --inst_dismatching                      true
% 2.67/1.00  --inst_eager_unprocessed_to_passive     true
% 2.67/1.00  --inst_prop_sim_given                   true
% 2.67/1.00  --inst_prop_sim_new                     false
% 2.67/1.00  --inst_subs_new                         false
% 2.67/1.00  --inst_eq_res_simp                      false
% 2.67/1.00  --inst_subs_given                       false
% 2.67/1.00  --inst_orphan_elimination               true
% 2.67/1.00  --inst_learning_loop_flag               true
% 2.67/1.00  --inst_learning_start                   3000
% 2.67/1.00  --inst_learning_factor                  2
% 2.67/1.00  --inst_start_prop_sim_after_learn       3
% 2.67/1.00  --inst_sel_renew                        solver
% 2.67/1.00  --inst_lit_activity_flag                true
% 2.67/1.00  --inst_restr_to_given                   false
% 2.67/1.00  --inst_activity_threshold               500
% 2.67/1.00  --inst_out_proof                        true
% 2.67/1.00  
% 2.67/1.00  ------ Resolution Options
% 2.67/1.00  
% 2.67/1.00  --resolution_flag                       true
% 2.67/1.00  --res_lit_sel                           adaptive
% 2.67/1.00  --res_lit_sel_side                      none
% 2.67/1.00  --res_ordering                          kbo
% 2.67/1.00  --res_to_prop_solver                    active
% 2.67/1.00  --res_prop_simpl_new                    false
% 2.67/1.00  --res_prop_simpl_given                  true
% 2.67/1.00  --res_passive_queue_type                priority_queues
% 2.67/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/1.00  --res_passive_queues_freq               [15;5]
% 2.67/1.00  --res_forward_subs                      full
% 2.67/1.00  --res_backward_subs                     full
% 2.67/1.00  --res_forward_subs_resolution           true
% 2.67/1.00  --res_backward_subs_resolution          true
% 2.67/1.00  --res_orphan_elimination                true
% 2.67/1.00  --res_time_limit                        2.
% 2.67/1.00  --res_out_proof                         true
% 2.67/1.00  
% 2.67/1.00  ------ Superposition Options
% 2.67/1.00  
% 2.67/1.00  --superposition_flag                    true
% 2.67/1.00  --sup_passive_queue_type                priority_queues
% 2.67/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.67/1.00  --demod_completeness_check              fast
% 2.67/1.00  --demod_use_ground                      true
% 2.67/1.00  --sup_to_prop_solver                    passive
% 2.67/1.00  --sup_prop_simpl_new                    true
% 2.67/1.00  --sup_prop_simpl_given                  true
% 2.67/1.00  --sup_fun_splitting                     false
% 2.67/1.00  --sup_smt_interval                      50000
% 2.67/1.00  
% 2.67/1.00  ------ Superposition Simplification Setup
% 2.67/1.00  
% 2.67/1.00  --sup_indices_passive                   []
% 2.67/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.00  --sup_full_bw                           [BwDemod]
% 2.67/1.00  --sup_immed_triv                        [TrivRules]
% 2.67/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.00  --sup_immed_bw_main                     []
% 2.67/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.00  
% 2.67/1.00  ------ Combination Options
% 2.67/1.00  
% 2.67/1.00  --comb_res_mult                         3
% 2.67/1.00  --comb_sup_mult                         2
% 2.67/1.00  --comb_inst_mult                        10
% 2.67/1.00  
% 2.67/1.00  ------ Debug Options
% 2.67/1.00  
% 2.67/1.00  --dbg_backtrace                         false
% 2.67/1.00  --dbg_dump_prop_clauses                 false
% 2.67/1.00  --dbg_dump_prop_clauses_file            -
% 2.67/1.00  --dbg_out_stat                          false
% 2.67/1.00  ------ Parsing...
% 2.67/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.67/1.00  
% 2.67/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 2.67/1.00  
% 2.67/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.67/1.00  
% 2.67/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.67/1.00  ------ Proving...
% 2.67/1.00  ------ Problem Properties 
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  clauses                                 15
% 2.67/1.00  conjectures                             3
% 2.67/1.00  EPR                                     0
% 2.67/1.00  Horn                                    14
% 2.67/1.00  unary                                   4
% 2.67/1.00  binary                                  10
% 2.67/1.00  lits                                    27
% 2.67/1.00  lits eq                                 14
% 2.67/1.00  fd_pure                                 0
% 2.67/1.00  fd_pseudo                               0
% 2.67/1.00  fd_cond                                 0
% 2.67/1.00  fd_pseudo_cond                          0
% 2.67/1.00  AC symbols                              0
% 2.67/1.00  
% 2.67/1.00  ------ Schedule dynamic 5 is on 
% 2.67/1.00  
% 2.67/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  ------ 
% 2.67/1.00  Current options:
% 2.67/1.00  ------ 
% 2.67/1.00  
% 2.67/1.00  ------ Input Options
% 2.67/1.00  
% 2.67/1.00  --out_options                           all
% 2.67/1.00  --tptp_safe_out                         true
% 2.67/1.00  --problem_path                          ""
% 2.67/1.00  --include_path                          ""
% 2.67/1.00  --clausifier                            res/vclausify_rel
% 2.67/1.00  --clausifier_options                    --mode clausify
% 2.67/1.00  --stdin                                 false
% 2.67/1.00  --stats_out                             all
% 2.67/1.00  
% 2.67/1.00  ------ General Options
% 2.67/1.00  
% 2.67/1.00  --fof                                   false
% 2.67/1.00  --time_out_real                         305.
% 2.67/1.00  --time_out_virtual                      -1.
% 2.67/1.00  --symbol_type_check                     false
% 2.67/1.00  --clausify_out                          false
% 2.67/1.00  --sig_cnt_out                           false
% 2.67/1.00  --trig_cnt_out                          false
% 2.67/1.00  --trig_cnt_out_tolerance                1.
% 2.67/1.00  --trig_cnt_out_sk_spl                   false
% 2.67/1.00  --abstr_cl_out                          false
% 2.67/1.00  
% 2.67/1.00  ------ Global Options
% 2.67/1.00  
% 2.67/1.00  --schedule                              default
% 2.67/1.00  --add_important_lit                     false
% 2.67/1.00  --prop_solver_per_cl                    1000
% 2.67/1.00  --min_unsat_core                        false
% 2.67/1.00  --soft_assumptions                      false
% 2.67/1.00  --soft_lemma_size                       3
% 2.67/1.00  --prop_impl_unit_size                   0
% 2.67/1.00  --prop_impl_unit                        []
% 2.67/1.00  --share_sel_clauses                     true
% 2.67/1.00  --reset_solvers                         false
% 2.67/1.00  --bc_imp_inh                            [conj_cone]
% 2.67/1.00  --conj_cone_tolerance                   3.
% 2.67/1.00  --extra_neg_conj                        none
% 2.67/1.00  --large_theory_mode                     true
% 2.67/1.00  --prolific_symb_bound                   200
% 2.67/1.00  --lt_threshold                          2000
% 2.67/1.00  --clause_weak_htbl                      true
% 2.67/1.00  --gc_record_bc_elim                     false
% 2.67/1.00  
% 2.67/1.00  ------ Preprocessing Options
% 2.67/1.00  
% 2.67/1.00  --preprocessing_flag                    true
% 2.67/1.00  --time_out_prep_mult                    0.1
% 2.67/1.00  --splitting_mode                        input
% 2.67/1.00  --splitting_grd                         true
% 2.67/1.00  --splitting_cvd                         false
% 2.67/1.00  --splitting_cvd_svl                     false
% 2.67/1.00  --splitting_nvd                         32
% 2.67/1.00  --sub_typing                            true
% 2.67/1.00  --prep_gs_sim                           true
% 2.67/1.00  --prep_unflatten                        true
% 2.67/1.00  --prep_res_sim                          true
% 2.67/1.00  --prep_upred                            true
% 2.67/1.00  --prep_sem_filter                       exhaustive
% 2.67/1.00  --prep_sem_filter_out                   false
% 2.67/1.00  --pred_elim                             true
% 2.67/1.00  --res_sim_input                         true
% 2.67/1.00  --eq_ax_congr_red                       true
% 2.67/1.00  --pure_diseq_elim                       true
% 2.67/1.00  --brand_transform                       false
% 2.67/1.00  --non_eq_to_eq                          false
% 2.67/1.00  --prep_def_merge                        true
% 2.67/1.00  --prep_def_merge_prop_impl              false
% 2.67/1.00  --prep_def_merge_mbd                    true
% 2.67/1.00  --prep_def_merge_tr_red                 false
% 2.67/1.00  --prep_def_merge_tr_cl                  false
% 2.67/1.00  --smt_preprocessing                     true
% 2.67/1.00  --smt_ac_axioms                         fast
% 2.67/1.00  --preprocessed_out                      false
% 2.67/1.00  --preprocessed_stats                    false
% 2.67/1.00  
% 2.67/1.00  ------ Abstraction refinement Options
% 2.67/1.00  
% 2.67/1.00  --abstr_ref                             []
% 2.67/1.00  --abstr_ref_prep                        false
% 2.67/1.00  --abstr_ref_until_sat                   false
% 2.67/1.00  --abstr_ref_sig_restrict                funpre
% 2.67/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/1.00  --abstr_ref_under                       []
% 2.67/1.00  
% 2.67/1.00  ------ SAT Options
% 2.67/1.00  
% 2.67/1.00  --sat_mode                              false
% 2.67/1.00  --sat_fm_restart_options                ""
% 2.67/1.00  --sat_gr_def                            false
% 2.67/1.00  --sat_epr_types                         true
% 2.67/1.00  --sat_non_cyclic_types                  false
% 2.67/1.00  --sat_finite_models                     false
% 2.67/1.00  --sat_fm_lemmas                         false
% 2.67/1.00  --sat_fm_prep                           false
% 2.67/1.00  --sat_fm_uc_incr                        true
% 2.67/1.00  --sat_out_model                         small
% 2.67/1.00  --sat_out_clauses                       false
% 2.67/1.00  
% 2.67/1.00  ------ QBF Options
% 2.67/1.00  
% 2.67/1.00  --qbf_mode                              false
% 2.67/1.00  --qbf_elim_univ                         false
% 2.67/1.00  --qbf_dom_inst                          none
% 2.67/1.00  --qbf_dom_pre_inst                      false
% 2.67/1.00  --qbf_sk_in                             false
% 2.67/1.00  --qbf_pred_elim                         true
% 2.67/1.00  --qbf_split                             512
% 2.67/1.00  
% 2.67/1.00  ------ BMC1 Options
% 2.67/1.00  
% 2.67/1.00  --bmc1_incremental                      false
% 2.67/1.00  --bmc1_axioms                           reachable_all
% 2.67/1.00  --bmc1_min_bound                        0
% 2.67/1.00  --bmc1_max_bound                        -1
% 2.67/1.00  --bmc1_max_bound_default                -1
% 2.67/1.01  --bmc1_symbol_reachability              true
% 2.67/1.01  --bmc1_property_lemmas                  false
% 2.67/1.01  --bmc1_k_induction                      false
% 2.67/1.01  --bmc1_non_equiv_states                 false
% 2.67/1.01  --bmc1_deadlock                         false
% 2.67/1.01  --bmc1_ucm                              false
% 2.67/1.01  --bmc1_add_unsat_core                   none
% 2.67/1.01  --bmc1_unsat_core_children              false
% 2.67/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/1.01  --bmc1_out_stat                         full
% 2.67/1.01  --bmc1_ground_init                      false
% 2.67/1.01  --bmc1_pre_inst_next_state              false
% 2.67/1.01  --bmc1_pre_inst_state                   false
% 2.67/1.01  --bmc1_pre_inst_reach_state             false
% 2.67/1.01  --bmc1_out_unsat_core                   false
% 2.67/1.01  --bmc1_aig_witness_out                  false
% 2.67/1.01  --bmc1_verbose                          false
% 2.67/1.01  --bmc1_dump_clauses_tptp                false
% 2.67/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.67/1.01  --bmc1_dump_file                        -
% 2.67/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.67/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.67/1.01  --bmc1_ucm_extend_mode                  1
% 2.67/1.01  --bmc1_ucm_init_mode                    2
% 2.67/1.01  --bmc1_ucm_cone_mode                    none
% 2.67/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.67/1.01  --bmc1_ucm_relax_model                  4
% 2.67/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.67/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/1.01  --bmc1_ucm_layered_model                none
% 2.67/1.01  --bmc1_ucm_max_lemma_size               10
% 2.67/1.01  
% 2.67/1.01  ------ AIG Options
% 2.67/1.01  
% 2.67/1.01  --aig_mode                              false
% 2.67/1.01  
% 2.67/1.01  ------ Instantiation Options
% 2.67/1.01  
% 2.67/1.01  --instantiation_flag                    true
% 2.67/1.01  --inst_sos_flag                         false
% 2.67/1.01  --inst_sos_phase                        true
% 2.67/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/1.01  --inst_lit_sel_side                     none
% 2.67/1.01  --inst_solver_per_active                1400
% 2.67/1.01  --inst_solver_calls_frac                1.
% 2.67/1.01  --inst_passive_queue_type               priority_queues
% 2.67/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/1.01  --inst_passive_queues_freq              [25;2]
% 2.67/1.01  --inst_dismatching                      true
% 2.67/1.01  --inst_eager_unprocessed_to_passive     true
% 2.67/1.01  --inst_prop_sim_given                   true
% 2.67/1.01  --inst_prop_sim_new                     false
% 2.67/1.01  --inst_subs_new                         false
% 2.67/1.01  --inst_eq_res_simp                      false
% 2.67/1.01  --inst_subs_given                       false
% 2.67/1.01  --inst_orphan_elimination               true
% 2.67/1.01  --inst_learning_loop_flag               true
% 2.67/1.01  --inst_learning_start                   3000
% 2.67/1.01  --inst_learning_factor                  2
% 2.67/1.01  --inst_start_prop_sim_after_learn       3
% 2.67/1.01  --inst_sel_renew                        solver
% 2.67/1.01  --inst_lit_activity_flag                true
% 2.67/1.01  --inst_restr_to_given                   false
% 2.67/1.01  --inst_activity_threshold               500
% 2.67/1.01  --inst_out_proof                        true
% 2.67/1.01  
% 2.67/1.01  ------ Resolution Options
% 2.67/1.01  
% 2.67/1.01  --resolution_flag                       false
% 2.67/1.01  --res_lit_sel                           adaptive
% 2.67/1.01  --res_lit_sel_side                      none
% 2.67/1.01  --res_ordering                          kbo
% 2.67/1.01  --res_to_prop_solver                    active
% 2.67/1.01  --res_prop_simpl_new                    false
% 2.67/1.01  --res_prop_simpl_given                  true
% 2.67/1.01  --res_passive_queue_type                priority_queues
% 2.67/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/1.01  --res_passive_queues_freq               [15;5]
% 2.67/1.01  --res_forward_subs                      full
% 2.67/1.01  --res_backward_subs                     full
% 2.67/1.01  --res_forward_subs_resolution           true
% 2.67/1.01  --res_backward_subs_resolution          true
% 2.67/1.01  --res_orphan_elimination                true
% 2.67/1.01  --res_time_limit                        2.
% 2.67/1.01  --res_out_proof                         true
% 2.67/1.01  
% 2.67/1.01  ------ Superposition Options
% 2.67/1.01  
% 2.67/1.01  --superposition_flag                    true
% 2.67/1.01  --sup_passive_queue_type                priority_queues
% 2.67/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.67/1.01  --demod_completeness_check              fast
% 2.67/1.01  --demod_use_ground                      true
% 2.67/1.01  --sup_to_prop_solver                    passive
% 2.67/1.01  --sup_prop_simpl_new                    true
% 2.67/1.01  --sup_prop_simpl_given                  true
% 2.67/1.01  --sup_fun_splitting                     false
% 2.67/1.01  --sup_smt_interval                      50000
% 2.67/1.01  
% 2.67/1.01  ------ Superposition Simplification Setup
% 2.67/1.01  
% 2.67/1.01  --sup_indices_passive                   []
% 2.67/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.01  --sup_full_bw                           [BwDemod]
% 2.67/1.01  --sup_immed_triv                        [TrivRules]
% 2.67/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.01  --sup_immed_bw_main                     []
% 2.67/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.01  
% 2.67/1.01  ------ Combination Options
% 2.67/1.01  
% 2.67/1.01  --comb_res_mult                         3
% 2.67/1.01  --comb_sup_mult                         2
% 2.67/1.01  --comb_inst_mult                        10
% 2.67/1.01  
% 2.67/1.01  ------ Debug Options
% 2.67/1.01  
% 2.67/1.01  --dbg_backtrace                         false
% 2.67/1.01  --dbg_dump_prop_clauses                 false
% 2.67/1.01  --dbg_dump_prop_clauses_file            -
% 2.67/1.01  --dbg_out_stat                          false
% 2.67/1.01  
% 2.67/1.01  
% 2.67/1.01  
% 2.67/1.01  
% 2.67/1.01  ------ Proving...
% 2.67/1.01  
% 2.67/1.01  
% 2.67/1.01  % SZS status Theorem for theBenchmark.p
% 2.67/1.01  
% 2.67/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.67/1.01  
% 2.67/1.01  fof(f14,conjecture,(
% 2.67/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f15,negated_conjecture,(
% 2.67/1.01    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.67/1.01    inference(negated_conjecture,[],[f14])).
% 2.67/1.01  
% 2.67/1.01  fof(f36,plain,(
% 2.67/1.01    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.67/1.01    inference(ennf_transformation,[],[f15])).
% 2.67/1.01  
% 2.67/1.01  fof(f37,plain,(
% 2.67/1.01    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.67/1.01    inference(flattening,[],[f36])).
% 2.67/1.01  
% 2.67/1.01  fof(f41,plain,(
% 2.67/1.01    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.67/1.01    introduced(choice_axiom,[])).
% 2.67/1.01  
% 2.67/1.01  fof(f40,plain,(
% 2.67/1.01    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.67/1.01    introduced(choice_axiom,[])).
% 2.67/1.01  
% 2.67/1.01  fof(f39,plain,(
% 2.67/1.01    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.67/1.01    introduced(choice_axiom,[])).
% 2.67/1.01  
% 2.67/1.01  fof(f42,plain,(
% 2.67/1.01    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.67/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f41,f40,f39])).
% 2.67/1.01  
% 2.67/1.01  fof(f64,plain,(
% 2.67/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.67/1.01    inference(cnf_transformation,[],[f42])).
% 2.67/1.01  
% 2.67/1.01  fof(f11,axiom,(
% 2.67/1.01    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f31,plain,(
% 2.67/1.01    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.67/1.01    inference(ennf_transformation,[],[f11])).
% 2.67/1.01  
% 2.67/1.01  fof(f56,plain,(
% 2.67/1.01    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f31])).
% 2.67/1.01  
% 2.67/1.01  fof(f59,plain,(
% 2.67/1.01    l1_struct_0(sK0)),
% 2.67/1.01    inference(cnf_transformation,[],[f42])).
% 2.67/1.01  
% 2.67/1.01  fof(f61,plain,(
% 2.67/1.01    l1_struct_0(sK1)),
% 2.67/1.01    inference(cnf_transformation,[],[f42])).
% 2.67/1.01  
% 2.67/1.01  fof(f8,axiom,(
% 2.67/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k4_relat_1(X2) = k3_relset_1(X0,X1,X2))),
% 2.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f26,plain,(
% 2.67/1.01    ! [X0,X1,X2] : (k4_relat_1(X2) = k3_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.01    inference(ennf_transformation,[],[f8])).
% 2.67/1.01  
% 2.67/1.01  fof(f51,plain,(
% 2.67/1.01    ( ! [X2,X0,X1] : (k4_relat_1(X2) = k3_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/1.01    inference(cnf_transformation,[],[f26])).
% 2.67/1.01  
% 2.67/1.01  fof(f3,axiom,(
% 2.67/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f21,plain,(
% 2.67/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.01    inference(ennf_transformation,[],[f3])).
% 2.67/1.01  
% 2.67/1.01  fof(f46,plain,(
% 2.67/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/1.01    inference(cnf_transformation,[],[f21])).
% 2.67/1.01  
% 2.67/1.01  fof(f1,axiom,(
% 2.67/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(X0) = k4_relat_1(X0)))),
% 2.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f17,plain,(
% 2.67/1.01    ! [X0] : ((k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.67/1.01    inference(ennf_transformation,[],[f1])).
% 2.67/1.01  
% 2.67/1.01  fof(f18,plain,(
% 2.67/1.01    ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.67/1.01    inference(flattening,[],[f17])).
% 2.67/1.01  
% 2.67/1.01  fof(f43,plain,(
% 2.67/1.01    ( ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f18])).
% 2.67/1.01  
% 2.67/1.01  fof(f66,plain,(
% 2.67/1.01    v2_funct_1(sK2)),
% 2.67/1.01    inference(cnf_transformation,[],[f42])).
% 2.67/1.01  
% 2.67/1.01  fof(f62,plain,(
% 2.67/1.01    v1_funct_1(sK2)),
% 2.67/1.01    inference(cnf_transformation,[],[f42])).
% 2.67/1.01  
% 2.67/1.01  fof(f7,axiom,(
% 2.67/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f25,plain,(
% 2.67/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.01    inference(ennf_transformation,[],[f7])).
% 2.67/1.01  
% 2.67/1.01  fof(f50,plain,(
% 2.67/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/1.01    inference(cnf_transformation,[],[f25])).
% 2.67/1.01  
% 2.67/1.01  fof(f65,plain,(
% 2.67/1.01    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.67/1.01    inference(cnf_transformation,[],[f42])).
% 2.67/1.01  
% 2.67/1.01  fof(f63,plain,(
% 2.67/1.01    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.67/1.01    inference(cnf_transformation,[],[f42])).
% 2.67/1.01  
% 2.67/1.01  fof(f9,axiom,(
% 2.67/1.01    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f27,plain,(
% 2.67/1.01    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.67/1.01    inference(ennf_transformation,[],[f9])).
% 2.67/1.01  
% 2.67/1.01  fof(f28,plain,(
% 2.67/1.01    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.67/1.01    inference(flattening,[],[f27])).
% 2.67/1.01  
% 2.67/1.01  fof(f53,plain,(
% 2.67/1.01    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f28])).
% 2.67/1.01  
% 2.67/1.01  fof(f12,axiom,(
% 2.67/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 2.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f32,plain,(
% 2.67/1.01    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.67/1.01    inference(ennf_transformation,[],[f12])).
% 2.67/1.01  
% 2.67/1.01  fof(f33,plain,(
% 2.67/1.01    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.67/1.01    inference(flattening,[],[f32])).
% 2.67/1.01  
% 2.67/1.01  fof(f57,plain,(
% 2.67/1.01    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f33])).
% 2.67/1.01  
% 2.67/1.01  fof(f60,plain,(
% 2.67/1.01    ~v2_struct_0(sK1)),
% 2.67/1.01    inference(cnf_transformation,[],[f42])).
% 2.67/1.01  
% 2.67/1.01  fof(f4,axiom,(
% 2.67/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f16,plain,(
% 2.67/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.67/1.01    inference(pure_predicate_removal,[],[f4])).
% 2.67/1.01  
% 2.67/1.01  fof(f22,plain,(
% 2.67/1.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.01    inference(ennf_transformation,[],[f16])).
% 2.67/1.01  
% 2.67/1.01  fof(f47,plain,(
% 2.67/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/1.01    inference(cnf_transformation,[],[f22])).
% 2.67/1.01  
% 2.67/1.01  fof(f10,axiom,(
% 2.67/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f29,plain,(
% 2.67/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.67/1.01    inference(ennf_transformation,[],[f10])).
% 2.67/1.01  
% 2.67/1.01  fof(f30,plain,(
% 2.67/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.67/1.01    inference(flattening,[],[f29])).
% 2.67/1.01  
% 2.67/1.01  fof(f38,plain,(
% 2.67/1.01    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.67/1.01    inference(nnf_transformation,[],[f30])).
% 2.67/1.01  
% 2.67/1.01  fof(f54,plain,(
% 2.67/1.01    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f38])).
% 2.67/1.01  
% 2.67/1.01  fof(f5,axiom,(
% 2.67/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f23,plain,(
% 2.67/1.01    ! [X0,X1,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.01    inference(ennf_transformation,[],[f5])).
% 2.67/1.01  
% 2.67/1.01  fof(f48,plain,(
% 2.67/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/1.01    inference(cnf_transformation,[],[f23])).
% 2.67/1.01  
% 2.67/1.01  fof(f2,axiom,(
% 2.67/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f19,plain,(
% 2.67/1.01    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.67/1.01    inference(ennf_transformation,[],[f2])).
% 2.67/1.01  
% 2.67/1.01  fof(f20,plain,(
% 2.67/1.01    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.67/1.01    inference(flattening,[],[f19])).
% 2.67/1.01  
% 2.67/1.01  fof(f45,plain,(
% 2.67/1.01    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f20])).
% 2.67/1.01  
% 2.67/1.01  fof(f6,axiom,(
% 2.67/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f24,plain,(
% 2.67/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.01    inference(ennf_transformation,[],[f6])).
% 2.67/1.01  
% 2.67/1.01  fof(f49,plain,(
% 2.67/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/1.01    inference(cnf_transformation,[],[f24])).
% 2.67/1.01  
% 2.67/1.01  fof(f44,plain,(
% 2.67/1.01    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f20])).
% 2.67/1.01  
% 2.67/1.01  fof(f67,plain,(
% 2.67/1.01    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 2.67/1.01    inference(cnf_transformation,[],[f42])).
% 2.67/1.01  
% 2.67/1.01  fof(f13,axiom,(
% 2.67/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.67/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.01  
% 2.67/1.01  fof(f34,plain,(
% 2.67/1.01    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.67/1.01    inference(ennf_transformation,[],[f13])).
% 2.67/1.01  
% 2.67/1.01  fof(f35,plain,(
% 2.67/1.01    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.67/1.01    inference(flattening,[],[f34])).
% 2.67/1.01  
% 2.67/1.01  fof(f58,plain,(
% 2.67/1.01    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.67/1.01    inference(cnf_transformation,[],[f35])).
% 2.67/1.01  
% 2.67/1.01  cnf(c_19,negated_conjecture,
% 2.67/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.67/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_599,negated_conjecture,
% 2.67/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_19]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_829,plain,
% 2.67/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_599]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_13,plain,
% 2.67/1.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.67/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_24,negated_conjecture,
% 2.67/1.01      ( l1_struct_0(sK0) ),
% 2.67/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_280,plain,
% 2.67/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.67/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_281,plain,
% 2.67/1.01      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.67/1.01      inference(unflattening,[status(thm)],[c_280]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_597,plain,
% 2.67/1.01      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_281]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_22,negated_conjecture,
% 2.67/1.01      ( l1_struct_0(sK1) ),
% 2.67/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_275,plain,
% 2.67/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.67/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_276,plain,
% 2.67/1.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.67/1.01      inference(unflattening,[status(thm)],[c_275]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_598,plain,
% 2.67/1.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_276]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_842,plain,
% 2.67/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.67/1.01      inference(light_normalisation,[status(thm)],[c_829,c_597,c_598]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_8,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.01      | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
% 2.67/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_602,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 2.67/1.01      | k3_relset_1(X0_56,X1_56,X0_53) = k4_relat_1(X0_53) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_828,plain,
% 2.67/1.01      ( k3_relset_1(X0_56,X1_56,X0_53) = k4_relat_1(X0_53)
% 2.67/1.01      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_602]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1124,plain,
% 2.67/1.01      ( k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k4_relat_1(sK2) ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_842,c_828]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_3,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.01      | v1_relat_1(X0) ),
% 2.67/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_0,plain,
% 2.67/1.01      ( ~ v1_relat_1(X0)
% 2.67/1.01      | ~ v1_funct_1(X0)
% 2.67/1.01      | ~ v2_funct_1(X0)
% 2.67/1.01      | k4_relat_1(X0) = k2_funct_1(X0) ),
% 2.67/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_17,negated_conjecture,
% 2.67/1.01      ( v2_funct_1(sK2) ),
% 2.67/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_448,plain,
% 2.67/1.01      ( ~ v1_relat_1(X0)
% 2.67/1.01      | ~ v1_funct_1(X0)
% 2.67/1.01      | k4_relat_1(X0) = k2_funct_1(X0)
% 2.67/1.01      | sK2 != X0 ),
% 2.67/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_17]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_449,plain,
% 2.67/1.01      ( ~ v1_relat_1(sK2)
% 2.67/1.01      | ~ v1_funct_1(sK2)
% 2.67/1.01      | k4_relat_1(sK2) = k2_funct_1(sK2) ),
% 2.67/1.01      inference(unflattening,[status(thm)],[c_448]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_21,negated_conjecture,
% 2.67/1.01      ( v1_funct_1(sK2) ),
% 2.67/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_451,plain,
% 2.67/1.01      ( ~ v1_relat_1(sK2) | k4_relat_1(sK2) = k2_funct_1(sK2) ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_449,c_21]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_471,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.01      | k4_relat_1(sK2) = k2_funct_1(sK2)
% 2.67/1.01      | sK2 != X0 ),
% 2.67/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_451]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_472,plain,
% 2.67/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.67/1.01      | k4_relat_1(sK2) = k2_funct_1(sK2) ),
% 2.67/1.01      inference(unflattening,[status(thm)],[c_471]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_594,plain,
% 2.67/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 2.67/1.01      | k4_relat_1(sK2) = k2_funct_1(sK2) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_472]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_832,plain,
% 2.67/1.01      ( k4_relat_1(sK2) = k2_funct_1(sK2)
% 2.67/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_594]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_929,plain,
% 2.67/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.67/1.01      | k4_relat_1(sK2) = k2_funct_1(sK2) ),
% 2.67/1.01      inference(instantiation,[status(thm)],[c_594]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_966,plain,
% 2.67/1.01      ( k4_relat_1(sK2) = k2_funct_1(sK2) ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_832,c_19,c_929]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1126,plain,
% 2.67/1.01      ( k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.67/1.01      inference(light_normalisation,[status(thm)],[c_1124,c_966]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_7,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.67/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_603,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 2.67/1.01      | k2_relset_1(X0_56,X1_56,X0_53) = k2_relat_1(X0_53) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_827,plain,
% 2.67/1.01      ( k2_relset_1(X0_56,X1_56,X0_53) = k2_relat_1(X0_53)
% 2.67/1.01      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_603]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1110,plain,
% 2.67/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_842,c_827]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_18,negated_conjecture,
% 2.67/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.67/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_600,negated_conjecture,
% 2.67/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_18]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_839,plain,
% 2.67/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.67/1.01      inference(light_normalisation,[status(thm)],[c_600,c_597,c_598]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1177,plain,
% 2.67/1.01      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.67/1.01      inference(demodulation,[status(thm)],[c_1110,c_839]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_20,negated_conjecture,
% 2.67/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.67/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_9,plain,
% 2.67/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.67/1.01      | v1_partfun1(X0,X1)
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.01      | v1_xboole_0(X2)
% 2.67/1.01      | ~ v1_funct_1(X0) ),
% 2.67/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_14,plain,
% 2.67/1.01      ( v2_struct_0(X0)
% 2.67/1.01      | ~ l1_struct_0(X0)
% 2.67/1.01      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 2.67/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_23,negated_conjecture,
% 2.67/1.01      ( ~ v2_struct_0(sK1) ),
% 2.67/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_262,plain,
% 2.67/1.01      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 2.67/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_263,plain,
% 2.67/1.01      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.67/1.01      inference(unflattening,[status(thm)],[c_262]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_36,plain,
% 2.67/1.01      ( v2_struct_0(sK1)
% 2.67/1.01      | ~ l1_struct_0(sK1)
% 2.67/1.01      | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.67/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_265,plain,
% 2.67/1.01      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_263,c_23,c_22,c_36]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_287,plain,
% 2.67/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.67/1.01      | v1_partfun1(X0,X1)
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.01      | ~ v1_funct_1(X0)
% 2.67/1.01      | k2_struct_0(sK1) != X2 ),
% 2.67/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_265]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_288,plain,
% 2.67/1.01      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 2.67/1.01      | v1_partfun1(X0,X1)
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 2.67/1.01      | ~ v1_funct_1(X0) ),
% 2.67/1.01      inference(unflattening,[status(thm)],[c_287]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_4,plain,
% 2.67/1.01      ( v4_relat_1(X0,X1)
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.67/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_12,plain,
% 2.67/1.01      ( ~ v1_partfun1(X0,X1)
% 2.67/1.01      | ~ v4_relat_1(X0,X1)
% 2.67/1.01      | ~ v1_relat_1(X0)
% 2.67/1.01      | k1_relat_1(X0) = X1 ),
% 2.67/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_310,plain,
% 2.67/1.01      ( ~ v1_partfun1(X0,X1)
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.01      | ~ v1_relat_1(X0)
% 2.67/1.01      | k1_relat_1(X0) = X1 ),
% 2.67/1.01      inference(resolution,[status(thm)],[c_4,c_12]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_314,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.01      | ~ v1_partfun1(X0,X1)
% 2.67/1.01      | k1_relat_1(X0) = X1 ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_310,c_12,c_4,c_3]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_315,plain,
% 2.67/1.01      ( ~ v1_partfun1(X0,X1)
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.01      | k1_relat_1(X0) = X1 ),
% 2.67/1.01      inference(renaming,[status(thm)],[c_314]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_354,plain,
% 2.67/1.01      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 2.67/1.01      | ~ v1_funct_1(X0)
% 2.67/1.01      | k1_relat_1(X0) = X1 ),
% 2.67/1.01      inference(resolution,[status(thm)],[c_288,c_315]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_393,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 2.67/1.01      | ~ v1_funct_1(X0)
% 2.67/1.01      | u1_struct_0(sK0) != X1
% 2.67/1.01      | u1_struct_0(sK1) != k2_struct_0(sK1)
% 2.67/1.01      | k1_relat_1(X0) = X1
% 2.67/1.01      | sK2 != X0 ),
% 2.67/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_354]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_394,plain,
% 2.67/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
% 2.67/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
% 2.67/1.01      | ~ v1_funct_1(sK2)
% 2.67/1.01      | u1_struct_0(sK1) != k2_struct_0(sK1)
% 2.67/1.01      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 2.67/1.01      inference(unflattening,[status(thm)],[c_393]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_39,plain,
% 2.67/1.01      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.67/1.01      inference(instantiation,[status(thm)],[c_13]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_398,plain,
% 2.67/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0)))
% 2.67/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
% 2.67/1.01      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_394,c_22,c_21,c_39]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_595,plain,
% 2.67/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0_56)))
% 2.67/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
% 2.67/1.01      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_398]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_607,plain,
% 2.67/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
% 2.67/1.01      | sP0_iProver_split
% 2.67/1.01      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 2.67/1.01      inference(splitting,
% 2.67/1.01                [splitting(split),new_symbols(definition,[])],
% 2.67/1.01                [c_595]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_830,plain,
% 2.67/1.01      ( k1_relat_1(sK2) = u1_struct_0(sK0)
% 2.67/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.67/1.01      | sP0_iProver_split = iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_607]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_882,plain,
% 2.67/1.01      ( u1_struct_0(sK0) = k1_relat_1(sK2)
% 2.67/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.67/1.01      | sP0_iProver_split = iProver_top ),
% 2.67/1.01      inference(light_normalisation,[status(thm)],[c_830,c_597]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_883,plain,
% 2.67/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.67/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.67/1.01      | sP0_iProver_split = iProver_top ),
% 2.67/1.01      inference(demodulation,[status(thm)],[c_882,c_597]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_887,plain,
% 2.67/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.67/1.01      | sP0_iProver_split = iProver_top ),
% 2.67/1.01      inference(forward_subsumption_resolution,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_883,c_842]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_895,plain,
% 2.67/1.01      ( sP0_iProver_split | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.67/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_887]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_606,plain,
% 2.67/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X0_56)))
% 2.67/1.01      | ~ sP0_iProver_split ),
% 2.67/1.01      inference(splitting,
% 2.67/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.67/1.01                [c_595]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_918,plain,
% 2.67/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.67/1.01      | ~ sP0_iProver_split ),
% 2.67/1.01      inference(instantiation,[status(thm)],[c_606]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1566,plain,
% 2.67/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_887,c_19,c_895,c_918]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1730,plain,
% 2.67/1.01      ( k3_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.67/1.01      inference(light_normalisation,[status(thm)],[c_1126,c_1177,c_1566]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_5,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.01      | m1_subset_1(k3_relset_1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.67/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_605,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 2.67/1.01      | m1_subset_1(k3_relset_1(X0_56,X1_56,X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_56,X0_56))) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_825,plain,
% 2.67/1.01      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
% 2.67/1.01      | m1_subset_1(k3_relset_1(X0_56,X1_56,X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_56,X0_56))) = iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_605]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1732,plain,
% 2.67/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 2.67/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_1730,c_825]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1226,plain,
% 2.67/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.67/1.01      inference(demodulation,[status(thm)],[c_1177,c_842]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1569,plain,
% 2.67/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 2.67/1.01      inference(demodulation,[status(thm)],[c_1566,c_1226]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1870,plain,
% 2.67/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_1732,c_1569]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1877,plain,
% 2.67/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_1870,c_827]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1,plain,
% 2.67/1.01      ( ~ v1_relat_1(X0)
% 2.67/1.01      | ~ v1_funct_1(X0)
% 2.67/1.01      | ~ v2_funct_1(X0)
% 2.67/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.67/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_434,plain,
% 2.67/1.01      ( ~ v1_relat_1(X0)
% 2.67/1.01      | ~ v1_funct_1(X0)
% 2.67/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.67/1.01      | sK2 != X0 ),
% 2.67/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_17]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_435,plain,
% 2.67/1.01      ( ~ v1_relat_1(sK2)
% 2.67/1.01      | ~ v1_funct_1(sK2)
% 2.67/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.67/1.01      inference(unflattening,[status(thm)],[c_434]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_437,plain,
% 2.67/1.01      ( ~ v1_relat_1(sK2)
% 2.67/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_435,c_21]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_483,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.67/1.01      | sK2 != X0 ),
% 2.67/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_437]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_484,plain,
% 2.67/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.67/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.67/1.01      inference(unflattening,[status(thm)],[c_483]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_593,plain,
% 2.67/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 2.67/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_484]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_833,plain,
% 2.67/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.67/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_593]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_924,plain,
% 2.67/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.67/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.67/1.01      inference(instantiation,[status(thm)],[c_593]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1353,plain,
% 2.67/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_833,c_19,c_924]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1891,plain,
% 2.67/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.67/1.01      inference(light_normalisation,[status(thm)],[c_1877,c_1353]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_6,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.67/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_604,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 2.67/1.01      | k1_relset_1(X0_56,X1_56,X0_53) = k1_relat_1(X0_53) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_826,plain,
% 2.67/1.01      ( k1_relset_1(X0_56,X1_56,X0_53) = k1_relat_1(X0_53)
% 2.67/1.01      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_604]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1026,plain,
% 2.67/1.01      ( k1_relset_1(X0_56,X1_56,k3_relset_1(X1_56,X0_56,X0_53)) = k1_relat_1(k3_relset_1(X1_56,X0_56,X0_53))
% 2.67/1.01      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_56,X0_56))) != iProver_top ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_825,c_826]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1408,plain,
% 2.67/1.01      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k1_relat_1(k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
% 2.67/1.01      inference(superposition,[status(thm)],[c_1226,c_1026]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_2,plain,
% 2.67/1.01      ( ~ v1_relat_1(X0)
% 2.67/1.01      | ~ v1_funct_1(X0)
% 2.67/1.01      | ~ v2_funct_1(X0)
% 2.67/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.67/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_420,plain,
% 2.67/1.01      ( ~ v1_relat_1(X0)
% 2.67/1.01      | ~ v1_funct_1(X0)
% 2.67/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.67/1.01      | sK2 != X0 ),
% 2.67/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_17]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_421,plain,
% 2.67/1.01      ( ~ v1_relat_1(sK2)
% 2.67/1.01      | ~ v1_funct_1(sK2)
% 2.67/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.67/1.01      inference(unflattening,[status(thm)],[c_420]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_423,plain,
% 2.67/1.01      ( ~ v1_relat_1(sK2)
% 2.67/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_421,c_21]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_495,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.67/1.01      | sK2 != X0 ),
% 2.67/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_423]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_496,plain,
% 2.67/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.67/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.67/1.01      inference(unflattening,[status(thm)],[c_495]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_592,plain,
% 2.67/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 2.67/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_496]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_834,plain,
% 2.67/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.67/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top ),
% 2.67/1.01      inference(predicate_to_equality,[status(thm)],[c_592]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_921,plain,
% 2.67/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.67/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.67/1.01      inference(instantiation,[status(thm)],[c_592]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1562,plain,
% 2.67/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_834,c_19,c_921]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1824,plain,
% 2.67/1.01      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.67/1.01      inference(light_normalisation,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_1408,c_1562,c_1566,c_1730]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_16,negated_conjecture,
% 2.67/1.01      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.67/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.67/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_601,negated_conjecture,
% 2.67/1.01      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.67/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_16]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_15,plain,
% 2.67/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.67/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.01      | ~ v1_funct_1(X0)
% 2.67/1.01      | ~ v2_funct_1(X0)
% 2.67/1.01      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.67/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.67/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_382,plain,
% 2.67/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.01      | ~ v1_funct_1(X0)
% 2.67/1.01      | ~ v2_funct_1(X0)
% 2.67/1.01      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.67/1.01      | k2_relset_1(X1,X2,X0) != X2
% 2.67/1.01      | u1_struct_0(sK0) != X1
% 2.67/1.01      | u1_struct_0(sK1) != X2
% 2.67/1.01      | sK2 != X0 ),
% 2.67/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_383,plain,
% 2.67/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.67/1.01      | ~ v1_funct_1(sK2)
% 2.67/1.01      | ~ v2_funct_1(sK2)
% 2.67/1.01      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.67/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 2.67/1.01      inference(unflattening,[status(thm)],[c_382]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_385,plain,
% 2.67/1.01      ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.67/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 2.67/1.01      inference(global_propositional_subsumption,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_383,c_21,c_19,c_17]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_596,plain,
% 2.67/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 2.67/1.01      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.67/1.01      inference(subtyping,[status(esa)],[c_385]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_874,plain,
% 2.67/1.01      ( k2_struct_0(sK1) != k2_struct_0(sK1)
% 2.67/1.01      | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.67/1.01      inference(light_normalisation,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_596,c_597,c_598,c_839]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_875,plain,
% 2.67/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.67/1.01      inference(equality_resolution_simp,[status(thm)],[c_874]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_890,plain,
% 2.67/1.01      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.67/1.01      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
% 2.67/1.01      inference(light_normalisation,
% 2.67/1.01                [status(thm)],
% 2.67/1.01                [c_601,c_597,c_598,c_875]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1227,plain,
% 2.67/1.01      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.67/1.01      | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 2.67/1.01      inference(demodulation,[status(thm)],[c_1177,c_890]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(c_1573,plain,
% 2.67/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2)
% 2.67/1.01      | k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 2.67/1.01      inference(demodulation,[status(thm)],[c_1566,c_1227]) ).
% 2.67/1.01  
% 2.67/1.01  cnf(contradiction,plain,
% 2.67/1.01      ( $false ),
% 2.67/1.01      inference(minisat,[status(thm)],[c_1891,c_1824,c_1573]) ).
% 2.67/1.01  
% 2.67/1.01  
% 2.67/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.67/1.01  
% 2.67/1.01  ------                               Statistics
% 2.67/1.01  
% 2.67/1.01  ------ General
% 2.67/1.01  
% 2.67/1.01  abstr_ref_over_cycles:                  0
% 2.67/1.01  abstr_ref_under_cycles:                 0
% 2.67/1.01  gc_basic_clause_elim:                   0
% 2.67/1.01  forced_gc_time:                         0
% 2.67/1.01  parsing_time:                           0.017
% 2.67/1.01  unif_index_cands_time:                  0.
% 2.67/1.01  unif_index_add_time:                    0.
% 2.67/1.01  orderings_time:                         0.
% 2.67/1.01  out_proof_time:                         0.025
% 2.67/1.01  total_time:                             0.153
% 2.67/1.01  num_of_symbols:                         59
% 2.67/1.01  num_of_terms:                           1814
% 2.67/1.01  
% 2.67/1.01  ------ Preprocessing
% 2.67/1.01  
% 2.67/1.01  num_of_splits:                          1
% 2.67/1.01  num_of_split_atoms:                     1
% 2.67/1.01  num_of_reused_defs:                     0
% 2.67/1.01  num_eq_ax_congr_red:                    16
% 2.67/1.01  num_of_sem_filtered_clauses:            1
% 2.67/1.01  num_of_subtypes:                        5
% 2.67/1.01  monotx_restored_types:                  0
% 2.67/1.01  sat_num_of_epr_types:                   0
% 2.67/1.01  sat_num_of_non_cyclic_types:            0
% 2.67/1.01  sat_guarded_non_collapsed_types:        0
% 2.67/1.01  num_pure_diseq_elim:                    0
% 2.67/1.01  simp_replaced_by:                       0
% 2.67/1.01  res_preprocessed:                       101
% 2.67/1.01  prep_upred:                             0
% 2.67/1.01  prep_unflattend:                        19
% 2.67/1.01  smt_new_axioms:                         0
% 2.67/1.01  pred_elim_cands:                        1
% 2.67/1.01  pred_elim:                              9
% 2.67/1.01  pred_elim_cl:                           10
% 2.67/1.01  pred_elim_cycles:                       11
% 2.67/1.01  merged_defs:                            0
% 2.67/1.01  merged_defs_ncl:                        0
% 2.67/1.01  bin_hyper_res:                          0
% 2.67/1.01  prep_cycles:                            4
% 2.67/1.01  pred_elim_time:                         0.008
% 2.67/1.01  splitting_time:                         0.
% 2.67/1.01  sem_filter_time:                        0.
% 2.67/1.01  monotx_time:                            0.
% 2.67/1.01  subtype_inf_time:                       0.
% 2.67/1.01  
% 2.67/1.01  ------ Problem properties
% 2.67/1.01  
% 2.67/1.01  clauses:                                15
% 2.67/1.01  conjectures:                            3
% 2.67/1.01  epr:                                    0
% 2.67/1.01  horn:                                   14
% 2.67/1.01  ground:                                 7
% 2.67/1.01  unary:                                  4
% 2.67/1.01  binary:                                 10
% 2.67/1.01  lits:                                   27
% 2.67/1.01  lits_eq:                                14
% 2.67/1.01  fd_pure:                                0
% 2.67/1.01  fd_pseudo:                              0
% 2.67/1.01  fd_cond:                                0
% 2.67/1.01  fd_pseudo_cond:                         0
% 2.67/1.01  ac_symbols:                             0
% 2.67/1.01  
% 2.67/1.01  ------ Propositional Solver
% 2.67/1.01  
% 2.67/1.01  prop_solver_calls:                      30
% 2.67/1.01  prop_fast_solver_calls:                 551
% 2.67/1.01  smt_solver_calls:                       0
% 2.67/1.01  smt_fast_solver_calls:                  0
% 2.67/1.01  prop_num_of_clauses:                    677
% 2.67/1.01  prop_preprocess_simplified:             2801
% 2.67/1.01  prop_fo_subsumed:                       16
% 2.67/1.01  prop_solver_time:                       0.
% 2.67/1.01  smt_solver_time:                        0.
% 2.67/1.01  smt_fast_solver_time:                   0.
% 2.67/1.01  prop_fast_solver_time:                  0.
% 2.67/1.01  prop_unsat_core_time:                   0.
% 2.67/1.01  
% 2.67/1.01  ------ QBF
% 2.67/1.01  
% 2.67/1.01  qbf_q_res:                              0
% 2.67/1.01  qbf_num_tautologies:                    0
% 2.67/1.01  qbf_prep_cycles:                        0
% 2.67/1.01  
% 2.67/1.01  ------ BMC1
% 2.67/1.01  
% 2.67/1.01  bmc1_current_bound:                     -1
% 2.67/1.01  bmc1_last_solved_bound:                 -1
% 2.67/1.01  bmc1_unsat_core_size:                   -1
% 2.67/1.01  bmc1_unsat_core_parents_size:           -1
% 2.67/1.01  bmc1_merge_next_fun:                    0
% 2.67/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.67/1.01  
% 2.67/1.01  ------ Instantiation
% 2.67/1.01  
% 2.67/1.01  inst_num_of_clauses:                    258
% 2.67/1.01  inst_num_in_passive:                    77
% 2.67/1.01  inst_num_in_active:                     171
% 2.67/1.01  inst_num_in_unprocessed:                11
% 2.67/1.01  inst_num_of_loops:                      180
% 2.67/1.01  inst_num_of_learning_restarts:          0
% 2.67/1.01  inst_num_moves_active_passive:          2
% 2.67/1.01  inst_lit_activity:                      0
% 2.67/1.01  inst_lit_activity_moves:                0
% 2.67/1.01  inst_num_tautologies:                   0
% 2.67/1.01  inst_num_prop_implied:                  0
% 2.67/1.01  inst_num_existing_simplified:           0
% 2.67/1.01  inst_num_eq_res_simplified:             0
% 2.67/1.01  inst_num_child_elim:                    0
% 2.67/1.01  inst_num_of_dismatching_blockings:      24
% 2.67/1.01  inst_num_of_non_proper_insts:           232
% 2.67/1.01  inst_num_of_duplicates:                 0
% 2.67/1.01  inst_inst_num_from_inst_to_res:         0
% 2.67/1.01  inst_dismatching_checking_time:         0.
% 2.67/1.01  
% 2.67/1.01  ------ Resolution
% 2.67/1.01  
% 2.67/1.01  res_num_of_clauses:                     0
% 2.67/1.01  res_num_in_passive:                     0
% 2.67/1.01  res_num_in_active:                      0
% 2.67/1.01  res_num_of_loops:                       105
% 2.67/1.01  res_forward_subset_subsumed:            53
% 2.67/1.01  res_backward_subset_subsumed:           6
% 2.67/1.01  res_forward_subsumed:                   0
% 2.67/1.01  res_backward_subsumed:                  0
% 2.67/1.01  res_forward_subsumption_resolution:     1
% 2.67/1.01  res_backward_subsumption_resolution:    0
% 2.67/1.01  res_clause_to_clause_subsumption:       88
% 2.67/1.01  res_orphan_elimination:                 0
% 2.67/1.01  res_tautology_del:                      42
% 2.67/1.01  res_num_eq_res_simplified:              0
% 2.67/1.01  res_num_sel_changes:                    0
% 2.67/1.01  res_moves_from_active_to_pass:          0
% 2.67/1.01  
% 2.67/1.01  ------ Superposition
% 2.67/1.01  
% 2.67/1.01  sup_time_total:                         0.
% 2.67/1.01  sup_time_generating:                    0.
% 2.67/1.01  sup_time_sim_full:                      0.
% 2.67/1.01  sup_time_sim_immed:                     0.
% 2.67/1.01  
% 2.67/1.01  sup_num_of_clauses:                     33
% 2.67/1.01  sup_num_in_active:                      21
% 2.67/1.01  sup_num_in_passive:                     12
% 2.67/1.01  sup_num_of_loops:                       34
% 2.67/1.01  sup_fw_superposition:                   14
% 2.67/1.01  sup_bw_superposition:                   11
% 2.67/1.01  sup_immediate_simplified:               8
% 2.67/1.01  sup_given_eliminated:                   0
% 2.67/1.01  comparisons_done:                       0
% 2.67/1.01  comparisons_avoided:                    0
% 2.67/1.01  
% 2.67/1.01  ------ Simplifications
% 2.67/1.01  
% 2.67/1.01  
% 2.67/1.01  sim_fw_subset_subsumed:                 0
% 2.67/1.01  sim_bw_subset_subsumed:                 0
% 2.67/1.01  sim_fw_subsumed:                        0
% 2.67/1.01  sim_bw_subsumed:                        0
% 2.67/1.01  sim_fw_subsumption_res:                 1
% 2.67/1.01  sim_bw_subsumption_res:                 0
% 2.67/1.01  sim_tautology_del:                      0
% 2.67/1.01  sim_eq_tautology_del:                   2
% 2.67/1.01  sim_eq_res_simp:                        1
% 2.67/1.01  sim_fw_demodulated:                     1
% 2.67/1.01  sim_bw_demodulated:                     17
% 2.67/1.01  sim_light_normalised:                   14
% 2.67/1.01  sim_joinable_taut:                      0
% 2.67/1.01  sim_joinable_simp:                      0
% 2.67/1.01  sim_ac_normalised:                      0
% 2.67/1.01  sim_smt_subsumption:                    0
% 2.67/1.01  
%------------------------------------------------------------------------------
