%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:36 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :  224 (17173 expanded)
%              Number of clauses        :  143 (5442 expanded)
%              Number of leaves         :   21 (4760 expanded)
%              Depth                    :   31
%              Number of atoms          :  813 (107441 expanded)
%              Number of equality atoms :  303 (17217 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,
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

fof(f53,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f52,f51,f50])).

fof(f84,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f76,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f79,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f81,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f34])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f80,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f82,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f83,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f53])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f86,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f87,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f57,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f62,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f64,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f14,axiom,(
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

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f65,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_684,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1197,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_684])).

cnf(c_22,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_33,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_383,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_384,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_680,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_384])).

cnf(c_31,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_378,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_31])).

cnf(c_379,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_681,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_379])).

cnf(c_1221,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1197,c_680,c_681])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_23,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_365,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_366,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_46,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_368,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_366,c_32,c_31,c_46])).

cnf(c_390,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_368])).

cnf(c_391,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_17,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_487,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_391,c_17])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_503,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_487,c_12])).

cnf(c_678,plain,
    ( ~ v1_funct_2(X0_53,X0_54,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | k1_relat_1(X0_53) = X0_54 ),
    inference(subtyping,[status(esa)],[c_503])).

cnf(c_1202,plain,
    ( k1_relat_1(X0_53) = X0_54
    | v1_funct_2(X0_53,X0_54,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_678])).

cnf(c_1295,plain,
    ( k1_relat_1(X0_53) = X0_54
    | v1_funct_2(X0_53,X0_54,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1202,c_681])).

cnf(c_1662,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1221,c_1295])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_37,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_683,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1198,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_683])).

cnf(c_1215,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1198,c_680,c_681])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_703,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ v1_relat_1(X1_53)
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1466,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | v1_relat_1(X0_53)
    | ~ v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) ),
    inference(instantiation,[status(thm)],[c_703])).

cnf(c_1576,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1466])).

cnf(c_1577,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1576])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_702,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1634,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_702])).

cnf(c_1635,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1634])).

cnf(c_1724,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1662,c_37,c_39,c_1215,c_1577,c_1635])).

cnf(c_1727,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1724,c_1221])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_691,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | k2_relset_1(X0_54,X1_54,X0_53) = k2_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1191,plain,
    ( k2_relset_1(X0_54,X1_54,X0_53) = k2_relat_1(X0_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_691])).

cnf(c_1887,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1727,c_1191])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_685,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1218,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_685,c_680,c_681])).

cnf(c_1729,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1724,c_1218])).

cnf(c_2467,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1887,c_1729])).

cnf(c_2469,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2467,c_1887])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_687,plain,
    ( ~ v1_funct_2(X0_53,X0_54,X1_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v2_funct_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | k2_relset_1(X0_54,X1_54,X0_53) != X1_54
    | k2_tops_2(X0_54,X1_54,X0_53) = k2_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1195,plain,
    ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
    | k2_tops_2(X0_54,X1_54,X0_53) = k2_funct_1(X0_53)
    | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v2_funct_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_687])).

cnf(c_3697,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2469,c_1195])).

cnf(c_26,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_40,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2471,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2467,c_1727])).

cnf(c_1728,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1724,c_1215])).

cnf(c_2472,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2467,c_1728])).

cnf(c_4004,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3697,c_37,c_40,c_2471,c_2472])).

cnf(c_18,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_25,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_413,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_414,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_679,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_414])).

cnf(c_705,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sP0_iProver_split
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_679])).

cnf(c_1200,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_705])).

cnf(c_1382,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1200,c_680,c_681])).

cnf(c_704,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_53)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_679])).

cnf(c_1201,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_704])).

cnf(c_1286,plain,
    ( v1_funct_2(X0_53,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1201,c_680,c_681])).

cnf(c_1388,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1382,c_1286])).

cnf(c_1841,plain,
    ( k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_relat_1(sK2),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1388,c_1724])).

cnf(c_2470,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2467,c_1841])).

cnf(c_4007,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4004,c_2470])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_701,plain,
    ( ~ v1_funct_1(X0_53)
    | v1_funct_1(k2_funct_1(X0_53))
    | ~ v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_748,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_funct_1(X0_53)) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_750,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_748])).

cnf(c_686,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1196,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_686])).

cnf(c_7,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_696,plain,
    ( ~ v2_funct_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | k2_relat_1(k2_funct_1(X0_53)) = k1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1186,plain,
    ( k2_relat_1(k2_funct_1(X0_53)) = k1_relat_1(X0_53)
    | v2_funct_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_696])).

cnf(c_2000,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1196,c_1186])).

cnf(c_760,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_696])).

cnf(c_2119,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2000,c_30,c_28,c_26,c_760,c_1576,c_1634])).

cnf(c_5,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_698,plain,
    ( v2_funct_1(X0_53)
    | ~ v2_funct_1(k5_relat_1(X0_53,X1_53))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | ~ v1_relat_1(X0_53)
    | ~ v1_relat_1(X1_53)
    | k1_relat_1(X1_53) != k2_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1184,plain,
    ( k1_relat_1(X0_53) != k2_relat_1(X1_53)
    | v2_funct_1(X1_53) = iProver_top
    | v2_funct_1(k5_relat_1(X1_53,X0_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_relat_1(X1_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_698])).

cnf(c_2667,plain,
    ( k1_relat_1(X0_53) != k1_relat_1(sK2)
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_53)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(X0_53) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2119,c_1184])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_700,plain,
    ( ~ v1_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | v1_relat_1(k2_funct_1(X0_53)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_751,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top
    | v1_relat_1(k2_funct_1(X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_700])).

cnf(c_753,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_751])).

cnf(c_3151,plain,
    ( v1_relat_1(X0_53) != iProver_top
    | k1_relat_1(X0_53) != k1_relat_1(sK2)
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_53)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2667,c_37,c_39,c_750,c_753,c_1577,c_1635])).

cnf(c_3152,plain,
    ( k1_relat_1(X0_53) != k1_relat_1(sK2)
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_53)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_3151])).

cnf(c_3163,plain,
    ( v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3152])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_694,plain,
    ( ~ v2_funct_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | k5_relat_1(k2_funct_1(X0_53),X0_53) = k6_relat_1(k2_relat_1(X0_53)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1188,plain,
    ( k5_relat_1(k2_funct_1(X0_53),X0_53) = k6_relat_1(k2_relat_1(X0_53))
    | v2_funct_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_694])).

cnf(c_2705,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1196,c_1188])).

cnf(c_766,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_694])).

cnf(c_2956,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2705,c_30,c_28,c_26,c_766,c_1576,c_1634])).

cnf(c_3168,plain,
    ( v2_funct_1(k6_relat_1(k2_relat_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3163,c_2956])).

cnf(c_3175,plain,
    ( v2_funct_1(k6_relat_1(k2_relat_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3168,c_37,c_39,c_1577,c_1635])).

cnf(c_6,plain,
    ( v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_697,plain,
    ( v2_funct_1(k6_relat_1(X0_54)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1185,plain,
    ( v2_funct_1(k6_relat_1(X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_697])).

cnf(c_3181,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3175,c_1185])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_690,plain,
    ( ~ v1_funct_2(X0_53,X0_54,X1_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | m1_subset_1(k2_funct_1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_54,X0_54)))
    | ~ v2_funct_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | k2_relset_1(X0_54,X1_54,X0_53) != X1_54 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1192,plain,
    ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
    | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_54,X0_54))) = iProver_top
    | v2_funct_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_690])).

cnf(c_3698,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2469,c_1192])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_689,plain,
    ( ~ v1_funct_2(X0_53,X0_54,X1_54)
    | v1_funct_2(k2_funct_1(X0_53),X1_54,X0_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v2_funct_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | k2_relset_1(X0_54,X1_54,X0_53) != X1_54 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1193,plain,
    ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
    | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
    | v1_funct_2(k2_funct_1(X0_53),X1_54,X0_54) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v2_funct_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_689])).

cnf(c_3699,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2469,c_1193])).

cnf(c_4096,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3698,c_37,c_40,c_2471,c_2472])).

cnf(c_4102,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4096,c_1191])).

cnf(c_4109,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4102,c_2119])).

cnf(c_4336,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4109,c_1195])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_692,plain,
    ( ~ v2_funct_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | k2_funct_1(k2_funct_1(X0_53)) = X0_53 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1190,plain,
    ( k2_funct_1(k2_funct_1(X0_53)) = X0_53
    | v2_funct_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_692])).

cnf(c_1893,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1196,c_1190])).

cnf(c_772,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_692])).

cnf(c_2113,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1893,c_30,c_28,c_26,c_772,c_1576,c_1634])).

cnf(c_4356,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4336,c_2113])).

cnf(c_4463,plain,
    ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4007,c_37,c_39,c_40,c_750,c_1577,c_1635,c_2471,c_2472,c_3181,c_3698,c_3699,c_4356])).

cnf(c_4364,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4356,c_37,c_39,c_40,c_750,c_1577,c_1635,c_2471,c_2472,c_3181,c_3698,c_3699])).

cnf(c_4467,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4463,c_4364])).

cnf(c_682,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1199,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_682])).

cnf(c_4471,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4467,c_1199,c_2471,c_2472])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:57:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.64/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.01  
% 2.64/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.64/1.01  
% 2.64/1.01  ------  iProver source info
% 2.64/1.01  
% 2.64/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.64/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.64/1.01  git: non_committed_changes: false
% 2.64/1.01  git: last_make_outside_of_git: false
% 2.64/1.01  
% 2.64/1.01  ------ 
% 2.64/1.01  
% 2.64/1.01  ------ Input Options
% 2.64/1.01  
% 2.64/1.01  --out_options                           all
% 2.64/1.01  --tptp_safe_out                         true
% 2.64/1.01  --problem_path                          ""
% 2.64/1.01  --include_path                          ""
% 2.64/1.01  --clausifier                            res/vclausify_rel
% 2.64/1.01  --clausifier_options                    --mode clausify
% 2.64/1.01  --stdin                                 false
% 2.64/1.01  --stats_out                             all
% 2.64/1.01  
% 2.64/1.01  ------ General Options
% 2.64/1.01  
% 2.64/1.01  --fof                                   false
% 2.64/1.01  --time_out_real                         305.
% 2.64/1.01  --time_out_virtual                      -1.
% 2.64/1.01  --symbol_type_check                     false
% 2.64/1.01  --clausify_out                          false
% 2.64/1.01  --sig_cnt_out                           false
% 2.64/1.01  --trig_cnt_out                          false
% 2.64/1.01  --trig_cnt_out_tolerance                1.
% 2.64/1.01  --trig_cnt_out_sk_spl                   false
% 2.64/1.01  --abstr_cl_out                          false
% 2.64/1.01  
% 2.64/1.01  ------ Global Options
% 2.64/1.01  
% 2.64/1.01  --schedule                              default
% 2.64/1.01  --add_important_lit                     false
% 2.64/1.01  --prop_solver_per_cl                    1000
% 2.64/1.01  --min_unsat_core                        false
% 2.64/1.01  --soft_assumptions                      false
% 2.64/1.01  --soft_lemma_size                       3
% 2.64/1.01  --prop_impl_unit_size                   0
% 2.64/1.01  --prop_impl_unit                        []
% 2.64/1.01  --share_sel_clauses                     true
% 2.64/1.01  --reset_solvers                         false
% 2.64/1.01  --bc_imp_inh                            [conj_cone]
% 2.64/1.01  --conj_cone_tolerance                   3.
% 2.64/1.01  --extra_neg_conj                        none
% 2.64/1.01  --large_theory_mode                     true
% 2.64/1.01  --prolific_symb_bound                   200
% 2.64/1.01  --lt_threshold                          2000
% 2.64/1.01  --clause_weak_htbl                      true
% 2.64/1.01  --gc_record_bc_elim                     false
% 2.64/1.01  
% 2.64/1.01  ------ Preprocessing Options
% 2.64/1.01  
% 2.64/1.01  --preprocessing_flag                    true
% 2.64/1.01  --time_out_prep_mult                    0.1
% 2.64/1.01  --splitting_mode                        input
% 2.64/1.01  --splitting_grd                         true
% 2.64/1.01  --splitting_cvd                         false
% 2.64/1.01  --splitting_cvd_svl                     false
% 2.64/1.01  --splitting_nvd                         32
% 2.64/1.01  --sub_typing                            true
% 2.64/1.01  --prep_gs_sim                           true
% 2.64/1.01  --prep_unflatten                        true
% 2.64/1.01  --prep_res_sim                          true
% 2.64/1.01  --prep_upred                            true
% 2.64/1.01  --prep_sem_filter                       exhaustive
% 2.64/1.01  --prep_sem_filter_out                   false
% 2.64/1.01  --pred_elim                             true
% 2.64/1.01  --res_sim_input                         true
% 2.64/1.01  --eq_ax_congr_red                       true
% 2.64/1.01  --pure_diseq_elim                       true
% 2.64/1.01  --brand_transform                       false
% 2.64/1.01  --non_eq_to_eq                          false
% 2.64/1.01  --prep_def_merge                        true
% 2.64/1.01  --prep_def_merge_prop_impl              false
% 2.64/1.01  --prep_def_merge_mbd                    true
% 2.64/1.01  --prep_def_merge_tr_red                 false
% 2.64/1.01  --prep_def_merge_tr_cl                  false
% 2.64/1.01  --smt_preprocessing                     true
% 2.64/1.01  --smt_ac_axioms                         fast
% 2.64/1.01  --preprocessed_out                      false
% 2.64/1.01  --preprocessed_stats                    false
% 2.64/1.01  
% 2.64/1.01  ------ Abstraction refinement Options
% 2.64/1.01  
% 2.64/1.01  --abstr_ref                             []
% 2.64/1.01  --abstr_ref_prep                        false
% 2.64/1.01  --abstr_ref_until_sat                   false
% 2.64/1.01  --abstr_ref_sig_restrict                funpre
% 2.64/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.64/1.01  --abstr_ref_under                       []
% 2.64/1.01  
% 2.64/1.01  ------ SAT Options
% 2.64/1.01  
% 2.64/1.01  --sat_mode                              false
% 2.64/1.01  --sat_fm_restart_options                ""
% 2.64/1.01  --sat_gr_def                            false
% 2.64/1.01  --sat_epr_types                         true
% 2.64/1.01  --sat_non_cyclic_types                  false
% 2.64/1.01  --sat_finite_models                     false
% 2.64/1.01  --sat_fm_lemmas                         false
% 2.64/1.01  --sat_fm_prep                           false
% 2.64/1.01  --sat_fm_uc_incr                        true
% 2.64/1.01  --sat_out_model                         small
% 2.64/1.01  --sat_out_clauses                       false
% 2.64/1.01  
% 2.64/1.01  ------ QBF Options
% 2.64/1.01  
% 2.64/1.01  --qbf_mode                              false
% 2.64/1.01  --qbf_elim_univ                         false
% 2.64/1.01  --qbf_dom_inst                          none
% 2.64/1.01  --qbf_dom_pre_inst                      false
% 2.64/1.01  --qbf_sk_in                             false
% 2.64/1.01  --qbf_pred_elim                         true
% 2.64/1.01  --qbf_split                             512
% 2.64/1.01  
% 2.64/1.01  ------ BMC1 Options
% 2.64/1.01  
% 2.64/1.01  --bmc1_incremental                      false
% 2.64/1.01  --bmc1_axioms                           reachable_all
% 2.64/1.01  --bmc1_min_bound                        0
% 2.64/1.01  --bmc1_max_bound                        -1
% 2.64/1.01  --bmc1_max_bound_default                -1
% 2.64/1.01  --bmc1_symbol_reachability              true
% 2.64/1.01  --bmc1_property_lemmas                  false
% 2.64/1.01  --bmc1_k_induction                      false
% 2.64/1.01  --bmc1_non_equiv_states                 false
% 2.64/1.01  --bmc1_deadlock                         false
% 2.64/1.01  --bmc1_ucm                              false
% 2.64/1.01  --bmc1_add_unsat_core                   none
% 2.64/1.01  --bmc1_unsat_core_children              false
% 2.64/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.64/1.01  --bmc1_out_stat                         full
% 2.64/1.01  --bmc1_ground_init                      false
% 2.64/1.01  --bmc1_pre_inst_next_state              false
% 2.64/1.01  --bmc1_pre_inst_state                   false
% 2.64/1.01  --bmc1_pre_inst_reach_state             false
% 2.64/1.01  --bmc1_out_unsat_core                   false
% 2.64/1.01  --bmc1_aig_witness_out                  false
% 2.64/1.01  --bmc1_verbose                          false
% 2.64/1.01  --bmc1_dump_clauses_tptp                false
% 2.64/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.64/1.01  --bmc1_dump_file                        -
% 2.64/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.64/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.64/1.01  --bmc1_ucm_extend_mode                  1
% 2.64/1.01  --bmc1_ucm_init_mode                    2
% 2.64/1.01  --bmc1_ucm_cone_mode                    none
% 2.64/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.64/1.01  --bmc1_ucm_relax_model                  4
% 2.64/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.64/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.64/1.01  --bmc1_ucm_layered_model                none
% 2.64/1.01  --bmc1_ucm_max_lemma_size               10
% 2.64/1.01  
% 2.64/1.01  ------ AIG Options
% 2.64/1.01  
% 2.64/1.01  --aig_mode                              false
% 2.64/1.01  
% 2.64/1.01  ------ Instantiation Options
% 2.64/1.01  
% 2.64/1.01  --instantiation_flag                    true
% 2.64/1.01  --inst_sos_flag                         false
% 2.64/1.01  --inst_sos_phase                        true
% 2.64/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.64/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.64/1.01  --inst_lit_sel_side                     num_symb
% 2.64/1.01  --inst_solver_per_active                1400
% 2.64/1.01  --inst_solver_calls_frac                1.
% 2.64/1.01  --inst_passive_queue_type               priority_queues
% 2.64/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.64/1.01  --inst_passive_queues_freq              [25;2]
% 2.64/1.01  --inst_dismatching                      true
% 2.64/1.01  --inst_eager_unprocessed_to_passive     true
% 2.64/1.01  --inst_prop_sim_given                   true
% 2.64/1.01  --inst_prop_sim_new                     false
% 2.64/1.01  --inst_subs_new                         false
% 2.64/1.01  --inst_eq_res_simp                      false
% 2.64/1.01  --inst_subs_given                       false
% 2.64/1.01  --inst_orphan_elimination               true
% 2.64/1.01  --inst_learning_loop_flag               true
% 2.64/1.01  --inst_learning_start                   3000
% 2.64/1.01  --inst_learning_factor                  2
% 2.64/1.01  --inst_start_prop_sim_after_learn       3
% 2.64/1.01  --inst_sel_renew                        solver
% 2.64/1.01  --inst_lit_activity_flag                true
% 2.64/1.01  --inst_restr_to_given                   false
% 2.64/1.01  --inst_activity_threshold               500
% 2.64/1.01  --inst_out_proof                        true
% 2.64/1.01  
% 2.64/1.01  ------ Resolution Options
% 2.64/1.01  
% 2.64/1.01  --resolution_flag                       true
% 2.64/1.01  --res_lit_sel                           adaptive
% 2.64/1.01  --res_lit_sel_side                      none
% 2.64/1.01  --res_ordering                          kbo
% 2.64/1.01  --res_to_prop_solver                    active
% 2.64/1.01  --res_prop_simpl_new                    false
% 2.64/1.01  --res_prop_simpl_given                  true
% 2.64/1.01  --res_passive_queue_type                priority_queues
% 2.64/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.64/1.01  --res_passive_queues_freq               [15;5]
% 2.64/1.01  --res_forward_subs                      full
% 2.64/1.01  --res_backward_subs                     full
% 2.64/1.01  --res_forward_subs_resolution           true
% 2.64/1.01  --res_backward_subs_resolution          true
% 2.64/1.01  --res_orphan_elimination                true
% 2.64/1.01  --res_time_limit                        2.
% 2.64/1.01  --res_out_proof                         true
% 2.64/1.01  
% 2.64/1.01  ------ Superposition Options
% 2.64/1.01  
% 2.64/1.01  --superposition_flag                    true
% 2.64/1.01  --sup_passive_queue_type                priority_queues
% 2.64/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.64/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.64/1.01  --demod_completeness_check              fast
% 2.64/1.01  --demod_use_ground                      true
% 2.64/1.01  --sup_to_prop_solver                    passive
% 2.64/1.01  --sup_prop_simpl_new                    true
% 2.64/1.01  --sup_prop_simpl_given                  true
% 2.64/1.01  --sup_fun_splitting                     false
% 2.64/1.01  --sup_smt_interval                      50000
% 2.64/1.01  
% 2.64/1.01  ------ Superposition Simplification Setup
% 2.64/1.01  
% 2.64/1.01  --sup_indices_passive                   []
% 2.64/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.64/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.01  --sup_full_bw                           [BwDemod]
% 2.64/1.01  --sup_immed_triv                        [TrivRules]
% 2.64/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.64/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.01  --sup_immed_bw_main                     []
% 2.64/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.64/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/1.01  
% 2.64/1.01  ------ Combination Options
% 2.64/1.01  
% 2.64/1.01  --comb_res_mult                         3
% 2.64/1.01  --comb_sup_mult                         2
% 2.64/1.01  --comb_inst_mult                        10
% 2.64/1.01  
% 2.64/1.01  ------ Debug Options
% 2.64/1.01  
% 2.64/1.01  --dbg_backtrace                         false
% 2.64/1.01  --dbg_dump_prop_clauses                 false
% 2.64/1.01  --dbg_dump_prop_clauses_file            -
% 2.64/1.01  --dbg_out_stat                          false
% 2.64/1.01  ------ Parsing...
% 2.64/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.64/1.01  
% 2.64/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.64/1.01  
% 2.64/1.01  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.64/1.01  
% 2.64/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.64/1.01  ------ Proving...
% 2.64/1.01  ------ Problem Properties 
% 2.64/1.01  
% 2.64/1.01  
% 2.64/1.01  clauses                                 27
% 2.64/1.01  conjectures                             5
% 2.64/1.01  EPR                                     2
% 2.64/1.01  Horn                                    27
% 2.64/1.01  unary                                   9
% 2.64/1.01  binary                                  1
% 2.64/1.01  lits                                    92
% 2.64/1.01  lits eq                                 18
% 2.64/1.01  fd_pure                                 0
% 2.64/1.01  fd_pseudo                               0
% 2.64/1.01  fd_cond                                 0
% 2.64/1.01  fd_pseudo_cond                          1
% 2.64/1.01  AC symbols                              0
% 2.64/1.01  
% 2.64/1.01  ------ Schedule dynamic 5 is on 
% 2.64/1.01  
% 2.64/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.64/1.01  
% 2.64/1.01  
% 2.64/1.01  ------ 
% 2.64/1.01  Current options:
% 2.64/1.01  ------ 
% 2.64/1.01  
% 2.64/1.01  ------ Input Options
% 2.64/1.01  
% 2.64/1.01  --out_options                           all
% 2.64/1.01  --tptp_safe_out                         true
% 2.64/1.01  --problem_path                          ""
% 2.64/1.01  --include_path                          ""
% 2.64/1.01  --clausifier                            res/vclausify_rel
% 2.64/1.01  --clausifier_options                    --mode clausify
% 2.64/1.01  --stdin                                 false
% 2.64/1.01  --stats_out                             all
% 2.64/1.01  
% 2.64/1.01  ------ General Options
% 2.64/1.01  
% 2.64/1.01  --fof                                   false
% 2.64/1.01  --time_out_real                         305.
% 2.64/1.01  --time_out_virtual                      -1.
% 2.64/1.01  --symbol_type_check                     false
% 2.64/1.01  --clausify_out                          false
% 2.64/1.01  --sig_cnt_out                           false
% 2.64/1.01  --trig_cnt_out                          false
% 2.64/1.01  --trig_cnt_out_tolerance                1.
% 2.64/1.01  --trig_cnt_out_sk_spl                   false
% 2.64/1.01  --abstr_cl_out                          false
% 2.64/1.01  
% 2.64/1.01  ------ Global Options
% 2.64/1.01  
% 2.64/1.01  --schedule                              default
% 2.64/1.01  --add_important_lit                     false
% 2.64/1.01  --prop_solver_per_cl                    1000
% 2.64/1.01  --min_unsat_core                        false
% 2.64/1.01  --soft_assumptions                      false
% 2.64/1.01  --soft_lemma_size                       3
% 2.64/1.01  --prop_impl_unit_size                   0
% 2.64/1.01  --prop_impl_unit                        []
% 2.64/1.01  --share_sel_clauses                     true
% 2.64/1.01  --reset_solvers                         false
% 2.64/1.01  --bc_imp_inh                            [conj_cone]
% 2.64/1.01  --conj_cone_tolerance                   3.
% 2.64/1.01  --extra_neg_conj                        none
% 2.64/1.01  --large_theory_mode                     true
% 2.64/1.01  --prolific_symb_bound                   200
% 2.64/1.01  --lt_threshold                          2000
% 2.64/1.01  --clause_weak_htbl                      true
% 2.64/1.01  --gc_record_bc_elim                     false
% 2.64/1.01  
% 2.64/1.01  ------ Preprocessing Options
% 2.64/1.01  
% 2.64/1.01  --preprocessing_flag                    true
% 2.64/1.01  --time_out_prep_mult                    0.1
% 2.64/1.01  --splitting_mode                        input
% 2.64/1.01  --splitting_grd                         true
% 2.64/1.01  --splitting_cvd                         false
% 2.64/1.01  --splitting_cvd_svl                     false
% 2.64/1.01  --splitting_nvd                         32
% 2.64/1.01  --sub_typing                            true
% 2.64/1.01  --prep_gs_sim                           true
% 2.64/1.01  --prep_unflatten                        true
% 2.64/1.01  --prep_res_sim                          true
% 2.64/1.01  --prep_upred                            true
% 2.64/1.01  --prep_sem_filter                       exhaustive
% 2.64/1.01  --prep_sem_filter_out                   false
% 2.64/1.01  --pred_elim                             true
% 2.64/1.01  --res_sim_input                         true
% 2.64/1.01  --eq_ax_congr_red                       true
% 2.64/1.01  --pure_diseq_elim                       true
% 2.64/1.01  --brand_transform                       false
% 2.64/1.01  --non_eq_to_eq                          false
% 2.64/1.01  --prep_def_merge                        true
% 2.64/1.01  --prep_def_merge_prop_impl              false
% 2.64/1.01  --prep_def_merge_mbd                    true
% 2.64/1.01  --prep_def_merge_tr_red                 false
% 2.64/1.01  --prep_def_merge_tr_cl                  false
% 2.64/1.01  --smt_preprocessing                     true
% 2.64/1.01  --smt_ac_axioms                         fast
% 2.64/1.01  --preprocessed_out                      false
% 2.64/1.01  --preprocessed_stats                    false
% 2.64/1.01  
% 2.64/1.01  ------ Abstraction refinement Options
% 2.64/1.01  
% 2.64/1.01  --abstr_ref                             []
% 2.64/1.01  --abstr_ref_prep                        false
% 2.64/1.01  --abstr_ref_until_sat                   false
% 2.64/1.01  --abstr_ref_sig_restrict                funpre
% 2.64/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.64/1.01  --abstr_ref_under                       []
% 2.64/1.01  
% 2.64/1.01  ------ SAT Options
% 2.64/1.01  
% 2.64/1.01  --sat_mode                              false
% 2.64/1.01  --sat_fm_restart_options                ""
% 2.64/1.01  --sat_gr_def                            false
% 2.64/1.01  --sat_epr_types                         true
% 2.64/1.01  --sat_non_cyclic_types                  false
% 2.64/1.01  --sat_finite_models                     false
% 2.64/1.01  --sat_fm_lemmas                         false
% 2.64/1.01  --sat_fm_prep                           false
% 2.64/1.01  --sat_fm_uc_incr                        true
% 2.64/1.01  --sat_out_model                         small
% 2.64/1.01  --sat_out_clauses                       false
% 2.64/1.01  
% 2.64/1.01  ------ QBF Options
% 2.64/1.01  
% 2.64/1.01  --qbf_mode                              false
% 2.64/1.01  --qbf_elim_univ                         false
% 2.64/1.01  --qbf_dom_inst                          none
% 2.64/1.01  --qbf_dom_pre_inst                      false
% 2.64/1.01  --qbf_sk_in                             false
% 2.64/1.01  --qbf_pred_elim                         true
% 2.64/1.01  --qbf_split                             512
% 2.64/1.01  
% 2.64/1.01  ------ BMC1 Options
% 2.64/1.01  
% 2.64/1.01  --bmc1_incremental                      false
% 2.64/1.01  --bmc1_axioms                           reachable_all
% 2.64/1.01  --bmc1_min_bound                        0
% 2.64/1.01  --bmc1_max_bound                        -1
% 2.64/1.01  --bmc1_max_bound_default                -1
% 2.64/1.01  --bmc1_symbol_reachability              true
% 2.64/1.01  --bmc1_property_lemmas                  false
% 2.64/1.01  --bmc1_k_induction                      false
% 2.64/1.01  --bmc1_non_equiv_states                 false
% 2.64/1.01  --bmc1_deadlock                         false
% 2.64/1.01  --bmc1_ucm                              false
% 2.64/1.01  --bmc1_add_unsat_core                   none
% 2.64/1.01  --bmc1_unsat_core_children              false
% 2.64/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.64/1.01  --bmc1_out_stat                         full
% 2.64/1.01  --bmc1_ground_init                      false
% 2.64/1.01  --bmc1_pre_inst_next_state              false
% 2.64/1.01  --bmc1_pre_inst_state                   false
% 2.64/1.01  --bmc1_pre_inst_reach_state             false
% 2.64/1.01  --bmc1_out_unsat_core                   false
% 2.64/1.01  --bmc1_aig_witness_out                  false
% 2.64/1.01  --bmc1_verbose                          false
% 2.64/1.01  --bmc1_dump_clauses_tptp                false
% 2.64/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.64/1.01  --bmc1_dump_file                        -
% 2.64/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.64/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.64/1.01  --bmc1_ucm_extend_mode                  1
% 2.64/1.01  --bmc1_ucm_init_mode                    2
% 2.64/1.01  --bmc1_ucm_cone_mode                    none
% 2.64/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.64/1.01  --bmc1_ucm_relax_model                  4
% 2.64/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.64/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.64/1.01  --bmc1_ucm_layered_model                none
% 2.64/1.01  --bmc1_ucm_max_lemma_size               10
% 2.64/1.01  
% 2.64/1.01  ------ AIG Options
% 2.64/1.01  
% 2.64/1.01  --aig_mode                              false
% 2.64/1.01  
% 2.64/1.01  ------ Instantiation Options
% 2.64/1.01  
% 2.64/1.01  --instantiation_flag                    true
% 2.64/1.01  --inst_sos_flag                         false
% 2.64/1.01  --inst_sos_phase                        true
% 2.64/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.64/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.64/1.01  --inst_lit_sel_side                     none
% 2.64/1.01  --inst_solver_per_active                1400
% 2.64/1.01  --inst_solver_calls_frac                1.
% 2.64/1.01  --inst_passive_queue_type               priority_queues
% 2.64/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.64/1.01  --inst_passive_queues_freq              [25;2]
% 2.64/1.01  --inst_dismatching                      true
% 2.64/1.01  --inst_eager_unprocessed_to_passive     true
% 2.64/1.01  --inst_prop_sim_given                   true
% 2.64/1.01  --inst_prop_sim_new                     false
% 2.64/1.01  --inst_subs_new                         false
% 2.64/1.01  --inst_eq_res_simp                      false
% 2.64/1.01  --inst_subs_given                       false
% 2.64/1.01  --inst_orphan_elimination               true
% 2.64/1.01  --inst_learning_loop_flag               true
% 2.64/1.01  --inst_learning_start                   3000
% 2.64/1.01  --inst_learning_factor                  2
% 2.64/1.01  --inst_start_prop_sim_after_learn       3
% 2.64/1.01  --inst_sel_renew                        solver
% 2.64/1.01  --inst_lit_activity_flag                true
% 2.64/1.01  --inst_restr_to_given                   false
% 2.64/1.01  --inst_activity_threshold               500
% 2.64/1.01  --inst_out_proof                        true
% 2.64/1.01  
% 2.64/1.01  ------ Resolution Options
% 2.64/1.01  
% 2.64/1.01  --resolution_flag                       false
% 2.64/1.01  --res_lit_sel                           adaptive
% 2.64/1.01  --res_lit_sel_side                      none
% 2.64/1.01  --res_ordering                          kbo
% 2.64/1.01  --res_to_prop_solver                    active
% 2.64/1.01  --res_prop_simpl_new                    false
% 2.64/1.01  --res_prop_simpl_given                  true
% 2.64/1.01  --res_passive_queue_type                priority_queues
% 2.64/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.64/1.01  --res_passive_queues_freq               [15;5]
% 2.64/1.01  --res_forward_subs                      full
% 2.64/1.01  --res_backward_subs                     full
% 2.64/1.01  --res_forward_subs_resolution           true
% 2.64/1.01  --res_backward_subs_resolution          true
% 2.64/1.01  --res_orphan_elimination                true
% 2.64/1.01  --res_time_limit                        2.
% 2.64/1.01  --res_out_proof                         true
% 2.64/1.01  
% 2.64/1.01  ------ Superposition Options
% 2.64/1.01  
% 2.64/1.01  --superposition_flag                    true
% 2.64/1.01  --sup_passive_queue_type                priority_queues
% 2.64/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.64/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.64/1.01  --demod_completeness_check              fast
% 2.64/1.01  --demod_use_ground                      true
% 2.64/1.01  --sup_to_prop_solver                    passive
% 2.64/1.01  --sup_prop_simpl_new                    true
% 2.64/1.01  --sup_prop_simpl_given                  true
% 2.64/1.01  --sup_fun_splitting                     false
% 2.64/1.01  --sup_smt_interval                      50000
% 2.64/1.01  
% 2.64/1.01  ------ Superposition Simplification Setup
% 2.64/1.01  
% 2.64/1.01  --sup_indices_passive                   []
% 2.64/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.64/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.01  --sup_full_bw                           [BwDemod]
% 2.64/1.01  --sup_immed_triv                        [TrivRules]
% 2.64/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.64/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.01  --sup_immed_bw_main                     []
% 2.64/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.64/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/1.01  
% 2.64/1.01  ------ Combination Options
% 2.64/1.01  
% 2.64/1.01  --comb_res_mult                         3
% 2.64/1.01  --comb_sup_mult                         2
% 2.64/1.01  --comb_inst_mult                        10
% 2.64/1.01  
% 2.64/1.01  ------ Debug Options
% 2.64/1.01  
% 2.64/1.01  --dbg_backtrace                         false
% 2.64/1.01  --dbg_dump_prop_clauses                 false
% 2.64/1.01  --dbg_dump_prop_clauses_file            -
% 2.64/1.01  --dbg_out_stat                          false
% 2.64/1.01  
% 2.64/1.01  
% 2.64/1.01  
% 2.64/1.01  
% 2.64/1.01  ------ Proving...
% 2.64/1.01  
% 2.64/1.01  
% 2.64/1.01  % SZS status Theorem for theBenchmark.p
% 2.64/1.01  
% 2.64/1.01   Resolution empty clause
% 2.64/1.01  
% 2.64/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.64/1.01  
% 2.64/1.01  fof(f18,conjecture,(
% 2.64/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f19,negated_conjecture,(
% 2.64/1.01    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.64/1.01    inference(negated_conjecture,[],[f18])).
% 2.64/1.01  
% 2.64/1.01  fof(f47,plain,(
% 2.64/1.01    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.64/1.01    inference(ennf_transformation,[],[f19])).
% 2.64/1.01  
% 2.64/1.01  fof(f48,plain,(
% 2.64/1.01    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.64/1.01    inference(flattening,[],[f47])).
% 2.64/1.01  
% 2.64/1.01  fof(f52,plain,(
% 2.64/1.01    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.64/1.01    introduced(choice_axiom,[])).
% 2.64/1.01  
% 2.64/1.01  fof(f51,plain,(
% 2.64/1.01    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.64/1.01    introduced(choice_axiom,[])).
% 2.64/1.01  
% 2.64/1.01  fof(f50,plain,(
% 2.64/1.01    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.64/1.01    introduced(choice_axiom,[])).
% 2.64/1.01  
% 2.64/1.01  fof(f53,plain,(
% 2.64/1.01    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.64/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f52,f51,f50])).
% 2.64/1.01  
% 2.64/1.01  fof(f84,plain,(
% 2.64/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.64/1.01    inference(cnf_transformation,[],[f53])).
% 2.64/1.01  
% 2.64/1.01  fof(f15,axiom,(
% 2.64/1.01    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f42,plain,(
% 2.64/1.01    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.64/1.01    inference(ennf_transformation,[],[f15])).
% 2.64/1.01  
% 2.64/1.01  fof(f76,plain,(
% 2.64/1.01    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f42])).
% 2.64/1.01  
% 2.64/1.01  fof(f79,plain,(
% 2.64/1.01    l1_struct_0(sK0)),
% 2.64/1.01    inference(cnf_transformation,[],[f53])).
% 2.64/1.01  
% 2.64/1.01  fof(f81,plain,(
% 2.64/1.01    l1_struct_0(sK1)),
% 2.64/1.01    inference(cnf_transformation,[],[f53])).
% 2.64/1.01  
% 2.64/1.01  fof(f11,axiom,(
% 2.64/1.01    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f34,plain,(
% 2.64/1.01    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.64/1.01    inference(ennf_transformation,[],[f11])).
% 2.64/1.01  
% 2.64/1.01  fof(f35,plain,(
% 2.64/1.01    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.64/1.01    inference(flattening,[],[f34])).
% 2.64/1.01  
% 2.64/1.01  fof(f69,plain,(
% 2.64/1.01    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f35])).
% 2.64/1.01  
% 2.64/1.01  fof(f16,axiom,(
% 2.64/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f43,plain,(
% 2.64/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.64/1.01    inference(ennf_transformation,[],[f16])).
% 2.64/1.01  
% 2.64/1.01  fof(f44,plain,(
% 2.64/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.64/1.01    inference(flattening,[],[f43])).
% 2.64/1.01  
% 2.64/1.01  fof(f77,plain,(
% 2.64/1.01    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f44])).
% 2.64/1.01  
% 2.64/1.01  fof(f80,plain,(
% 2.64/1.01    ~v2_struct_0(sK1)),
% 2.64/1.01    inference(cnf_transformation,[],[f53])).
% 2.64/1.01  
% 2.64/1.01  fof(f12,axiom,(
% 2.64/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f36,plain,(
% 2.64/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.64/1.01    inference(ennf_transformation,[],[f12])).
% 2.64/1.01  
% 2.64/1.01  fof(f37,plain,(
% 2.64/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.64/1.01    inference(flattening,[],[f36])).
% 2.64/1.01  
% 2.64/1.01  fof(f49,plain,(
% 2.64/1.01    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.64/1.01    inference(nnf_transformation,[],[f37])).
% 2.64/1.01  
% 2.64/1.01  fof(f70,plain,(
% 2.64/1.01    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f49])).
% 2.64/1.01  
% 2.64/1.01  fof(f9,axiom,(
% 2.64/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f20,plain,(
% 2.64/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.64/1.01    inference(pure_predicate_removal,[],[f9])).
% 2.64/1.01  
% 2.64/1.01  fof(f32,plain,(
% 2.64/1.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.64/1.01    inference(ennf_transformation,[],[f20])).
% 2.64/1.01  
% 2.64/1.01  fof(f66,plain,(
% 2.64/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.64/1.01    inference(cnf_transformation,[],[f32])).
% 2.64/1.01  
% 2.64/1.01  fof(f82,plain,(
% 2.64/1.01    v1_funct_1(sK2)),
% 2.64/1.01    inference(cnf_transformation,[],[f53])).
% 2.64/1.01  
% 2.64/1.01  fof(f83,plain,(
% 2.64/1.01    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.64/1.01    inference(cnf_transformation,[],[f53])).
% 2.64/1.01  
% 2.64/1.01  fof(f1,axiom,(
% 2.64/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f21,plain,(
% 2.64/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.64/1.01    inference(ennf_transformation,[],[f1])).
% 2.64/1.01  
% 2.64/1.01  fof(f54,plain,(
% 2.64/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f21])).
% 2.64/1.01  
% 2.64/1.01  fof(f2,axiom,(
% 2.64/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f55,plain,(
% 2.64/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.64/1.01    inference(cnf_transformation,[],[f2])).
% 2.64/1.01  
% 2.64/1.01  fof(f10,axiom,(
% 2.64/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f33,plain,(
% 2.64/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.64/1.01    inference(ennf_transformation,[],[f10])).
% 2.64/1.01  
% 2.64/1.01  fof(f67,plain,(
% 2.64/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.64/1.01    inference(cnf_transformation,[],[f33])).
% 2.64/1.01  
% 2.64/1.01  fof(f85,plain,(
% 2.64/1.01    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.64/1.01    inference(cnf_transformation,[],[f53])).
% 2.64/1.01  
% 2.64/1.01  fof(f17,axiom,(
% 2.64/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f45,plain,(
% 2.64/1.01    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.64/1.01    inference(ennf_transformation,[],[f17])).
% 2.64/1.01  
% 2.64/1.01  fof(f46,plain,(
% 2.64/1.01    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.64/1.01    inference(flattening,[],[f45])).
% 2.64/1.01  
% 2.64/1.01  fof(f78,plain,(
% 2.64/1.01    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f46])).
% 2.64/1.01  
% 2.64/1.01  fof(f86,plain,(
% 2.64/1.01    v2_funct_1(sK2)),
% 2.64/1.01    inference(cnf_transformation,[],[f53])).
% 2.64/1.01  
% 2.64/1.01  fof(f13,axiom,(
% 2.64/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 2.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f38,plain,(
% 2.64/1.01    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.64/1.01    inference(ennf_transformation,[],[f13])).
% 2.64/1.01  
% 2.64/1.01  fof(f39,plain,(
% 2.64/1.01    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.64/1.01    inference(flattening,[],[f38])).
% 2.64/1.01  
% 2.64/1.01  fof(f72,plain,(
% 2.64/1.01    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f39])).
% 2.64/1.01  
% 2.64/1.01  fof(f87,plain,(
% 2.64/1.01    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 2.64/1.01    inference(cnf_transformation,[],[f53])).
% 2.64/1.01  
% 2.64/1.01  fof(f3,axiom,(
% 2.64/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f22,plain,(
% 2.64/1.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.64/1.01    inference(ennf_transformation,[],[f3])).
% 2.64/1.01  
% 2.64/1.01  fof(f23,plain,(
% 2.64/1.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.64/1.01    inference(flattening,[],[f22])).
% 2.64/1.01  
% 2.64/1.01  fof(f57,plain,(
% 2.64/1.01    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f23])).
% 2.64/1.01  
% 2.64/1.01  fof(f6,axiom,(
% 2.64/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f26,plain,(
% 2.64/1.01    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.64/1.01    inference(ennf_transformation,[],[f6])).
% 2.64/1.01  
% 2.64/1.01  fof(f27,plain,(
% 2.64/1.01    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.64/1.01    inference(flattening,[],[f26])).
% 2.64/1.01  
% 2.64/1.01  fof(f62,plain,(
% 2.64/1.01    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f27])).
% 2.64/1.01  
% 2.64/1.01  fof(f4,axiom,(
% 2.64/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 2.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f24,plain,(
% 2.64/1.01    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.64/1.01    inference(ennf_transformation,[],[f4])).
% 2.64/1.01  
% 2.64/1.01  fof(f25,plain,(
% 2.64/1.01    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.64/1.01    inference(flattening,[],[f24])).
% 2.64/1.01  
% 2.64/1.01  fof(f58,plain,(
% 2.64/1.01    ( ! [X0,X1] : (v2_funct_1(X1) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f25])).
% 2.64/1.01  
% 2.64/1.01  fof(f56,plain,(
% 2.64/1.01    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f23])).
% 2.64/1.01  
% 2.64/1.01  fof(f7,axiom,(
% 2.64/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f28,plain,(
% 2.64/1.01    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.64/1.01    inference(ennf_transformation,[],[f7])).
% 2.64/1.01  
% 2.64/1.01  fof(f29,plain,(
% 2.64/1.01    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.64/1.01    inference(flattening,[],[f28])).
% 2.64/1.01  
% 2.64/1.01  fof(f64,plain,(
% 2.64/1.01    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f29])).
% 2.64/1.01  
% 2.64/1.01  fof(f5,axiom,(
% 2.64/1.01    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 2.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f60,plain,(
% 2.64/1.01    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.64/1.01    inference(cnf_transformation,[],[f5])).
% 2.64/1.01  
% 2.64/1.01  fof(f14,axiom,(
% 2.64/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f40,plain,(
% 2.64/1.01    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.64/1.01    inference(ennf_transformation,[],[f14])).
% 2.64/1.01  
% 2.64/1.01  fof(f41,plain,(
% 2.64/1.01    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.64/1.01    inference(flattening,[],[f40])).
% 2.64/1.01  
% 2.64/1.01  fof(f75,plain,(
% 2.64/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f41])).
% 2.64/1.01  
% 2.64/1.01  fof(f74,plain,(
% 2.64/1.01    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f41])).
% 2.64/1.01  
% 2.64/1.01  fof(f8,axiom,(
% 2.64/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.64/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.64/1.01  
% 2.64/1.01  fof(f30,plain,(
% 2.64/1.01    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.64/1.01    inference(ennf_transformation,[],[f8])).
% 2.64/1.01  
% 2.64/1.01  fof(f31,plain,(
% 2.64/1.01    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.64/1.01    inference(flattening,[],[f30])).
% 2.64/1.01  
% 2.64/1.01  fof(f65,plain,(
% 2.64/1.01    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.64/1.01    inference(cnf_transformation,[],[f31])).
% 2.64/1.01  
% 2.64/1.01  cnf(c_28,negated_conjecture,
% 2.64/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.64/1.01      inference(cnf_transformation,[],[f84]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_684,negated_conjecture,
% 2.64/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_28]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1197,plain,
% 2.64/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_684]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_22,plain,
% 2.64/1.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.64/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_33,negated_conjecture,
% 2.64/1.01      ( l1_struct_0(sK0) ),
% 2.64/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_383,plain,
% 2.64/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.64/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_384,plain,
% 2.64/1.01      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.64/1.01      inference(unflattening,[status(thm)],[c_383]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_680,plain,
% 2.64/1.01      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_384]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_31,negated_conjecture,
% 2.64/1.01      ( l1_struct_0(sK1) ),
% 2.64/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_378,plain,
% 2.64/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.64/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_31]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_379,plain,
% 2.64/1.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.64/1.01      inference(unflattening,[status(thm)],[c_378]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_681,plain,
% 2.64/1.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_379]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1221,plain,
% 2.64/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.64/1.01      inference(light_normalisation,[status(thm)],[c_1197,c_680,c_681]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_14,plain,
% 2.64/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.64/1.01      | v1_partfun1(X0,X1)
% 2.64/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.64/1.01      | v1_xboole_0(X2)
% 2.64/1.01      | ~ v1_funct_1(X0) ),
% 2.64/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_23,plain,
% 2.64/1.01      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.64/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_32,negated_conjecture,
% 2.64/1.01      ( ~ v2_struct_0(sK1) ),
% 2.64/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_365,plain,
% 2.64/1.01      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 2.64/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_32]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_366,plain,
% 2.64/1.01      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.64/1.01      inference(unflattening,[status(thm)],[c_365]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_46,plain,
% 2.64/1.01      ( v2_struct_0(sK1)
% 2.64/1.01      | ~ l1_struct_0(sK1)
% 2.64/1.01      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_23]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_368,plain,
% 2.64/1.01      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_366,c_32,c_31,c_46]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_390,plain,
% 2.64/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.64/1.01      | v1_partfun1(X0,X1)
% 2.64/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.64/1.01      | ~ v1_funct_1(X0)
% 2.64/1.01      | u1_struct_0(sK1) != X2 ),
% 2.64/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_368]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_391,plain,
% 2.64/1.01      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.64/1.01      | v1_partfun1(X0,X1)
% 2.64/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.64/1.01      | ~ v1_funct_1(X0) ),
% 2.64/1.01      inference(unflattening,[status(thm)],[c_390]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_17,plain,
% 2.64/1.01      ( ~ v1_partfun1(X0,X1)
% 2.64/1.01      | ~ v4_relat_1(X0,X1)
% 2.64/1.01      | ~ v1_relat_1(X0)
% 2.64/1.01      | k1_relat_1(X0) = X1 ),
% 2.64/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_487,plain,
% 2.64/1.01      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.64/1.01      | ~ v4_relat_1(X0,X1)
% 2.64/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.64/1.01      | ~ v1_funct_1(X0)
% 2.64/1.01      | ~ v1_relat_1(X0)
% 2.64/1.01      | k1_relat_1(X0) = X1 ),
% 2.64/1.01      inference(resolution,[status(thm)],[c_391,c_17]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_12,plain,
% 2.64/1.01      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.64/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_503,plain,
% 2.64/1.01      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.64/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.64/1.01      | ~ v1_funct_1(X0)
% 2.64/1.01      | ~ v1_relat_1(X0)
% 2.64/1.01      | k1_relat_1(X0) = X1 ),
% 2.64/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_487,c_12]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_678,plain,
% 2.64/1.01      ( ~ v1_funct_2(X0_53,X0_54,u1_struct_0(sK1))
% 2.64/1.01      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,u1_struct_0(sK1))))
% 2.64/1.01      | ~ v1_funct_1(X0_53)
% 2.64/1.01      | ~ v1_relat_1(X0_53)
% 2.64/1.01      | k1_relat_1(X0_53) = X0_54 ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_503]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1202,plain,
% 2.64/1.01      ( k1_relat_1(X0_53) = X0_54
% 2.64/1.01      | v1_funct_2(X0_53,X0_54,u1_struct_0(sK1)) != iProver_top
% 2.64/1.01      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,u1_struct_0(sK1)))) != iProver_top
% 2.64/1.01      | v1_funct_1(X0_53) != iProver_top
% 2.64/1.01      | v1_relat_1(X0_53) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_678]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1295,plain,
% 2.64/1.01      ( k1_relat_1(X0_53) = X0_54
% 2.64/1.01      | v1_funct_2(X0_53,X0_54,k2_struct_0(sK1)) != iProver_top
% 2.64/1.01      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,k2_struct_0(sK1)))) != iProver_top
% 2.64/1.01      | v1_funct_1(X0_53) != iProver_top
% 2.64/1.01      | v1_relat_1(X0_53) != iProver_top ),
% 2.64/1.01      inference(light_normalisation,[status(thm)],[c_1202,c_681]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1662,plain,
% 2.64/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.64/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.64/1.01      | v1_funct_1(sK2) != iProver_top
% 2.64/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_1221,c_1295]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_30,negated_conjecture,
% 2.64/1.01      ( v1_funct_1(sK2) ),
% 2.64/1.01      inference(cnf_transformation,[],[f82]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_37,plain,
% 2.64/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_39,plain,
% 2.64/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_29,negated_conjecture,
% 2.64/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.64/1.01      inference(cnf_transformation,[],[f83]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_683,negated_conjecture,
% 2.64/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_29]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1198,plain,
% 2.64/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_683]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1215,plain,
% 2.64/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.64/1.01      inference(light_normalisation,[status(thm)],[c_1198,c_680,c_681]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_0,plain,
% 2.64/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.64/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_703,plain,
% 2.64/1.01      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 2.64/1.01      | ~ v1_relat_1(X1_53)
% 2.64/1.01      | v1_relat_1(X0_53) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1466,plain,
% 2.64/1.01      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.64/1.01      | v1_relat_1(X0_53)
% 2.64/1.01      | ~ v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_703]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1576,plain,
% 2.64/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.64/1.01      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.64/1.01      | v1_relat_1(sK2) ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_1466]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1577,plain,
% 2.64/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.64/1.01      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.64/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_1576]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1,plain,
% 2.64/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.64/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_702,plain,
% 2.64/1.01      ( v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1634,plain,
% 2.64/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_702]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1635,plain,
% 2.64/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_1634]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1724,plain,
% 2.64/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_1662,c_37,c_39,c_1215,c_1577,c_1635]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1727,plain,
% 2.64/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) = iProver_top ),
% 2.64/1.01      inference(demodulation,[status(thm)],[c_1724,c_1221]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_13,plain,
% 2.64/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.64/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.64/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_691,plain,
% 2.64/1.01      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.64/1.01      | k2_relset_1(X0_54,X1_54,X0_53) = k2_relat_1(X0_53) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_13]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1191,plain,
% 2.64/1.01      ( k2_relset_1(X0_54,X1_54,X0_53) = k2_relat_1(X0_53)
% 2.64/1.01      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_691]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1887,plain,
% 2.64/1.01      ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_1727,c_1191]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_27,negated_conjecture,
% 2.64/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.64/1.01      inference(cnf_transformation,[],[f85]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_685,negated_conjecture,
% 2.64/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_27]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1218,plain,
% 2.64/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.64/1.01      inference(light_normalisation,[status(thm)],[c_685,c_680,c_681]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1729,plain,
% 2.64/1.01      ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.64/1.01      inference(demodulation,[status(thm)],[c_1724,c_1218]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2467,plain,
% 2.64/1.01      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.64/1.01      inference(demodulation,[status(thm)],[c_1887,c_1729]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2469,plain,
% 2.64/1.01      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.64/1.01      inference(demodulation,[status(thm)],[c_2467,c_1887]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_24,plain,
% 2.64/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.64/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.64/1.01      | ~ v2_funct_1(X0)
% 2.64/1.01      | ~ v1_funct_1(X0)
% 2.64/1.01      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.64/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.64/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_687,plain,
% 2.64/1.01      ( ~ v1_funct_2(X0_53,X0_54,X1_54)
% 2.64/1.01      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.64/1.01      | ~ v2_funct_1(X0_53)
% 2.64/1.01      | ~ v1_funct_1(X0_53)
% 2.64/1.01      | k2_relset_1(X0_54,X1_54,X0_53) != X1_54
% 2.64/1.01      | k2_tops_2(X0_54,X1_54,X0_53) = k2_funct_1(X0_53) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_24]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1195,plain,
% 2.64/1.01      ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
% 2.64/1.01      | k2_tops_2(X0_54,X1_54,X0_53) = k2_funct_1(X0_53)
% 2.64/1.01      | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
% 2.64/1.01      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 2.64/1.01      | v2_funct_1(X0_53) != iProver_top
% 2.64/1.01      | v1_funct_1(X0_53) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_687]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_3697,plain,
% 2.64/1.01      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 2.64/1.01      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.64/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.64/1.01      | v2_funct_1(sK2) != iProver_top
% 2.64/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_2469,c_1195]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_26,negated_conjecture,
% 2.64/1.01      ( v2_funct_1(sK2) ),
% 2.64/1.01      inference(cnf_transformation,[],[f86]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_40,plain,
% 2.64/1.01      ( v2_funct_1(sK2) = iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2471,plain,
% 2.64/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 2.64/1.01      inference(demodulation,[status(thm)],[c_2467,c_1727]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1728,plain,
% 2.64/1.01      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) = iProver_top ),
% 2.64/1.01      inference(demodulation,[status(thm)],[c_1724,c_1215]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2472,plain,
% 2.64/1.01      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 2.64/1.01      inference(demodulation,[status(thm)],[c_2467,c_1728]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4004,plain,
% 2.64/1.01      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_3697,c_37,c_40,c_2471,c_2472]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_18,plain,
% 2.64/1.01      ( r2_funct_2(X0,X1,X2,X2)
% 2.64/1.01      | ~ v1_funct_2(X2,X0,X1)
% 2.64/1.01      | ~ v1_funct_2(X3,X0,X1)
% 2.64/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.64/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.64/1.01      | ~ v1_funct_1(X2)
% 2.64/1.01      | ~ v1_funct_1(X3) ),
% 2.64/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_25,negated_conjecture,
% 2.64/1.01      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 2.64/1.01      inference(cnf_transformation,[],[f87]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_413,plain,
% 2.64/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.64/1.01      | ~ v1_funct_2(X3,X1,X2)
% 2.64/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.64/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.64/1.01      | ~ v1_funct_1(X0)
% 2.64/1.01      | ~ v1_funct_1(X3)
% 2.64/1.01      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 2.64/1.01      | u1_struct_0(sK1) != X2
% 2.64/1.01      | u1_struct_0(sK0) != X1
% 2.64/1.01      | sK2 != X0 ),
% 2.64/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_414,plain,
% 2.64/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.64/1.01      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.64/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.64/1.01      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.64/1.01      | ~ v1_funct_1(X0)
% 2.64/1.01      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.64/1.01      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.64/1.01      inference(unflattening,[status(thm)],[c_413]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_679,plain,
% 2.64/1.01      ( ~ v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.64/1.01      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.64/1.01      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.64/1.01      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.64/1.01      | ~ v1_funct_1(X0_53)
% 2.64/1.01      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.64/1.01      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_414]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_705,plain,
% 2.64/1.01      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.64/1.01      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.64/1.01      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.64/1.01      | sP0_iProver_split
% 2.64/1.01      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.64/1.01      inference(splitting,
% 2.64/1.01                [splitting(split),new_symbols(definition,[])],
% 2.64/1.01                [c_679]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1200,plain,
% 2.64/1.01      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.64/1.01      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.64/1.01      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.64/1.01      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
% 2.64/1.01      | sP0_iProver_split = iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_705]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1382,plain,
% 2.64/1.01      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.64/1.01      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.64/1.01      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.64/1.01      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
% 2.64/1.01      | sP0_iProver_split = iProver_top ),
% 2.64/1.01      inference(light_normalisation,[status(thm)],[c_1200,c_680,c_681]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_704,plain,
% 2.64/1.01      ( ~ v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.64/1.01      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.64/1.01      | ~ v1_funct_1(X0_53)
% 2.64/1.01      | ~ sP0_iProver_split ),
% 2.64/1.01      inference(splitting,
% 2.64/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.64/1.01                [c_679]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1201,plain,
% 2.64/1.01      ( v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.64/1.01      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.64/1.01      | v1_funct_1(X0_53) != iProver_top
% 2.64/1.01      | sP0_iProver_split != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_704]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1286,plain,
% 2.64/1.01      ( v1_funct_2(X0_53,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.64/1.01      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.64/1.01      | v1_funct_1(X0_53) != iProver_top
% 2.64/1.01      | sP0_iProver_split != iProver_top ),
% 2.64/1.01      inference(light_normalisation,[status(thm)],[c_1201,c_680,c_681]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1388,plain,
% 2.64/1.01      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.64/1.01      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.64/1.01      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.64/1.01      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.64/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_1382,c_1286]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1841,plain,
% 2.64/1.01      ( k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) != sK2
% 2.64/1.01      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_relat_1(sK2),k2_struct_0(sK1)) != iProver_top
% 2.64/1.01      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) != iProver_top
% 2.64/1.01      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.64/1.01      inference(light_normalisation,[status(thm)],[c_1388,c_1724]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2470,plain,
% 2.64/1.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
% 2.64/1.01      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.64/1.01      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.64/1.01      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
% 2.64/1.01      inference(demodulation,[status(thm)],[c_2467,c_1841]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4007,plain,
% 2.64/1.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 2.64/1.01      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.64/1.01      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.64/1.01      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 2.64/1.01      inference(demodulation,[status(thm)],[c_4004,c_2470]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2,plain,
% 2.64/1.01      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 2.64/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_701,plain,
% 2.64/1.01      ( ~ v1_funct_1(X0_53)
% 2.64/1.01      | v1_funct_1(k2_funct_1(X0_53))
% 2.64/1.01      | ~ v1_relat_1(X0_53) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_748,plain,
% 2.64/1.01      ( v1_funct_1(X0_53) != iProver_top
% 2.64/1.01      | v1_funct_1(k2_funct_1(X0_53)) = iProver_top
% 2.64/1.01      | v1_relat_1(X0_53) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_701]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_750,plain,
% 2.64/1.01      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.64/1.01      | v1_funct_1(sK2) != iProver_top
% 2.64/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_748]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_686,negated_conjecture,
% 2.64/1.01      ( v2_funct_1(sK2) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_26]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1196,plain,
% 2.64/1.01      ( v2_funct_1(sK2) = iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_686]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_7,plain,
% 2.64/1.01      ( ~ v2_funct_1(X0)
% 2.64/1.01      | ~ v1_funct_1(X0)
% 2.64/1.01      | ~ v1_relat_1(X0)
% 2.64/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.64/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_696,plain,
% 2.64/1.01      ( ~ v2_funct_1(X0_53)
% 2.64/1.01      | ~ v1_funct_1(X0_53)
% 2.64/1.01      | ~ v1_relat_1(X0_53)
% 2.64/1.01      | k2_relat_1(k2_funct_1(X0_53)) = k1_relat_1(X0_53) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1186,plain,
% 2.64/1.01      ( k2_relat_1(k2_funct_1(X0_53)) = k1_relat_1(X0_53)
% 2.64/1.01      | v2_funct_1(X0_53) != iProver_top
% 2.64/1.01      | v1_funct_1(X0_53) != iProver_top
% 2.64/1.01      | v1_relat_1(X0_53) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_696]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2000,plain,
% 2.64/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.64/1.01      | v1_funct_1(sK2) != iProver_top
% 2.64/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_1196,c_1186]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_760,plain,
% 2.64/1.01      ( ~ v2_funct_1(sK2)
% 2.64/1.01      | ~ v1_funct_1(sK2)
% 2.64/1.01      | ~ v1_relat_1(sK2)
% 2.64/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_696]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2119,plain,
% 2.64/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_2000,c_30,c_28,c_26,c_760,c_1576,c_1634]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_5,plain,
% 2.64/1.01      ( v2_funct_1(X0)
% 2.64/1.01      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 2.64/1.01      | ~ v1_funct_1(X1)
% 2.64/1.01      | ~ v1_funct_1(X0)
% 2.64/1.01      | ~ v1_relat_1(X1)
% 2.64/1.01      | ~ v1_relat_1(X0)
% 2.64/1.01      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 2.64/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_698,plain,
% 2.64/1.01      ( v2_funct_1(X0_53)
% 2.64/1.01      | ~ v2_funct_1(k5_relat_1(X0_53,X1_53))
% 2.64/1.01      | ~ v1_funct_1(X0_53)
% 2.64/1.01      | ~ v1_funct_1(X1_53)
% 2.64/1.01      | ~ v1_relat_1(X0_53)
% 2.64/1.01      | ~ v1_relat_1(X1_53)
% 2.64/1.01      | k1_relat_1(X1_53) != k2_relat_1(X0_53) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1184,plain,
% 2.64/1.01      ( k1_relat_1(X0_53) != k2_relat_1(X1_53)
% 2.64/1.01      | v2_funct_1(X1_53) = iProver_top
% 2.64/1.01      | v2_funct_1(k5_relat_1(X1_53,X0_53)) != iProver_top
% 2.64/1.01      | v1_funct_1(X1_53) != iProver_top
% 2.64/1.01      | v1_funct_1(X0_53) != iProver_top
% 2.64/1.01      | v1_relat_1(X1_53) != iProver_top
% 2.64/1.01      | v1_relat_1(X0_53) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_698]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2667,plain,
% 2.64/1.01      ( k1_relat_1(X0_53) != k1_relat_1(sK2)
% 2.64/1.01      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_53)) != iProver_top
% 2.64/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.64/1.01      | v1_funct_1(X0_53) != iProver_top
% 2.64/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.64/1.01      | v1_relat_1(X0_53) != iProver_top
% 2.64/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_2119,c_1184]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_3,plain,
% 2.64/1.01      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 2.64/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_700,plain,
% 2.64/1.01      ( ~ v1_funct_1(X0_53)
% 2.64/1.01      | ~ v1_relat_1(X0_53)
% 2.64/1.01      | v1_relat_1(k2_funct_1(X0_53)) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_751,plain,
% 2.64/1.01      ( v1_funct_1(X0_53) != iProver_top
% 2.64/1.01      | v1_relat_1(X0_53) != iProver_top
% 2.64/1.01      | v1_relat_1(k2_funct_1(X0_53)) = iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_700]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_753,plain,
% 2.64/1.01      ( v1_funct_1(sK2) != iProver_top
% 2.64/1.01      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 2.64/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_751]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_3151,plain,
% 2.64/1.01      ( v1_relat_1(X0_53) != iProver_top
% 2.64/1.01      | k1_relat_1(X0_53) != k1_relat_1(sK2)
% 2.64/1.01      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_53)) != iProver_top
% 2.64/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.64/1.01      | v1_funct_1(X0_53) != iProver_top ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_2667,c_37,c_39,c_750,c_753,c_1577,c_1635]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_3152,plain,
% 2.64/1.01      ( k1_relat_1(X0_53) != k1_relat_1(sK2)
% 2.64/1.01      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_53)) != iProver_top
% 2.64/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.64/1.01      | v1_funct_1(X0_53) != iProver_top
% 2.64/1.01      | v1_relat_1(X0_53) != iProver_top ),
% 2.64/1.01      inference(renaming,[status(thm)],[c_3151]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_3163,plain,
% 2.64/1.01      ( v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
% 2.64/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.64/1.01      | v1_funct_1(sK2) != iProver_top
% 2.64/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.64/1.01      inference(equality_resolution,[status(thm)],[c_3152]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_9,plain,
% 2.64/1.01      ( ~ v2_funct_1(X0)
% 2.64/1.01      | ~ v1_funct_1(X0)
% 2.64/1.01      | ~ v1_relat_1(X0)
% 2.64/1.01      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
% 2.64/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_694,plain,
% 2.64/1.01      ( ~ v2_funct_1(X0_53)
% 2.64/1.01      | ~ v1_funct_1(X0_53)
% 2.64/1.01      | ~ v1_relat_1(X0_53)
% 2.64/1.01      | k5_relat_1(k2_funct_1(X0_53),X0_53) = k6_relat_1(k2_relat_1(X0_53)) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_9]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1188,plain,
% 2.64/1.01      ( k5_relat_1(k2_funct_1(X0_53),X0_53) = k6_relat_1(k2_relat_1(X0_53))
% 2.64/1.01      | v2_funct_1(X0_53) != iProver_top
% 2.64/1.01      | v1_funct_1(X0_53) != iProver_top
% 2.64/1.01      | v1_relat_1(X0_53) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_694]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2705,plain,
% 2.64/1.01      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
% 2.64/1.01      | v1_funct_1(sK2) != iProver_top
% 2.64/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_1196,c_1188]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_766,plain,
% 2.64/1.01      ( ~ v2_funct_1(sK2)
% 2.64/1.01      | ~ v1_funct_1(sK2)
% 2.64/1.01      | ~ v1_relat_1(sK2)
% 2.64/1.01      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_694]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2956,plain,
% 2.64/1.01      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_2705,c_30,c_28,c_26,c_766,c_1576,c_1634]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_3168,plain,
% 2.64/1.01      ( v2_funct_1(k6_relat_1(k2_relat_1(sK2))) != iProver_top
% 2.64/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.64/1.01      | v1_funct_1(sK2) != iProver_top
% 2.64/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.64/1.01      inference(light_normalisation,[status(thm)],[c_3163,c_2956]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_3175,plain,
% 2.64/1.01      ( v2_funct_1(k6_relat_1(k2_relat_1(sK2))) != iProver_top
% 2.64/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_3168,c_37,c_39,c_1577,c_1635]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_6,plain,
% 2.64/1.01      ( v2_funct_1(k6_relat_1(X0)) ),
% 2.64/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_697,plain,
% 2.64/1.01      ( v2_funct_1(k6_relat_1(X0_54)) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1185,plain,
% 2.64/1.01      ( v2_funct_1(k6_relat_1(X0_54)) = iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_697]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_3181,plain,
% 2.64/1.01      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.64/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_3175,c_1185]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_19,plain,
% 2.64/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.64/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.64/1.01      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.64/1.01      | ~ v2_funct_1(X0)
% 2.64/1.01      | ~ v1_funct_1(X0)
% 2.64/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.64/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_690,plain,
% 2.64/1.01      ( ~ v1_funct_2(X0_53,X0_54,X1_54)
% 2.64/1.01      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.64/1.01      | m1_subset_1(k2_funct_1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_54,X0_54)))
% 2.64/1.01      | ~ v2_funct_1(X0_53)
% 2.64/1.01      | ~ v1_funct_1(X0_53)
% 2.64/1.01      | k2_relset_1(X0_54,X1_54,X0_53) != X1_54 ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_19]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1192,plain,
% 2.64/1.01      ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
% 2.64/1.01      | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
% 2.64/1.01      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 2.64/1.01      | m1_subset_1(k2_funct_1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_54,X0_54))) = iProver_top
% 2.64/1.01      | v2_funct_1(X0_53) != iProver_top
% 2.64/1.01      | v1_funct_1(X0_53) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_690]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_3698,plain,
% 2.64/1.01      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.64/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 2.64/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.64/1.01      | v2_funct_1(sK2) != iProver_top
% 2.64/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_2469,c_1192]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_20,plain,
% 2.64/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.64/1.01      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.64/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.64/1.01      | ~ v2_funct_1(X0)
% 2.64/1.01      | ~ v1_funct_1(X0)
% 2.64/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.64/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_689,plain,
% 2.64/1.01      ( ~ v1_funct_2(X0_53,X0_54,X1_54)
% 2.64/1.01      | v1_funct_2(k2_funct_1(X0_53),X1_54,X0_54)
% 2.64/1.01      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.64/1.01      | ~ v2_funct_1(X0_53)
% 2.64/1.01      | ~ v1_funct_1(X0_53)
% 2.64/1.01      | k2_relset_1(X0_54,X1_54,X0_53) != X1_54 ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_20]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1193,plain,
% 2.64/1.01      ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
% 2.64/1.01      | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
% 2.64/1.01      | v1_funct_2(k2_funct_1(X0_53),X1_54,X0_54) = iProver_top
% 2.64/1.01      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 2.64/1.01      | v2_funct_1(X0_53) != iProver_top
% 2.64/1.01      | v1_funct_1(X0_53) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_689]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_3699,plain,
% 2.64/1.01      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 2.64/1.01      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.64/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.64/1.01      | v2_funct_1(sK2) != iProver_top
% 2.64/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_2469,c_1193]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4096,plain,
% 2.64/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_3698,c_37,c_40,c_2471,c_2472]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4102,plain,
% 2.64/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_4096,c_1191]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4109,plain,
% 2.64/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.64/1.01      inference(light_normalisation,[status(thm)],[c_4102,c_2119]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4336,plain,
% 2.64/1.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.64/1.01      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.64/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.64/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.64/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_4109,c_1195]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_11,plain,
% 2.64/1.01      ( ~ v2_funct_1(X0)
% 2.64/1.01      | ~ v1_funct_1(X0)
% 2.64/1.01      | ~ v1_relat_1(X0)
% 2.64/1.01      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.64/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_692,plain,
% 2.64/1.01      ( ~ v2_funct_1(X0_53)
% 2.64/1.01      | ~ v1_funct_1(X0_53)
% 2.64/1.01      | ~ v1_relat_1(X0_53)
% 2.64/1.01      | k2_funct_1(k2_funct_1(X0_53)) = X0_53 ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_11]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1190,plain,
% 2.64/1.01      ( k2_funct_1(k2_funct_1(X0_53)) = X0_53
% 2.64/1.01      | v2_funct_1(X0_53) != iProver_top
% 2.64/1.01      | v1_funct_1(X0_53) != iProver_top
% 2.64/1.01      | v1_relat_1(X0_53) != iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_692]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1893,plain,
% 2.64/1.01      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.64/1.01      | v1_funct_1(sK2) != iProver_top
% 2.64/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.64/1.01      inference(superposition,[status(thm)],[c_1196,c_1190]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_772,plain,
% 2.64/1.01      ( ~ v2_funct_1(sK2)
% 2.64/1.01      | ~ v1_funct_1(sK2)
% 2.64/1.01      | ~ v1_relat_1(sK2)
% 2.64/1.01      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.64/1.01      inference(instantiation,[status(thm)],[c_692]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_2113,plain,
% 2.64/1.01      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_1893,c_30,c_28,c_26,c_772,c_1576,c_1634]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4356,plain,
% 2.64/1.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 2.64/1.01      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.64/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.64/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.64/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.64/1.01      inference(light_normalisation,[status(thm)],[c_4336,c_2113]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4463,plain,
% 2.64/1.01      ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.64/1.01      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.64/1.01      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_4007,c_37,c_39,c_40,c_750,c_1577,c_1635,c_2471,c_2472,
% 2.64/1.01                 c_3181,c_3698,c_3699,c_4356]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4364,plain,
% 2.64/1.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 2.64/1.01      inference(global_propositional_subsumption,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_4356,c_37,c_39,c_40,c_750,c_1577,c_1635,c_2471,c_2472,
% 2.64/1.01                 c_3181,c_3698,c_3699]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4467,plain,
% 2.64/1.01      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.64/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.64/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.64/1.01      inference(light_normalisation,[status(thm)],[c_4463,c_4364]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_682,negated_conjecture,
% 2.64/1.01      ( v1_funct_1(sK2) ),
% 2.64/1.01      inference(subtyping,[status(esa)],[c_30]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_1199,plain,
% 2.64/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 2.64/1.01      inference(predicate_to_equality,[status(thm)],[c_682]) ).
% 2.64/1.01  
% 2.64/1.01  cnf(c_4471,plain,
% 2.64/1.01      ( $false ),
% 2.64/1.01      inference(forward_subsumption_resolution,
% 2.64/1.01                [status(thm)],
% 2.64/1.01                [c_4467,c_1199,c_2471,c_2472]) ).
% 2.64/1.01  
% 2.64/1.01  
% 2.64/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.64/1.01  
% 2.64/1.01  ------                               Statistics
% 2.64/1.01  
% 2.64/1.01  ------ General
% 2.64/1.01  
% 2.64/1.01  abstr_ref_over_cycles:                  0
% 2.64/1.01  abstr_ref_under_cycles:                 0
% 2.64/1.01  gc_basic_clause_elim:                   0
% 2.64/1.01  forced_gc_time:                         0
% 2.64/1.01  parsing_time:                           0.01
% 2.64/1.01  unif_index_cands_time:                  0.
% 2.64/1.01  unif_index_add_time:                    0.
% 2.64/1.01  orderings_time:                         0.
% 2.64/1.01  out_proof_time:                         0.017
% 2.64/1.01  total_time:                             0.234
% 2.64/1.01  num_of_symbols:                         61
% 2.64/1.01  num_of_terms:                           4177
% 2.64/1.01  
% 2.64/1.01  ------ Preprocessing
% 2.64/1.01  
% 2.64/1.01  num_of_splits:                          1
% 2.64/1.01  num_of_split_atoms:                     1
% 2.64/1.01  num_of_reused_defs:                     0
% 2.64/1.01  num_eq_ax_congr_red:                    4
% 2.64/1.01  num_of_sem_filtered_clauses:            2
% 2.64/1.01  num_of_subtypes:                        4
% 2.64/1.01  monotx_restored_types:                  1
% 2.64/1.01  sat_num_of_epr_types:                   0
% 2.64/1.01  sat_num_of_non_cyclic_types:            0
% 2.64/1.01  sat_guarded_non_collapsed_types:        1
% 2.64/1.01  num_pure_diseq_elim:                    0
% 2.64/1.01  simp_replaced_by:                       0
% 2.64/1.01  res_preprocessed:                       151
% 2.64/1.01  prep_upred:                             0
% 2.64/1.01  prep_unflattend:                        11
% 2.64/1.01  smt_new_axioms:                         0
% 2.64/1.01  pred_elim_cands:                        5
% 2.64/1.01  pred_elim:                              6
% 2.64/1.01  pred_elim_cl:                           7
% 2.64/1.01  pred_elim_cycles:                       9
% 2.64/1.01  merged_defs:                            0
% 2.64/1.01  merged_defs_ncl:                        0
% 2.64/1.01  bin_hyper_res:                          0
% 2.64/1.01  prep_cycles:                            4
% 2.64/1.01  pred_elim_time:                         0.005
% 2.64/1.01  splitting_time:                         0.
% 2.64/1.01  sem_filter_time:                        0.
% 2.64/1.01  monotx_time:                            0.001
% 2.64/1.01  subtype_inf_time:                       0.001
% 2.64/1.01  
% 2.64/1.01  ------ Problem properties
% 2.64/1.01  
% 2.64/1.01  clauses:                                27
% 2.64/1.01  conjectures:                            5
% 2.64/1.01  epr:                                    2
% 2.64/1.01  horn:                                   27
% 2.64/1.01  ground:                                 8
% 2.64/1.01  unary:                                  9
% 2.64/1.01  binary:                                 1
% 2.64/1.01  lits:                                   92
% 2.64/1.01  lits_eq:                                18
% 2.64/1.01  fd_pure:                                0
% 2.64/1.01  fd_pseudo:                              0
% 2.64/1.01  fd_cond:                                0
% 2.64/1.01  fd_pseudo_cond:                         1
% 2.64/1.01  ac_symbols:                             0
% 2.64/1.01  
% 2.64/1.01  ------ Propositional Solver
% 2.64/1.01  
% 2.64/1.01  prop_solver_calls:                      29
% 2.64/1.01  prop_fast_solver_calls:                 1253
% 2.64/1.01  smt_solver_calls:                       0
% 2.64/1.01  smt_fast_solver_calls:                  0
% 2.64/1.01  prop_num_of_clauses:                    1629
% 2.64/1.01  prop_preprocess_simplified:             5852
% 2.64/1.01  prop_fo_subsumed:                       59
% 2.64/1.01  prop_solver_time:                       0.
% 2.64/1.01  smt_solver_time:                        0.
% 2.64/1.01  smt_fast_solver_time:                   0.
% 2.64/1.01  prop_fast_solver_time:                  0.
% 2.64/1.01  prop_unsat_core_time:                   0.
% 2.64/1.01  
% 2.64/1.01  ------ QBF
% 2.64/1.01  
% 2.64/1.01  qbf_q_res:                              0
% 2.64/1.01  qbf_num_tautologies:                    0
% 2.64/1.01  qbf_prep_cycles:                        0
% 2.64/1.01  
% 2.64/1.01  ------ BMC1
% 2.64/1.01  
% 2.64/1.01  bmc1_current_bound:                     -1
% 2.64/1.01  bmc1_last_solved_bound:                 -1
% 2.64/1.01  bmc1_unsat_core_size:                   -1
% 2.64/1.01  bmc1_unsat_core_parents_size:           -1
% 2.64/1.01  bmc1_merge_next_fun:                    0
% 2.64/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.64/1.01  
% 2.64/1.01  ------ Instantiation
% 2.64/1.01  
% 2.64/1.01  inst_num_of_clauses:                    596
% 2.64/1.01  inst_num_in_passive:                    69
% 2.64/1.01  inst_num_in_active:                     305
% 2.64/1.01  inst_num_in_unprocessed:                222
% 2.64/1.01  inst_num_of_loops:                      330
% 2.64/1.01  inst_num_of_learning_restarts:          0
% 2.64/1.01  inst_num_moves_active_passive:          21
% 2.64/1.01  inst_lit_activity:                      0
% 2.64/1.01  inst_lit_activity_moves:                0
% 2.64/1.01  inst_num_tautologies:                   0
% 2.64/1.01  inst_num_prop_implied:                  0
% 2.64/1.01  inst_num_existing_simplified:           0
% 2.64/1.01  inst_num_eq_res_simplified:             0
% 2.64/1.01  inst_num_child_elim:                    0
% 2.64/1.01  inst_num_of_dismatching_blockings:      133
% 2.64/1.01  inst_num_of_non_proper_insts:           573
% 2.64/1.01  inst_num_of_duplicates:                 0
% 2.64/1.01  inst_inst_num_from_inst_to_res:         0
% 2.64/1.01  inst_dismatching_checking_time:         0.
% 2.64/1.01  
% 2.64/1.01  ------ Resolution
% 2.64/1.01  
% 2.64/1.01  res_num_of_clauses:                     0
% 2.64/1.01  res_num_in_passive:                     0
% 2.64/1.01  res_num_in_active:                      0
% 2.64/1.01  res_num_of_loops:                       155
% 2.64/1.01  res_forward_subset_subsumed:            58
% 2.64/1.01  res_backward_subset_subsumed:           0
% 2.64/1.01  res_forward_subsumed:                   0
% 2.64/1.01  res_backward_subsumed:                  0
% 2.64/1.01  res_forward_subsumption_resolution:     1
% 2.64/1.01  res_backward_subsumption_resolution:    0
% 2.64/1.01  res_clause_to_clause_subsumption:       85
% 2.64/1.01  res_orphan_elimination:                 0
% 2.64/1.01  res_tautology_del:                      58
% 2.64/1.01  res_num_eq_res_simplified:              0
% 2.64/1.01  res_num_sel_changes:                    0
% 2.64/1.01  res_moves_from_active_to_pass:          0
% 2.64/1.01  
% 2.64/1.01  ------ Superposition
% 2.64/1.01  
% 2.64/1.01  sup_time_total:                         0.
% 2.64/1.01  sup_time_generating:                    0.
% 2.64/1.01  sup_time_sim_full:                      0.
% 2.64/1.01  sup_time_sim_immed:                     0.
% 2.64/1.01  
% 2.64/1.01  sup_num_of_clauses:                     52
% 2.64/1.01  sup_num_in_active:                      52
% 2.64/1.01  sup_num_in_passive:                     0
% 2.64/1.01  sup_num_of_loops:                       64
% 2.64/1.01  sup_fw_superposition:                   19
% 2.64/1.01  sup_bw_superposition:                   24
% 2.64/1.01  sup_immediate_simplified:               17
% 2.64/1.01  sup_given_eliminated:                   0
% 2.64/1.01  comparisons_done:                       0
% 2.64/1.01  comparisons_avoided:                    0
% 2.64/1.01  
% 2.64/1.01  ------ Simplifications
% 2.64/1.01  
% 2.64/1.01  
% 2.64/1.01  sim_fw_subset_subsumed:                 6
% 2.64/1.01  sim_bw_subset_subsumed:                 0
% 2.64/1.01  sim_fw_subsumed:                        3
% 2.64/1.01  sim_bw_subsumed:                        0
% 2.64/1.01  sim_fw_subsumption_res:                 5
% 2.64/1.01  sim_bw_subsumption_res:                 0
% 2.64/1.01  sim_tautology_del:                      0
% 2.64/1.01  sim_eq_tautology_del:                   7
% 2.64/1.01  sim_eq_res_simp:                        0
% 2.64/1.01  sim_fw_demodulated:                     0
% 2.64/1.01  sim_bw_demodulated:                     12
% 2.64/1.01  sim_light_normalised:                   19
% 2.64/1.01  sim_joinable_taut:                      0
% 2.64/1.01  sim_joinable_simp:                      0
% 2.64/1.01  sim_ac_normalised:                      0
% 2.64/1.01  sim_smt_subsumption:                    0
% 2.64/1.01  
%------------------------------------------------------------------------------
